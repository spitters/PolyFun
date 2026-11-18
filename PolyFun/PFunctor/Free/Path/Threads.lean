/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.PFunctor.Handler.Stateful

/-!
# Threading state along completed paths

A stateful handler `h : Handler.Stateful (FreeM Q) S P` implements each call of `P` by a program
over `Q` that reads a state and returns an answer with the next state. Running a program `x` over
`P` through `h` from a state `s` is the program `(x.liftM h).run s` over `Q`
(`Handler.Stateful.run`).

`Path.Threads h x p s t s'` states that the calls along the completed path `p` through `x` are
answered, in the order of the path, by completed paths through their implementations, each
returning the answer `p` takes, the state passing from `s` to `s'` through the steps, and the
event traces of these implementation paths concatenating to `t`.

`Path.exists_run_liftM_iff` is the exact law of a stateful simulation: the completed paths through
`(x.liftM h).run s`, read as output, final state and event trace, are exactly the completed paths
through `x` threaded by `h` from `s`. It is the stateful form of `Path.exists_path_liftM_iff`.

The event trace of a path through a bind is the product of the traces of its two parts
(`Path.trace_joinBind`, `Path.trace_splitBind`).
-/

@[expose] public section

universe uA uB uA₂ uB₂ v w

namespace PFunctor.FreeM

namespace Path

variable {Q : PFunctor.{uA₂, uB₂}}

/-- The event trace of a joined path through a bind is the trace of the path through the first
program followed by the trace of the path through the continuation. -/
theorem trace_joinBind {γ : Type v} {δ : Type w} (x : FreeM Q γ) (f : γ → FreeM Q δ)
    (p : Path x) (q : Path (f (output x p))) :
    trace (FreeM.bind x f) (joinBind x f p q) = trace x p * trace _ q := by
  induction x using FreeM.rec with
  | pure a => exact (one_mul _).symm
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    change FreeMonoid.of (α := Q.Idx) ⟨a, b⟩ * trace _ (joinBind (r b) f p q) =
      (FreeMonoid.of (α := Q.Idx) ⟨a, b⟩ * trace (r b) p) * _
    rw [ih b p q, mul_assoc]
    rfl

/-- The event trace of a path through a bind is the product of the traces of the two paths
`splitBind` returns. -/
theorem trace_splitBind {γ : Type v} {δ : Type w} (x : FreeM Q γ) (f : γ → FreeM Q δ)
    (q : Path (FreeM.bind x f)) :
    trace (FreeM.bind x f) q = trace x (splitBind x f q).1 * trace _ (splitBind x f q).2 := by
  conv_lhs => rw [← joinBind_splitBind x f q]
  exact trace_joinBind x f _ _

variable {P : PFunctor.{uA, uB}} {S α : Type uB}

/-- `Threads h x p s t s'`: the calls along the completed path `p` through `x` are answered in
order by completed paths through their implementations under `h`, each returning the answer `p`
takes; the state passes from `s` to `s'`, and the event traces of the implementation paths
concatenate to `t`. -/
def Threads (h : Handler.Stateful (FreeM Q) S P) :
    (x : FreeM P α) → Path x → S → TraceList Q → S → Prop
  | .pure _, _, s, t, s' => t = 1 ∧ s' = s
  | .liftBind a r, ⟨b, p⟩, s, t, s' => ∃ q : Path ((h a).run s), (output _ q).1 = b ∧
      ∃ t', Threads h (r b) p (output _ q).2 t' s' ∧ t = trace _ q * t'

/-- **The exact law of a stateful simulation.** The completed paths through the run of `x` under
the stateful handler `h` from the state `s`, read as an output, a final state and an event trace,
are exactly the completed paths through `x` whose calls `h` answers with the answers taken, the
state threaded in the order of the path. -/
theorem exists_run_liftM_iff (h : Handler.Stateful (FreeM Q) S P) (x : FreeM P α) (s : S)
    (v : α) (s' : S) (t : TraceList Q) :
    (∃ q : Path ((x.liftM h).run s), output _ q = (v, s') ∧ trace _ q = t) ↔
      ∃ p : Path x, output x p = v ∧ Threads h x p s t s' := by
  induction x using FreeM.rec generalizing s t with
  | pure a =>
    constructor
    · rintro ⟨_, hv, rfl⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
      exact ⟨⟨⟩, rfl, rfl, rfl⟩
    · rintro ⟨_, rfl, rfl, rfl⟩
      exact ⟨⟨⟩, rfl, rfl⟩
  | liftBind a r ih =>
    let k : P.B a × S → FreeM Q (α × S) := fun y => ((r y.1).liftM h).run y.2
    change (∃ q : Path (FreeM.bind ((h a).run s) k), _) ↔ _
    constructor
    · rintro ⟨q, hv, rfl⟩
      let sp := splitBind ((h a).run s) k q
      obtain ⟨p, hp, ht⟩ := (ih (output _ sp.1).1 (output _ sp.1).2 _).1
        ⟨sp.2, (output_splitBind _ k q).symm.trans hv, rfl⟩
      exact ⟨⟨(output _ sp.1).1, p⟩, hp, sp.1, rfl, _, ht, trace_splitBind _ k q⟩
    · rintro ⟨⟨b, p⟩, hv, q₁, rfl, t', ht, rfl⟩
      obtain ⟨q₂, hq₂, rfl⟩ := (ih (output _ q₁).1 (output _ q₁).2 t').2 ⟨p, hv, ht⟩
      exact ⟨joinBind _ k q₁ q₂, (output_joinBind _ k q₁ q₂).trans hq₂,
        trace_joinBind _ k q₁ q₂⟩

end Path

end PFunctor.FreeM
