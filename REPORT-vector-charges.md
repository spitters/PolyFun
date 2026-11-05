# Vector charges over certified handlers — validation report

Outcome: **done**. Branch `work/vector-charges-v` = upstream PR #396 head `c267bcd` + one commit
`feat(pfunctor): vector charges, prices and demand maps over certified handlers`.

## validate.sh

`./scripts/validate.sh --lint --test --axioms` on the squashed commit: exit 0,
"All requested validation checks passed."

- project build: 2654 jobs OK; module scopes, umbrella imports, docs integrity OK
- environment linters: passed for every root (production and examples)
- `lake test`: 2899 jobs OK; documentation consumer, Parliament consumer and CLI/filesystem tests OK
- axiom sweep: 18154 declarations across 487 modules, 0 non-standard-axiom-tainted
- no warnings from the new files (the only `sorry` warnings are the sweep's own taint fixtures)

## Declarations

`PolyFun/PFunctor/Handler/CertifiedVec.lean`:
`PFunctor.priceHom`, `priceHom_apply`, `demandHom`, `demandHom_apply`, `demandHom_demandHom`;
`PFunctor.FreeM.costWith_pi_apply`, `cost_pi_apply`, `cost_le_pi_iff`, `IsChargeBound.price`,
`cost_price_le`, `cost_price_le_of_le`;
`PFunctor.Handler.Certified.ofDemand`, `isChargeBound_liftM_demand`,
`isChargeBound_liftM_demand_comp`.

`PolyFunTest/PFunctor/Charge/Vector.lean`: a two-resource program (use vector `(2, 1)`),
componentwise worst-case costs, pricing (bound `7`), demands by steps (`7` steps) and the
composite demand through steps and gates (`28` gates).

Also: `PolyFun.lean` import, `docs/guides/cost.md` paragraph, `docs/reference/repo-map.md` link.

## What the new #396 head required

The rebase onto `c267bcd` applied cleanly and both modules built unchanged: the new head weakens
the typeclasses of `Certified` (`AddMonoid`/`Preorder`, `AddLeftMono`/`AddRightMono` instead of
`IsOrderedAddMonoid`), which the `CommSemiring`/`IsOrderedRing` instances here still supply, and
`map_zero` on `demandHom` still rewrites the transferred start. To follow the new universe
generality, the handler section now takes `Q : PFunctor.{uA₂, uB₂}` and
`R : PFunctor.{uA₃, uB₃}` (`Certified.ofDemand`, `isChargeBound_liftM_demand`), while
`isChargeBound_liftM_demand_comp` pins `Q : PFunctor.{uA₂, uB}` as `Certified.comp` does.
The earlier draft commits (no empty report commit was present; `b5b6e7b` is not on the branch,
the base was the old #396 head `106b687`) were squashed into one commit.

Lessons: `validate.sh` builds the separate consumers, whose dependency resolution runs Mathlib's
post-update `cache get`; in a sandbox without the Mathlib cache set `MATHLIB_NO_CACHE_ON_UPDATE=1`,
otherwise it spends an hour retrying 9000 downloads before the consumers build from the shared
unpacked packages.
