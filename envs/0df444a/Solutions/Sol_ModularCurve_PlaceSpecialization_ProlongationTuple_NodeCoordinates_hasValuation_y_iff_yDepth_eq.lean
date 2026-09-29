-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.hasValuation_y_iff_yDepth_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/feac8e51-18ea-51ac-a1e3-98a373d654a7

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_PlaceDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_hasValuation_y_iff_yDepth_eq
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVw : P.reduceFst V = w) (hV : V.IsRational)
    (γ : A.ValueGroup) :
    V.HasValuation A ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) γ ↔ c.yDepth V = γ := by
  rw [Place.hasValuation_iff_valuation_evalAt A V hV]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨c.y.2.1.2.2 V hVw, h⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_hasValuation_y_iff_yDepth_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_hasValuation_y_iff_yDepth_eq (solution)
