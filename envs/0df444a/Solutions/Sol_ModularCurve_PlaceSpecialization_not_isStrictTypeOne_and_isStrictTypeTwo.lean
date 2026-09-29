-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.not_isStrictTypeOne_and_isStrictTypeTwo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a169197e-b8f1-5856-a775-2c7ed0877517

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    ¬ (P.IsStrictTypeOne W ∧ P.IsStrictTypeTwo W) := by
  rintro ⟨⟨h1, -⟩, ⟨h2, h2'⟩⟩

  apply h2'
  have h2e : P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) := h2
  rw [← h2e]
  exact h1

end S_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo (solution)
