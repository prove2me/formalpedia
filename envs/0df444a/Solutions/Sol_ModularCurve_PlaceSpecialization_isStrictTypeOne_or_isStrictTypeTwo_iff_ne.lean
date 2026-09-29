-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/69ffb5df-3a9e-53b7-8514-cca0e8316b69

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne

open AlgebraicCurve ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W) ↔
      frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
        ≠ P.redFst W := by
  have hinj : Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) :=
    frobOnPlacesGeomLevel_injective k 1 data hKr
  have hd : P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) ∨
      frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W :=
    P.d1 W
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, h2⟩)
    · exact h2
    · intro h
      apply h2
      apply hinj
      rw [← h1]
      exact h
  · intro hW
    rcases hd with h | h
    · right
      refine ⟨h, fun h2 => hW ?_⟩
      rw [h, h2]
    · left
      exact ⟨h, hW⟩

end S_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne (solution)
