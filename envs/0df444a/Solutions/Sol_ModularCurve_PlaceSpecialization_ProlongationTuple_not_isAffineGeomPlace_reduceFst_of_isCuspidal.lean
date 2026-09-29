-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/590d2e2f-9422-5fec-aa21-abe505ce5c64

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : ProlongationTuple.IsCuspidal P V) :
    ¬ IsAffineGeomPlace k N (P.reduceFst V) := by
  set jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ with hjN
  have hαj : heckeAlphaBar (AlgebraicClosure ℚ) N q jN = ProlongationTuple.jFun N q :=
    Subtype.ext (coe_heckeAlphaBar N q jN)
  have he : 0 < Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) V := by
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    exact V.ramificationIndex_pos (F := modularFunctionFieldBar N)

  have hcusp : ∀ a : A, (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have hle := hV a
    have key := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [map_sub, hαj, AlgHom.commutes] at key
    rw [key] at hle
    by_contra hpos
    push_neg at hpos
    exact absurd hle (not_le.mpr (mul_pos (by exact_mod_cast he) hpos))
  have hpole := P.d0_j_pole (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hcusp
  intro haff
  have h0 := (P.reduceFst V).ord_nonneg_of_mem haff.1
  exact absurd hpole (not_lt.mpr h0)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal (solution)
