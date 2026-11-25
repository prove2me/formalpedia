-- Prove2me | solution 1 for GlobalTheory.IntClsCount.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:15.503235+00:00
-- url     : https://prove2.me/submissions/984c090c-3a1c-403d-9243-dcfc81469372

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
import Theorems.Thm_GlobalTheory_IntClsCount_det_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_OrbitDenom_det_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.IntClsCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IntClsCount
theorem _root_.solution (L : LocE F E) {N : ℕ} {A : Matrix (Fin N) (Fin N) E} (hA : IsUni A)
    (hI : IsIntM L A) : ∃ B, IsUni B ∧ IsIntM L B ∧ A * B = 1 ∧ B * A = 1 := by
  have ht : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular ht]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI := A.invertibleOfIsUnitDet hu
  have hti : A⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular ht
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hu
  refine ⟨A⁻¹, ⟨fun i j h => hti h, fun i => ?_⟩, fun i j => ?_, h1, Matrix.nonsing_inv_mul A hu⟩
  · have h2 := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2, one_mul, Matrix.one_apply_eq] at h2
    · exact h2
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hti (show id i < id l from h), mul_zero]
    · simp
  · rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, Matrix.adjugate_apply]
    refine det_mem L fun a b => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact L.O.one_mem
      · exact L.O.zero_mem
    · exact hI a b
end GlobalTheory.IntClsCount
