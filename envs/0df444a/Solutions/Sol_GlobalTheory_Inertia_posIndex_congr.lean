-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:07.436884+00:00
-- url     : https://prove2.me/submissions/b0521b2c-a10c-4598-8a7a-0c57735eb97b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_congr_le
import Theorems.Thm_GlobalTheory_Inertia_congr_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (G : Matrix n n ℂ) {P : Matrix n n ℂ} (hP : P.det ≠ 0) :
    posIndex (Pᵀ * G * P.map conj) = posIndex G := by
  have hu : IsUnit P.det := hP.isUnit
  refine le_antisymm (posIndex_congr_le G (mulVec_injective_iff_isUnit.2
    ((isUnit_iff_isUnit_det P).2 hu))) ?_
  have h := posIndex_congr_le (Pᵀ * G * P.map conj) (P := P⁻¹)
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det P hu)))
  rw [← congr_mul, mul_nonsing_inv P hu] at h
  simpa using h
end GlobalTheory.Inertia
