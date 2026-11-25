-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.norm_index_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:16:21.371857+00:00
-- url     : https://prove2.me/submissions/b42879d6-4a14-44f2-b031-6b2635c644d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
import Theorems.Thm_GlobalTheory_NormDetIndex_norm_det_eq_norm_index


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution (l : ℕ) [Fact l.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖(((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℕ) : ℚ_[l])‖ := by
  first
  | exact @_root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index
  | exact _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index
  | (apply _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index ..)
end GlobalTheory.TorsionMatrix
