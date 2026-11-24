-- Prove2me | solution 1 for GlobalTheory.QNorm.Defect.evenNorms_of_le_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:25.3508+00:00
-- url     : https://prove2.me/submissions/cced2543-976b-4f63-8845-3f21bedc8e55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStepStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormalFormNonsquareAdicCompletion
import Theorems.Thm_GlobalTheory_QNorm_Defect_map_four_le
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_evenOrderNorms_one_add_four_mul_of_no_root
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
open GlobalTheory.QNorm.Defect
variable {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
namespace GlobalTheory.QNorm.Defect
theorem _root_.solution (h2 : (2 : K) ≠ 0)
    (hsq : ∀ x : K, w (x - 1) < w 4 → IsSquare x) (δ : K) (hδ : w δ = 1) (hns : ¬ IsSquare δ)
    (h : w (δ - 1) ≤ w 4) : EvenNorms w δ := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hw4 : 0 < w 4 := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 h4)
  set ρ : K := (δ - 1) / 4 with hρ
  have hδρ : δ = 1 + 4 * ρ := by rw [hρ]; field_simp; ring
  have hρ1 : w ρ ≤ 1 := by rw [hρ, map_div₀]; exact div_le_one_of_le₀ h zero_le'
  rw [hδρ]
  refine GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root K w ρ h2 hρ1 fun x hx => ?_
  have hle : w (x ^ 2 + x - ρ) ≤ 1 := by
    refine w.map_sub_le (w.map_add_le ?_ hx) hρ1
    rw [map_pow]; exact pow_le_one₀ zero_le' hx
  refine le_antisymm hle (not_lt.1 fun hlt => hns ?_)
  have e1 : δ - (1 + 2 * x) ^ 2 = -(4 * (x ^ 2 + x - ρ)) := by rw [hδρ]; ring
  have l1 : w (δ - (1 + 2 * x) ^ 2) < w 4 := by
    rw [e1, Valuation.map_neg, map_mul]
    exact mul_lt_of_lt_one_right hw4 hlt
  have l2 : w ((1 + 2 * x) ^ 2) = 1 := by
    rw [← hδ]
    refine w.map_eq_of_sub_lt ?_
    rw [Valuation.map_sub_swap, hδ]
    exact l1.trans_le (map_four_le w)
  have hy : (1 + 2 * x) ^ 2 ≠ 0 := by
    intro h0; rw [h0] at l2; simp at l2
  have hs : IsSquare (δ / (1 + 2 * x) ^ 2) := by
    refine hsq _ ?_
    rw [div_sub_one hy, map_div₀, l2, div_one]; exact l1
  have : δ = δ / (1 + 2 * x) ^ 2 * (1 + 2 * x) ^ 2 := (div_mul_cancel₀ _ hy).symm
  rw [this]
  exact hs.mul (IsSquare.sq _)
end GlobalTheory.QNorm.Defect
