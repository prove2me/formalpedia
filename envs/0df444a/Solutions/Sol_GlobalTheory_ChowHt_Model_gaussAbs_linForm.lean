-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.gaussAbs_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:42.862799+00:00
-- url     : https://prove2.me/submissions/cf1091df-f1a9-45a6-ac0c-26d04ca2e872

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Theorems.Thm_GlobalTheory_ChowHt_Model_coeff_linForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
namespace GlobalTheory.ChowHt.Model
theorem _root_.solution {F : Type} [Field F] [NumberField F] {N : ℕ} (v : FinitePlace F)
    (c : Fin N → F) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linForm c) = ⨆ k, v (c k) := by
  classical
  have hb : BddAbove (Set.range fun k => v (c k)) := (Set.finite_range _).bddAbove
  have hn : 0 ≤ ⨆ k, v (c k) := Real.iSup_nonneg fun k => apply_nonneg _ _
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  apply le_antisymm
  · rw [← Real.coe_toNNReal _ hn, NNReal.coe_le_coe]
    refine Finset.sup_le fun s hs => Real.toNNReal_le_toNNReal ?_
    by_cases h : ∃ k, s = Finsupp.single (0, k) 1
    · obtain ⟨k, rfl⟩ := h
      rw [coeff_linForm]; exact le_ciSup hb k
    · exfalso
      rw [mem_support_iff] at hs
      apply hs
      simp only [linForm, coeff_sum, coeff_C_mul, coeff_X']
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg, mul_zero]
      intro h'; exact h ⟨j, h'.symm⟩
  · refine Real.iSup_le (fun k => ?_) (NNReal.coe_nonneg _)
    by_cases h : c k = 0
    · simp [h]
    · have hm : Finsupp.single ((0 : Fin 1), k) 1 ∈ (linForm c).support := by
        rw [mem_support_iff, coeff_linForm]; exact h
      have := Finset.le_sup (f := fun s => (v ((linForm c).coeff s)).toNNReal) hm
      simp only [coeff_linForm] at this
      have h2 := NNReal.coe_le_coe.2 this
      rwa [Real.coe_toNNReal _ (apply_nonneg _ _)] at h2
end GlobalTheory.ChowHt.Model
