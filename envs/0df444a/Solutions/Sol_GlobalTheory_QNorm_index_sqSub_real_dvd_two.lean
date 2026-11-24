-- Prove2me | solution 1 for GlobalTheory.QNorm.index_sqSub_real_dvd_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:54.636229+00:00
-- url     : https://prove2.me/submissions/3e95e9b8-040e-477e-a04b-e3ccde9fde8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Theorems.Thm_GlobalTheory_QNorm_mem_sqSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
private theorem isSquare_real_iff_nonneg (r : ℝ) : IsSquare r ↔ 0 ≤ r :=
  ⟨fun h => h.nonneg, fun h => ⟨Real.sqrt r, (Real.mul_self_sqrt h).symm⟩⟩
end GlobalTheory.QNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F : Type} [Field F] (σ : F →+* ℝ) : (sqSub σ).index ∣ 2 := by
  by_cases h : ∀ x : Fˣ, x ∈ sqSub σ
  · rw [show sqSub σ = ⊤ from eq_top_iff.mpr fun x _ => h x, Subgroup.index_top]
    exact one_dvd 2
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    have hne : ∀ x : Fˣ, σ (x : F) ≠ 0 := fun x => (x.isUnit.map σ).ne_zero
    have hmem : ∀ x : Fˣ, x ∈ sqSub σ ↔ 0 ≤ σ (x : F) := fun x =>
      (mem_sqSub σ x).trans (isSquare_real_iff_nonneg _)
    have ha' : σ (a : F) < 0 := not_le.mp fun h' => ha ((hmem a).mpr h')
    have h2 : (sqSub σ).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨a, fun b => ?_⟩
      rw [hmem, hmem, Units.val_mul, map_mul]
      rcases lt_or_gt_of_ne (hne b) with hb | hb
      · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hb.le ha'.le, not_le.mpr hb⟩
      · exact Or.inr ⟨hb.le, not_le.mpr (mul_neg_of_pos_of_neg hb ha')⟩
    rw [h2]
end GlobalTheory.QNorm
