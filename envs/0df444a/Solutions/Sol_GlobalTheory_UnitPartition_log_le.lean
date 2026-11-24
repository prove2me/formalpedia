-- Prove2me | solution 1 for GlobalTheory.UnitPartition.log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:16.31132+00:00
-- url     : https://prove2.me/submissions/0061d4f5-7dbf-4ba3-ae79-775e559ecb60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
private lemma le_of_mul_le_of_one_le' {m t B : ℝ} (hm : 1 ≤ m) (hB : 0 ≤ B) (h : m * t ≤ B) :
    t ≤ B := by
  rcases le_or_gt t 0 with ht | ht
  · exact ht.trans hB
  · nlinarith
end UnitPartition
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open GlobalTheory.UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.UnitPartition
theorem _root_.solution (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) (w : InfinitePlace K) :
    Real.log (normAtPlace w x) ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ +
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ := by
  classical
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hd0 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  have hL : Real.log (mixedEmbedding.norm x) =
      ∑ v, (mult v : ℝ) * Real.log (normAtPlace v x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun v _ => pow_ne_zero _ (hN v))]
    simp only [Real.log_pow]
  have hm : ∑ v : InfinitePlace K, (mult v : ℝ) = Module.finrank ℚ K := by
    rw [← sum_mult_eq, Nat.cast_sum]
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hpos : 0 ≤ ‖logMap x‖ := norm_nonneg _
  have hB : 0 ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ := by positivity
  have hle : ‖logMap x‖ ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ :=
    le_mul_of_one_le_left hpos hcard
  rw [← sub_le_iff_le_add]
  by_cases hw : w = w₀
  · subst hw
    set L := Real.log (mixedEmbedding.norm x)
    set d : ℝ := (Module.finrank ℚ K : ℝ)
    have h1 := Fintype.sum_eq_add_sum_subtype_ne
      (fun v => (mult v : ℝ) * Real.log (normAtPlace v x)) w₀
    have h2 := Fintype.sum_eq_add_sum_subtype_ne (fun v : InfinitePlace K => (mult v : ℝ)) w₀
    rw [← hL] at h1
    rw [hm] at h2
    have hS : ∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v =
        ∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ) * Real.log (normAtPlace v.1 x) -
          (∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ)) * (L * d⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [logMap_apply]
      ring
    have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0.ne'
    have hkey : (mult (w₀ : InfinitePlace K) : ℝ) * (Real.log (normAtPlace w₀ x) - L * d⁻¹) =
        -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v := by
      rw [hS]
      linear_combination (-1 : ℝ) * h1 + (L * d⁻¹) * h2 - L * hdd
    have hSle : -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v ≤
        Fintype.card (InfinitePlace K) * ‖logMap x‖ := by
      refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      refine (Finset.sum_le_sum fun v _ => (show |logMap x v| ≤ ‖logMap x‖ from
        (Real.norm_eq_abs (logMap x v)).symm.trans_le (norm_le_pi_norm (logMap x) v))).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) hpos
    exact le_of_mul_le_of_one_le' one_le_mult hB (hkey.trans_le hSle)
  · have hv : logMap x ⟨w, hw⟩ = (mult w : ℝ) * (Real.log (normAtPlace w x) -
        Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) := logMap_apply x ⟨w, hw⟩
    refine le_of_mul_le_of_one_le' (one_le_mult (w := w)) hB ?_
    rw [← hv]
    exact (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le
      (norm_le_pi_norm (logMap x) ⟨w, hw⟩)).trans hle)
end GlobalTheory.UnitPartition
