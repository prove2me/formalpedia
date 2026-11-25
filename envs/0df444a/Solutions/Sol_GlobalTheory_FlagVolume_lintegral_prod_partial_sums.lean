-- Prove2me | solution 1 for GlobalTheory.FlagVolume.lintegral_prod_partial_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:47.284528+00:00
-- url     : https://prove2.me/submissions/9baa7da6-d580-4e81-b000-49a2117de1d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralProdPartialSums
import Theorems.Thm_GlobalTheory_FlagVolume_lintegral_complex_inv_pow
import Theorems.Thm_GlobalTheory_FlagVolume_lintegral_fin_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat
open GlobalTheory GlobalTheory.FlagVolume
namespace GlobalTheory.FlagVolume
theorem _root_.solution (n : ℕ) : ∀ {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal
      (∏ i : Fin n, ((A + ∑ k, if k ≤ i then ‖z k‖ ^ 2 else 0) ^ 2)⁻¹) =
      ENNReal.ofReal (π ^ n / n ! * (A ^ n)⁻¹) := by
  induction n with
  | zero =>
    intro A hA
    simp [volume_pi]
  | succ n ih =>
    intro A hA
    have hm : ∀ (N : ℕ) (B : ℝ), Measurable fun z : Fin N → ℂ ↦ ENNReal.ofReal
        (∏ i : Fin N, ((B + ∑ k, if k ≤ i then ‖z k‖ ^ 2 else 0) ^ 2)⁻¹) := fun N B ↦ by
      refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦ ?_)
      refine ((Measurable.const_add (Finset.measurable_sum _ fun k _ ↦ ?_) B).pow_const 2).inv
      split_ifs <;> fun_prop
    rw [lintegral_fin_succ (hm _ _)]
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc,
      Fin.zero_le, if_true, Fin.succ_le_succ_iff, Fin.le_zero_iff, Fin.succ_ne_zero, if_false,
      Finset.sum_const_zero, add_zero]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ 2)⁻¹ *
          ∏ i : Fin n, ((A + ‖z‖ ^ 2 + ∑ k, if k ≤ i then ‖w k‖ ^ 2 else 0) ^ 2)⁻¹) =
        ENNReal.ofReal (π ^ n / n !) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (n + 2))⁻¹) := fun z ↦ by
      simp only [ENNReal.ofReal_mul (show 0 ≤ ((A + ‖z‖ ^ 2) ^ 2)⁻¹ by positivity)]
      rw [lintegral_const_mul _ (hm _ _), ih (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), Nat.factorial_succ n]
    congr 1
    push_cast
    field_simp
    ring
end GlobalTheory.FlagVolume
