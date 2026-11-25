-- Prove2me | solution 1 for GlobalTheory.FlagVolume.lintegral_pi_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:42.560729+00:00
-- url     : https://prove2.me/submissions/71476535-7d03-4ce3-88c9-f7afad673ea0

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
theorem _root_.solution (n : ℕ) : ∀ (m : ℕ) {A : ℝ}, 0 < A →
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((A + ∑ k, ‖z k‖ ^ 2) ^ (m + n + 1))⁻¹) =
      ENNReal.ofReal (π ^ n * m ! / (m + n)! * (A ^ (m + 1))⁻¹) := by
  induction n with
  | zero =>
    intro m A hA
    have : (m ! : ℝ) ≠ 0 := by positivity
    simp [volume_pi, this]
  | succ n ih =>
    intro m A hA
    rw [lintegral_fin_succ (by fun_prop)]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← add_assoc]
    have h : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ,
        ENNReal.ofReal (((A + ‖z‖ ^ 2 + ∑ k, ‖w k‖ ^ 2) ^ (m + n + 1 + 1))⁻¹) =
        ENNReal.ofReal (π ^ n * (m + 1)! / (m + 1 + n)!) *
          ENNReal.ofReal (((A + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := fun z ↦ by
      rw [← ENNReal.ofReal_mul (by positivity), ← ih (m + 1) (by positivity),
        show m + 1 + n = m + n + 1 by ring]
    simp only [h]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_complex_inv_pow hA,
      ← ENNReal.ofReal_mul (by positivity), show m + 1 + n = m + n + 1 by ring,
      Nat.factorial_succ m]
    congr 1
    push_cast
    field_simp
    ring
end GlobalTheory.FlagVolume
