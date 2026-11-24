-- Prove2me | solution 1 for GlobalTheory.NearZeroDeriv.power_sum_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:22.405977+00:00
-- url     : https://prove2.me/submissions/7da2e6ae-3373-47e3-bf9e-d2ad72d99ca5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLargeVonMangoldtLogPowerSeriesNearZero
import Theorems.Thm_GlobalTheory_NearZeroDeriv_power_sum_mult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.NearZeroDeriv
namespace GlobalTheory.NearZeroDeriv
theorem _root_.solution {C : ℝ} (hC : 1 ≤ C)
    (hT : ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖)
    (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (r B : ℝ) (K : ℕ) (hr : 0 < r)
    (hs : ∀ w ∈ Z, s - w ≠ 0)
    (hB : ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ B / r ^ 2) (hK : 4 * (8 * C) ^ 2 * B ≤ K)
    (ρ : ℂ) (hρ : ρ ∈ Z) (hm : 1 ≤ m ρ) (hd : ‖s - ρ‖ ≤ 2 * r) :
    ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      3 / 4 * (1 / (4 * C * r)) ^ j ≤ ‖∑ w ∈ Z, (m w : ℂ) / (s - w) ^ j‖ := by
  set D := 8 * C * r with hD
  have hDp : 0 < D := by positivity
  have hB' : D ^ 2 * ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 ≤ K / 4 := by
    calc _ ≤ D ^ 2 * (B / r ^ 2) := by gcongr
      _ = (8 * C) ^ 2 * B := by rw [hD]; field_simp
      _ ≤ _ := by linarith
  have hsub : ∀ (p : ℂ → Prop) [DecidablePred p], ∑ w ∈ Z.filter p, (m w : ℝ) / ‖s - w‖ ^ 2
      ≤ ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 := fun p _ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  have hcount : ∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), m w ≤ K := by
    have : ((∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), m w : ℕ) : ℝ) ≤ K := by
      push_cast
      calc _ ≤ ∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2) := by
            refine Finset.sum_le_sum fun w hw => ?_
            rw [Finset.mem_filter] at hw
            have h0 : 0 < ‖s - w‖ := norm_pos_iff.2 (hs w hw.1)
            rw [mul_div_assoc', le_div_iff₀ (by positivity), mul_comm (D ^ 2)]
            gcongr
            exact hw.2
        _ ≤ D ^ 2 * ∑ w ∈ Z, (m w : ℝ) / ‖s - w‖ ^ 2 := by
            rw [← Finset.mul_sum]; gcongr; exact Finset.filter_subset _ _
        _ ≤ K := by have : (0 : ℝ) ≤ K := by positivity
                    linarith
    exact_mod_cast this
  have hρ' : ρ ∈ Z.filter (fun w => ‖s - w‖ ≤ D) :=
    Finset.mem_filter.2 ⟨hρ, hd.trans (by rw [hD]; nlinarith)⟩
  have hK1 : 1 ≤ K :=
    hm.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hρ').trans hcount)
  obtain ⟨j, h1, h2, h3⟩ := power_sum_mult hC hT _ m (fun w => 1 / (s - w)) K hcount ρ hρ' hm
  refine ⟨j, h1, h2, ?_⟩
  have h0 : 0 < ‖s - ρ‖ := norm_pos_iff.2 (hs ρ hρ)
  have h4 : (1 / (4 * C * r)) ^ j ≤
      ‖∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ j‖ := by
    simp only [one_div_pow, mul_one_div] at h3
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ _) h3
    rw [norm_div, norm_one, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have h5 : ‖∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2)‖
      ≤ 1 / 4 * (1 / (4 * C * r)) ^ (i + 2) := by
    calc _ ≤ ∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D),
            (1 / D ^ (i + 2)) * (D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)
          rw [Finset.mem_filter, not_le] at hw
          have h0 : 0 < ‖s - w‖ := hDp.trans hw.2
          have e : (1 / D ^ (i + 2)) * (D ^ 2 * ((m w : ℝ) / ‖s - w‖ ^ 2))
              = (m w : ℝ) / (D ^ i * ‖s - w‖ ^ 2) := by field_simp; ring
          rw [e, norm_div, norm_pow, Complex.norm_natCast, pow_add]
          gcongr
          exact hw.2.le
      _ ≤ (1 / D ^ (i + 2)) * (K / 4) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          gcongr
          exact le_trans (mul_le_mul_of_nonneg_left (hsub _) (by positivity)) hB'
      _ ≤ (1 / D ^ (i + 2)) * (2 ^ (i + 2) / 4) := by
          gcongr
          have : K ≤ 2 ^ (i + 2) := le_trans (by omega) (Nat.lt_two_pow_self (n := i + 2)).le
          exact_mod_cast this
      _ = _ := by
          rw [show D = 2 * (4 * C * r) by rw [hD]; ring, mul_pow, one_div_pow]
          field_simp
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun w => ‖s - w‖ ≤ D)]
  have := norm_sub_le (∑ w ∈ Z.filter (fun w => ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2) +
    ∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2))
    (∑ w ∈ Z.filter (fun w => ¬ ‖s - w‖ ≤ D), (m w : ℂ) / (s - w) ^ (i + 2))
  rw [add_sub_cancel_right] at this
  linarith
end GlobalTheory.NearZeroDeriv
