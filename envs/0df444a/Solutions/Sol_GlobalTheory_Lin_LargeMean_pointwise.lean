-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:42.607306+00:00
-- url     : https://prove2.me/submissions/c5b331e0-0b32-4fbd-8401-2bbb8e016a66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_nonneg
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_small
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_large
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_pp
import Theorems.Thm_GlobalTheory_Lin_LargeMean_rpow_form

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
noncomputable section
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.LargeMean
namespace GlobalTheory.Lin.LargeMean
theorem _root_.solution (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (n : ℕ) :
    ‖((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n -
      (if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0)‖ ≤
      δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) +
        (4 * r) ^ k * ((if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primesIoc]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have key : ∀ w : ℝ, 0 ≤ w → ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ Λ n / n * w := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hc n)
  have hpw : 0 ≤ pw k (r * Real.log n) := pw_nonneg k (by positivity)
  have fin : ∀ w : ℝ, 0 ≤ w → w ≤ δ ^ k * Real.exp (-(r * Real.log n / 2)) →
      ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) := by
    intro w hw h
    refine (key w hw).trans ?_
    rw [rpow_form n hn]
    calc _ ≤ Λ n / n * (δ ^ k * Real.exp (-(r * Real.log n / 2))) := by gcongr
      _ = _ := by ring_nf
  by_cases hp : n.Prime
  · simp only [hp, if_true, zero_div, mul_zero, add_zero]
    split_ifs with hm
    · rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le] at hm
      rw [Real.log_exp]
      have e0 : r * (32 / δ * K / r) = 32 / δ * K := by field_simp
      rw [e0]
      have e : ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n - (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (32 / δ * K) : ℝ) : ℂ) =
          ((Λ n / n * pw k (32 / δ * K) : ℝ) : ℂ) * c n := by
        rw [vonMangoldt_apply_prime hp]; push_cast; ring
      rw [e]
      refine fin _ (pw_nonneg k (by positivity)) ((pw_large K k hδ le_rfl h2).trans ?_)
      have h3 : Real.log n ≤ 32 / δ * K / r := by
        rw [Real.log_le_iff_le_exp hn']; exact hm.1.2
      rw [le_div_iff₀ hr] at h3
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    · rw [sub_zero]
      refine fin _ hpw ?_
      rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le,
        Nat.floor_lt (Real.exp_pos _).le] at hm
      by_cases h4 : Real.exp (δ / 3 * K / r) < n
      · have h5 : Real.exp (32 / δ * K / r) < n := by
          by_contra h6
          exact hm ⟨⟨h4, not_lt.mp h6⟩, hp⟩
        refine pw_large K k hδ ?_ h2
        have h3 := (Real.lt_log_iff_exp_lt hn').mpr h5
        rw [div_lt_iff₀ hr] at h3
        linarith
      · refine pw_small K k hδ (by positivity) ?_ h1
        have h3 := (Real.log_le_iff_le_exp hn').mpr (not_lt.mp h4)
        rw [le_div_iff₀ hr] at h3
        linarith
  · have hm : n ∉ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) := by
      rw [primesIoc, Finset.mem_filter]; exact fun h => hp h.2
    simp only [hp, hm, if_false, sub_zero]
    refine (key _ hpw).trans (le_add_of_nonneg_of_le (by positivity) ?_)
    have e : (3 / 4 : ℝ) = 1 + (-1 / 4) := by norm_num
    rw [e, rpow_form n hn]
    calc _ ≤ Λ n / n * ((4 * r) ^ k * Real.exp (Real.log n / 4)) := by
          gcongr; exact pw_pp k hr hl
      _ = _ := by ring_nf
end GlobalTheory.Lin.LargeMean
