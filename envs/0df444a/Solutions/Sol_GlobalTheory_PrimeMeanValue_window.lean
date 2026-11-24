-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:07.589472+00:00
-- url     : https://prove2.me/submissions/d49010fd-bacf-4c31-b7e9-15e11c7ec2d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe
import Theorems.Thm_GlobalTheory_PrimeMeanValue_orth
import Theorems.Thm_GlobalTheory_PrimeMeanValue_mem_primesIoc

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
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution (C : ℝ) (hC : 0 < C)
    (hB : ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y →
      (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤
        C * y / (q.totient * Real.log (y / q)))
    (q : ℕ) [NeZero q] (T N x : ℝ) (a : ℕ → ℂ) (S : Finset ℕ) (hT : 1 ≤ T)
    (hN : (2 * q * T) ^ 2 ≤ N) (hx : 0 < x)
    (hS : ∀ n ∈ S, n.Prime ∧ N < n ∧ x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, 4 * C * n / (T * Real.log n) * ‖a n‖ ^ 2 := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ 1 / T := by positivity
  have hqT : (q : ℝ) ≤ q * T := le_mul_of_one_le_right (by positivity) hT
  have hcop : ∀ n ∈ S, Nat.Coprime n q := fun n hn => by
    obtain ⟨hp, h1, -, -⟩ := hS n hn
    have : (q : ℝ) < n := by nlinarith
    have hlt : q < n := by exact_mod_cast this
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hq hlt)
  have e3 := Real.abs_exp_sub_one_le (x := 1 / T)
    (by rw [abs_of_nonneg hδ, div_le_one hT0]; exact hT)
  rw [abs_of_nonneg hδ] at e3
  have e4 : Real.exp (1 / T) - 1 ≤ 2 * (1 / T) := (le_abs_self _).trans e3
  have e5 : x * Real.exp (1 / T) ≤ x + 2 * x / T := by
    have := mul_le_mul_of_nonneg_left e4 hx.le
    have e : x * (2 * (1 / T)) = 2 * x / T := by ring
    linarith
  have e6 : 2 * x / T ≤ 2 * x := div_le_self (by positivity) hT
  refine (orth q S a hcop).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hp, h1, h2, h3⟩ := hS n hn
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hn3 : (n : ℝ) ≤ 3 * x := by linarith
  have hx3 : (2 * q * T) ^ 2 ≤ 3 * x := by linarith
  have hY : 2 * (q : ℝ) ≤ 2 * x / T := by
    rw [le_div_iff₀ hT0]; nlinarith
  have hb := hB q n x (2 * x / T) hq (hcop n hn) hx.le hY
  have hsub : S.filter (fun m => m ≡ n [MOD q]) ⊆
      (primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q]) := by
    refine Finset.filter_subset_filter _ fun m hm => ?_
    obtain ⟨hp', -, h2', h3'⟩ := hS m hm
    exact (mem_primesIoc hx.le).2 ⟨h2', h3'.trans e5, hp'⟩
  have hc : ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) ≤
      (((primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q])).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : (n : ℝ) ≤ (2 * x / T / q) ^ 2 := by
    rw [div_div, div_pow, le_div_iff₀ (by positivity)]
    have h4 : (T * q) ^ 2 ≤ 3 * x / 4 := by nlinarith
    calc (n : ℝ) * (T * q) ^ 2 ≤ (3 * x) * (3 * x / 4) := by gcongr
      _ ≤ (2 * x) ^ 2 := by nlinarith
  have hl : Real.log n / 2 ≤ Real.log (2 * x / T / q) := by
    have := Real.log_le_log (by linarith) hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  calc (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ)
      ≤ q.totient * (C * (2 * x / T) / (q.totient * Real.log (2 * x / T / q))) :=
        mul_le_mul_of_nonneg_left (hc.trans hb) hφ.le
    _ ≤ q.totient * (C * (2 * n / T) / (q.totient * (Real.log n / 2))) := by gcongr
    _ = 4 * C * n / (T * Real.log n) := by field_simp; ring
end GlobalTheory.PrimeMeanValue
