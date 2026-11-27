-- Prove2me | solution 1 for GlobalTheory.log_exp_mul_le_of_generator_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:11.206485+00:00
-- url     : https://prove2.me/submissions/398c32b2-10af-40fd-a372-ce51cf2857d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LogExpMulLeOfGeneratorSupBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private theorem log_one_add_le_log_two_add_of_log_le (x M : ℝ) (hx : 0 < x) (hM : 0 ≤ M)
    (h : Real.log x ≤ M) : Real.log (1 + x) ≤ Real.log 2 + M := by
  rcases le_or_gt x 1 with h1 | h1
  · have : Real.log (1 + x) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
    linarith
  · have : Real.log (1 + x) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx.ne'] at this
    linarith
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 800000
namespace GlobalTheory
theorem _root_.solution : ∀ (f r n d : ℕ) (L ℓ a rd lam t c S v p1 : ℝ), 2 ≤ L → 1 ≤ f → 1 ≤ r → r ≤ n → (d : ℝ) ≤ a → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log f ≤ 2 * L → 1 ≤ rd → Real.log rd ≤ 2 * L → 0 < lam → Real.log (1 / lam ^ 2) ≤ 80 * L → 0 < t → 0 ≤ ℓ → 0 ≤ p1 → p1 ≤ Real.exp ℓ → 0 ≤ c → c ≤ Real.exp (f * r * n * L) → 0 ≤ S → S ≤ 2 * v → v ≤ c * (p1 * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (f * r : ℕ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) / (Real.sqrt Real.pi * lam)) ^ (f * r * n)) → Real.log (Real.exp (-((d : ℝ) / 2) * Real.log (Real.pi * t)) * S) ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by
  intro f r n d L ℓ a rd lam t c S v p1 hL hf hr hrn hda ha hn hfL hrd hrdL hlam hlamL ht hℓ hp1
    hp1ℓ hc hcL hS hSv hv
  have hf' : 0 < f := by omega
  have hr' : 0 < r := by omega
  have hn' : 0 < n := by omega
  have hf0 : (0:ℝ) < f := by exact_mod_cast hf'
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr'
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn'
  have hrd0 : (0:ℝ) < rd := by linarith
  have hfr0 : (0:ℝ) < ((f * r : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hf' hr'
  have hrnR : (r:ℝ) ≤ n := by exact_mod_cast hrn
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have ha0 : 0 ≤ a := hd0.trans hda
  have hK1 : (1:ℝ) ≤ (f:ℝ) * r * n := by
    have h1 : 1 ≤ f * r * n := Nat.mul_pos (Nat.mul_pos hf' hr') hn'
    exact_mod_cast h1
  have hlog2 := Real.log_two_lt_d9
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hsqpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsq1 : 0 < Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n) := Real.sqrt_pos.mpr (by positivity)
  have hfp : 0 < (f : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hf0 _
  set X := 4 * Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)
    / (Real.sqrt Real.pi * lam) with hX
  have hX0 : 0 < X := by positivity
  have hlogX : Real.log X ≤ 3.5 * Real.log 2 + 49 * L := by
    have e1 : Real.log (Real.sqrt (2 * ((f * r : ℕ) : ℝ) * n))
        = (Real.log 2 + Real.log f + Real.log r + Real.log n) / 2 := by
      rw [Real.log_sqrt (by positivity)]
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      ring
    have e2 : Real.log (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)
        = Real.log 2 + 3 / 2 * Real.log f + 2 * Real.log n + Real.log rd := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_rpow hf0, Real.log_pow]
      push_cast
      ring
    have e3 : Real.log (Real.sqrt Real.pi * lam) = Real.log Real.pi / 2 + Real.log lam := by
      rw [Real.log_mul hsqpi.ne' hlam.ne', Real.log_sqrt hpi.le]
    have e4 : Real.log (1 / lam ^ 2) = -2 * Real.log lam := by
      rw [one_div, Real.log_inv, Real.log_pow]
      push_cast
      ring
    have e5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have hlr : Real.log r ≤ Real.log n := Real.log_le_log hr0 hrnR
    have hlogf0 : 0 ≤ Real.log f := Real.log_nonneg (by exact_mod_cast hf)
    have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
    rw [hX, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), e1, e2, e3, e5]
    rw [e4] at hlamL
    nlinarith
  have hC : Real.log (1 + X) ≤ 55 * L := by
    have := log_one_add_le_log_two_add_of_log_le X (3.5 * Real.log 2 + 49 * L) hX0
      (by nlinarith) hlogX
    nlinarith
  have hRHS0 : 0 ≤ ℓ + 10 * L * a + 200 * f * r * n * L := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ L) ha0,
      mul_nonneg (by linarith : (0:ℝ) ≤ (f:ℝ) * r * n) (by linarith : (0:ℝ) ≤ L)]
  rcases hS.eq_or_lt with hS0 | hSpos
  · rw [← hS0, mul_zero, Real.log_zero]
    exact hRHS0
  set E := (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) with hEdef
  have hE : 0 < E ∧ Real.log E - (d / 2) * Real.log (Real.pi * t) ≤ 10 * L * a := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [hEdef, Nat.cast_zero, zero_div, Real.rpow_zero, Real.log_one, zero_mul, sub_zero]
      exact ⟨one_pos, by nlinarith⟩
    · have hdR : (0:ℝ) < d := by exact_mod_cast hd
      have hB : 0 < Real.pi * Real.exp 1 * t * d := by positivity
      refine ⟨Real.rpow_pos_of_pos hB _, ?_⟩
      rw [hEdef, Real.log_rpow hB, Real.log_mul (by positivity) hdR.ne',
        Real.log_mul (by positivity) ht.ne', Real.log_mul hpi.ne' (Real.exp_pos 1).ne',
        Real.log_mul hpi.ne' ht.ne', Real.log_exp]
      have hld : Real.log d ≤ 2 * L :=
        (Real.log_le_log hdR (by linarith)).trans ha
      nlinarith [mul_le_mul_of_nonneg_left hld (by linarith : (0:ℝ) ≤ d / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ a - d) (by linarith : (0:ℝ) ≤ 1 + 2 * L),
        mul_nonneg ha0 (by linarith : (0:ℝ) ≤ L - 2)]
  obtain ⟨hE0, hEb⟩ := hE
  have hvpos : 0 < v := by linarith
  have hcpos : 0 < c := by
    rcases hc.eq_or_lt with h | h
    · rw [← h, zero_mul] at hv
      linarith
    · exact h
  have hp1pos : 0 < p1 := by
    rcases hp1.eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul, zero_mul, mul_zero] at hv
      linarith
    · exact h
  have hsq2 : 0 < Real.sqrt 2 := by positivity
  have hC0 : 0 < 1 + X := by linarith
  have hprod : Real.log (c * (p1 * E * Real.sqrt 2 * (1 + X) ^ (f * r * n)))
      = Real.log c + Real.log p1 + Real.log E + Real.log 2 / 2
        + ((f:ℝ) * r * n) * Real.log (1 + X) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_sqrt (by norm_num)]
    push_cast
    ring
  have hlv : Real.log v ≤ Real.log (c * (p1 * E * Real.sqrt 2 * (1 + X) ^ (f * r * n))) :=
    Real.log_le_log hvpos hv
  have hlS : Real.log S ≤ Real.log 2 + Real.log v := by
    rw [← Real.log_mul (by norm_num) hvpos.ne']
    exact Real.log_le_log hSpos hSv
  have hlc : Real.log c ≤ (f:ℝ) * r * n * L := by
    have := Real.log_le_log hcpos hcL
    rwa [Real.log_exp] at this
  have hlp : Real.log p1 ≤ ℓ := by
    have := Real.log_le_log hp1pos hp1ℓ
    rwa [Real.log_exp] at this
  have hKC : ((f:ℝ) * r * n) * Real.log (1 + X) ≤ ((f:ℝ) * r * n) * (55 * L) :=
    mul_le_mul_of_nonneg_left hC (by linarith)
  have hKL : 2 ≤ ((f:ℝ) * r * n) * L := by nlinarith
  rw [Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp]
  rw [hprod] at hlv
  nlinarith
end GlobalTheory
