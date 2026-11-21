-- Prove2me | solution 1 for MasulloRH.trace_formula_rational_full_strip
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:28:54.459691+00:00
-- url     : https://prove2.me/submissions/05856ebd-c0e5-4c2a-ae8f-c5ea95711a47

import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place

set_option autoImplicit false
open MeasureTheory Set MasulloRH

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ (1 / 2)) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip (1 / 2), zetaTraceTerm φ (1 / 2) ρ := by
  let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | 1/2 ≤ |ρ.val.re - 1/2|}
  let : IsEmpty omitted := ⟨fun r => by
    have h := (r.val.property : ConnesRZ.IsCriticalZero r.val.val)
    have hlt : |r.val.val.re - 1/2| < 1/2 :=
      abs_lt.mpr ⟨by linarith [h.2.1], by linarith [h.2.2]⟩
    exact (not_le_of_gt hlt) r.property⟩
  obtain ⟨hi, hp, hz, _, hid⟩ := trace_window_comparison (1/2) φ hφ
  refine ⟨hi, hp, hz, ?_⟩
  have hzero : (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 :=
    tsum_empty
  rw [hzero, add_zero, archTerm_log_test_eq_neg_real_place φ hφ] at hid
  linear_combination hid
