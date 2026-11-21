-- Prove2me | solution 2 for MasulloRH.narrow_window_omitted_zero_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:33:09.642119+00:00
-- url     : https://prove2.me/submissions/8543dfa0-5cc4-490d-864f-3c91bc630c98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_regularized_trace_scalar_lower_bound
import Theorems.Thm_MasulloRH_single_resolvent_test
import Definitions.Def_ConnesRZ_weil_defs

open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
  have hbound := regularized_trace_scalar_lower_bound α hα hsmall
  rw [← regularized_initial_identity_full_strip 3 (by norm_num)] at hbound
  have hin := (single_resolvent_test α).mp hbound
  let O := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
  have : IsEmpty O := by
    constructor
    intro r
    obtain ⟨hz, h0, h1⟩ := r.val.property
    have hfull : |r.val.val.re - 1/2| < 1/2 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (not_lt_of_ge r.property) (hin ⟨r.val.val, hz, h0, h1, hfull⟩)
  change (∑' r : O, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0
  simp
