-- Prove2me | solution 1 for MasulloRH.unrestricted_spectral_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:24:05.702747+00:00
-- url     : https://prove2.me/submissions/fc6b5a24-3e94-4e53-be9c-504328ef5f9d

import Theorems.Thm_ConnesRZ_explicit_formula
import Definitions.Def_MasulloRH_RationalTrace
open Set MeasureTheory MasulloRH
private theorem mellin_exp_coordinates (φ : ℝ → ℂ) (w : ℂ) :
    mellin φ w = ∫ u : ℝ, φ (Real.exp u) * Complex.exp (w * (u : ℂ)) := by
  let F (t : ℝ) := (t : ℂ) ^ (w - 1) • φ t
  have he := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn F
  rw [image_univ, Real.range_exp, setIntegral_univ] at he
  change (∫ t in Ioi 0, F t) = _
  rw [he]
  apply integral_congr_ae
  filter_upwards with u
  have hpos := Real.exp_pos u
  simp only [abs_of_pos hpos, F, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne' : (Real.exp u : ℂ) ≠ 0),
    ← Complex.ofReal_log hpos.le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add, mul_comm (φ _)]
  congr 2
  ring

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (fun ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} =>
      (ConnesRZ.zeroMult ρ.val : ℂ) * mellin φ (ρ.val - 1/2))
      (ConnesRZ.weilDistribution (fun u => φ (Real.exp u))) := by
  have hlog : ContinuousOn Real.log (tsupport φ) :=
    fun x hx => (Real.continuousAt_log (hφ.2.2.1 hx : 0 < x).ne').continuousWithinAt
  have hc := (show IsCompact (tsupport φ) from hφ.2.1).image_of_continuousOn hlog
  have htest : ConnesRZ.IsTest (fun u => φ (Real.exp u)) := by
    refine ⟨hφ.1.comp Real.contDiff_exp, hc.of_isClosed_subset (isClosed_tsupport _) ?_⟩
    apply closure_minimal _ hc.isClosed
    intro u hu
    exact ⟨Real.exp u, subset_tsupport φ hu, Real.log_exp u⟩
  simpa only [mellin_exp_coordinates, ConnesRZ.mellinHat] using
    ConnesRZ.explicit_formula (fun u => φ (Real.exp u)) htest
