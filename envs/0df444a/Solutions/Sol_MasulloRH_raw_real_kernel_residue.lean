-- Prove2me | solution 1 for MasulloRH.raw_real_kernel_residue
-- status  : ACCEPTED   (prove)
-- author  : @phi9t
-- created : 2026-11-21T01:54:58.373361+00:00
-- url     : https://prove2.me/submissions/c7fdaa33-a804-453e-9e27-5c54ac9e5d34

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.RingNF

/-!
# Fixed-parameter endpoint checks for the Masullo trace reconstruction

These are local calibration and source-audit results. They assume no trace
identity, zero-free region, or Riemann hypothesis. The subtraction used below
belongs to the explicitly labeled mission reconstruction.

Only fixed-parameter limits are proved. Uniformity in the parameter, improper
integral divergence, full-interval integrability, and spectral sums are outside
the scope of this file.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace Argonaut.MasulloEndpoint

/-- A derivative at one controls division by the quadratic endpoint factor. -/
theorem quotient_limit_at_one {f : ℂ → ℂ} {d : ℂ}
    (hf : HasDerivAt f d 1) (hzero : f 1 = 0) :
    Tendsto (fun z : ℂ => f z / (z ^ 2 - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 (d / 2)) := by
  have hs : Tendsto (fun z : ℂ => f z / (z - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 d) := by
    simpa only [slope_fun_def_field, hzero, sub_zero] using hf.tendsto_slope
  have ha : Tendsto (fun z : ℂ => z + 1)
      (𝓝[≠] (1 : ℂ)) (𝓝 (2 : ℂ)) := by
    have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    convert hid.add_const (1 : ℂ) using 1
    norm_num
  have ht := hs.div ha (by norm_num : (2 : ℂ) ≠ 0)
  convert ht using 1
  funext z
  change f z / (z ^ 2 - 1) = (f z / (z - 1)) / (z + 1)
  rw [div_div]
  congr 1
  ring

private theorem cpow_hasDerivAt_one (p : ℂ) :
    HasDerivAt (fun z : ℂ => z ^ p) p 1 := by
  simpa using
    (Complex.hasStrictDerivAt_cpow_const (x := (1 : ℂ)) (c := p)
      (by simp)).hasDerivAt

/-- Subtracting a reference power cancels the endpoint singularity. -/
theorem cpow_sub_quotient_limit (p q : ℂ) :
    Tendsto (fun z : ℂ => (z ^ p - z ^ q) / (z ^ 2 - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 ((p - q) / 2)) := by
  exact quotient_limit_at_one
    ((cpow_hasDerivAt_one p).sub (cpow_hasDerivAt_one q)) (by simp)

/-- The unsubtracted power has nonzero endpoint residue. -/
theorem cpow_quotient_residue (p : ℂ) :
    Tendsto (fun z : ℂ => (z - 1) * z ^ p / (z ^ 2 - 1))
      (𝓝[≠] (1 : ℂ)) (𝓝 (1 / 2 : ℂ)) := by
  have hd : HasDerivAt (fun z : ℂ => (z - 1) * z ^ p) 1 1 := by
    simpa using!
      (((hasDerivAt_id (1 : ℂ)).sub_const 1).mul (cpow_hasDerivAt_one p))
  exact quotient_limit_at_one hd (by simp)

private theorem ofReal_tendsto_one_right :
    Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff]
    exact_mod_cast (ne_of_gt ht : t ≠ 1)

private theorem sqrt_tendsto_one_right :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  simpa using
    ((Real.continuous_sqrt.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).ofReal

/-- The actual real-place square-root factor preserves the cancellation. -/
theorem cpow_sub_real_kernel_limit (p q : ℂ) :
    Tendsto
      (fun t : ℝ => ((t : ℂ) ^ p - (t : ℂ) ^ q) *
        ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 ((p - q) / 2)) := by
  have hc := (cpow_sub_quotient_limit p q).comp ofReal_tendsto_one_right
  have hm := hc.mul sqrt_tendsto_one_right
  simp only [mul_one] at hm
  convert hm using 1
  funext t
  simp only [Function.comp_apply]
  push_cast
  ring

/-- Fixed-s endpoint limit for the mission's reconstructed archimedean integrand.
The parameter s is the unshifted zeta argument; the reference value is 5/2. -/
theorem regularizedArch_endpoint_limit (s : ℂ) :
    Tendsto
      (fun t : ℝ => ((t : ℂ) ^ (1 / 2 - s) - (t : ℂ) ^ (-2 : ℂ)) *
        ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (((5 / 2 : ℂ) - s) / 2)) := by
  convert cpow_sub_real_kernel_limit (1 / 2 - s) (-2 : ℂ) using 1
  congr 1
  ring

/-- The corresponding unsubtracted real-place integrand has residue 1/2.
This limit is not itself a formal proof of divergence of an improper integral. -/
theorem raw_real_kernel_residue (p : ℂ) :
    Tendsto
      (fun t : ℝ => ((t - 1 : ℝ) : ℂ) *
        ((t : ℂ) ^ p * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
  have hc := (cpow_quotient_residue p).comp ofReal_tendsto_one_right
  have hm := hc.mul sqrt_tendsto_one_right
  simp only [mul_one] at hm
  convert hm using 1
  funext t
  simp only [Function.comp_apply]
  push_cast
  ring

end Argonaut.MasulloEndpoint

theorem solution (p : ℂ) :
    Tendsto
      (fun t : ℝ => ((t - 1 : ℝ) : ℂ) *
        ((t : ℂ) ^ p * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
  exact Argonaut.MasulloEndpoint.raw_real_kernel_residue p

#print axioms solution
