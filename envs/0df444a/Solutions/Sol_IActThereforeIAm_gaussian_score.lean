-- Prove2me | solution 1 for IActThereforeIAm.gaussian_score
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:12:40.65939+00:00
-- url     : https://prove2.me/submissions/169c98d0-c9b3-44dc-9628-336e81064357

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace IActThereforeIAm


theorem gaussian_score (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (u : ℝ) :
    deriv (fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) u = -(u - m) / v ∧
    deriv (deriv fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) u = -1 / v := by
  have hv' : (0:ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  set C : ℝ := Real.log ((Real.sqrt (2 * Real.pi * v))⁻¹) with hC
  have hf : (fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) =
      fun x => C + (-(x - m) ^ 2 / (2 * v)) := by
    funext x
    rw [ProbabilityTheory.gaussianPDFReal, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hd : ∀ u, HasDerivAt (fun x => C + (-(x - m) ^ 2 / (2 * v))) (-(u - m) / v) u := by
    intro u
    have := ((((hasDerivAt_id' u).sub_const m).pow 2).neg.div_const (2 * (v:ℝ))).const_add C
    refine this.congr_deriv ?_
    rw [div_eq_div_iff (by positivity) (by positivity)]
    norm_num
    ring
  have hdd : deriv (fun x => C + (-(x - m) ^ 2 / (2 * v))) = fun u => -(u - m) / v := by
    funext u; exact (hd u).deriv
  refine ⟨by rw [hf]; exact (hd u).deriv, ?_⟩
  rw [hf, hdd]
  have := (((hasDerivAt_id' u).sub_const m).neg.div_const (v:ℝ))
  exact (this.congr_deriv (by ring)).deriv


end IActThereforeIAm

open IActThereforeIAm in
theorem solution (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (u : ℝ) :
    deriv (fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) u = -(u - m) / v ∧
    deriv (deriv fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) u = -1 / v := by
  have hv' : (0:ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  set C : ℝ := Real.log ((Real.sqrt (2 * Real.pi * v))⁻¹) with hC
  have hf : (fun x => Real.log (ProbabilityTheory.gaussianPDFReal m v x)) =
      fun x => C + (-(x - m) ^ 2 / (2 * v)) := by
    funext x
    rw [ProbabilityTheory.gaussianPDFReal, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hd : ∀ u, HasDerivAt (fun x => C + (-(x - m) ^ 2 / (2 * v))) (-(u - m) / v) u := by
    intro u
    have := ((((hasDerivAt_id' u).sub_const m).pow 2).neg.div_const (2 * (v:ℝ))).const_add C
    refine this.congr_deriv ?_
    rw [div_eq_div_iff (by positivity) (by positivity)]
    norm_num
    ring
  have hdd : deriv (fun x => C + (-(x - m) ^ 2 / (2 * v))) = fun u => -(u - m) / v := by
    funext u; exact (hd u).deriv
  refine ⟨by rw [hf]; exact (hd u).deriv, ?_⟩
  rw [hf, hdd]
  have := (((hasDerivAt_id' u).sub_const m).neg.div_const (v:ℝ))
  exact (this.congr_deriv (by ring)).deriv

