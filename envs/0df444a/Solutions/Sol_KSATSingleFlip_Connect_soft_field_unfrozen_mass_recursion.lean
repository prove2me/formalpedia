-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_unfrozen_mass_recursion
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:53:21.881986+00:00
-- url     : https://prove2.me/submissions/aed9f4f6-5c09-43f1-99f1-8d6b64e37781

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_jump_moments
import Theorems.Thm_KSATSingleFlip_Connect_symmetric_compound_exponential_moment
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_potential_bounds
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν) (hcosh : Integrable Real.cosh ν) :
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(Rbeta β ν)) =
      ENNReal.ofReal (β*Real.exp (∫ z, Real.cosh z ∂ν)) := by
  let u : ℝ := ∫ z, Real.cosh z ∂ν
  let h : ℝ := hPot ν
  let μ : Measure ℝ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
  let P : Measure ℝ := compoundPoisson μ
  let K : Measure ℝ := P ∗ Measure.map (fun z : ℝ => -z) P
  have hu : 0 ≤ u := integral_nonneg (fun z => le_of_lt (Real.cosh_pos z))
  have hh : 0 ≤ h := (soft_field_potential_bounds ν).2.1
  have hjump := soft_field_jump_moments ν hsym hcosh
  change μ Set.univ = ENNReal.ofReal (u+h/2) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = ENNReal.ofReal (2*u) ∧
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ) = ENNReal.ofReal u at hjump
  letI : IsFiniteMeasure μ := ⟨by rw [hjump.1]; exact ENNReal.ofReal_lt_top⟩
  have hmass : (μ Set.univ).toReal = u+h/2 := by
    rw [hjump.1, ENNReal.toReal_ofReal (by positivity)]
  have hpos : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ).toReal = 2*u := by
    rw [hjump.2.1, ENNReal.toReal_ofReal (by positivity)]
  have hneg : (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ).toReal = u := by
    rw [hjump.2.2, ENNReal.toReal_ofReal hu]
  have hposfin : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≠ ∞ := by rw [hjump.2.1]; exact ENNReal.ofReal_ne_top
  have hnegfin : (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ) ≠ ∞ := by rw [hjump.2.2]; exact ENNReal.ofReal_ne_top
  have hproduct : Real.exp (-(u+h/2))*Real.exp (2*u) * (Real.exp (-(u+h/2))*Real.exp u) = Real.exp (u-h) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hp : (∫⁻ z, ENNReal.ofReal (Real.exp z) ∂K) = ENNReal.ofReal (Real.exp (u-h)) := by
    have hv := symmetric_compound_exponential_moment μ 1 (by simpa using hposfin) (by simpa using hnegfin)
    simp only [one_mul, neg_one_mul] at hv
    rw [hmass,hpos,hneg,hproduct] at hv
    exact hv
  have hn : (∫⁻ z, ENNReal.ofReal (Real.exp (-z)) ∂K) = ENNReal.ofReal (Real.exp (u-h)) := by
    have hv := symmetric_compound_exponential_moment μ (-1) (by simpa using hnegfin) (by simpa using hposfin)
    simp only [neg_one_mul, neg_neg, one_mul] at hv
    rw [hmass,hneg,hpos] at hv
    have hp' : Real.exp (-(u+h/2))*Real.exp u * (Real.exp (-(u+h/2))*Real.exp (2*u)) = Real.exp (u-h) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hp'] at hv
    exact hv
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp z)) := by fun_prop
  have hg : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-z))) := by fun_prop
  have hK : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂K) = ENNReal.ofReal (Real.exp (u-h)) := by
    have hpoint (z : ℝ) : ENNReal.ofReal (Real.cosh z) = ENNReal.ofReal (1/2:ℝ) *
        (ENNReal.ofReal (Real.exp z)+ENNReal.ofReal (Real.exp (-z))) := by
      rw [← ENNReal.ofReal_add (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2), Real.cosh_eq]
      congr 1
      ring
    simp_rw [hpoint]
    change (∫⁻ z, ENNReal.ofReal (1/2:ℝ) * ((fun z => ENNReal.ofReal (Real.exp z)) + (fun z => ENNReal.ofReal (Real.exp (-z)))) z ∂K) = _
    rw [lintegral_const_mul _ (hf.add hg)]
    change ENNReal.ofReal (1/2:ℝ) * (∫⁻ z, ENNReal.ofReal (Real.exp z)+ENNReal.ofReal (Real.exp (-z)) ∂K) = _
    rw [lintegral_add_left hf, hp, hn]
    rw [← ENNReal.ofReal_add (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    ring
  change (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂((ENNReal.ofReal (β*Real.exp h)) • K)) = ENNReal.ofReal (β*Real.exp u)
  rw [lintegral_smul_measure, smul_eq_mul, hK, ← ENNReal.ofReal_mul (mul_nonneg hβ (le_of_lt (Real.exp_pos _)))]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring
