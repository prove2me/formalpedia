-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_withdensity_to_iterated_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T07:30:47.964661+00:00
-- url     : https://prove2.me/submissions/5524c12c-0203-4fff-b8db-4885e6c8b516

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℝ) (ρ : Measure ℝ) (s : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal d * ∫⁻ y in Ici (0 : ℝ), (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∂volume := by
  have h_tail_meas : Measurable (fun y : ℝ => ρ (Ioi y)) :=
    (show Antitone (fun y : ℝ => ρ (Ioi y)) from fun a b hab =>
      measure_mono (fun x hx => mem_Ioi.mpr (lt_of_le_of_lt hab (mem_Ioi.mp hx)))).measurable
  set dens : ℝ → ℝ≥0∞ := fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0 with hdens
  have h_dens_meas : Measurable dens := by
    rw [hdens]
    apply Measurable.ite _ _ measurable_const
    · have hset : {y : ℝ | 0 ≤ y} = Ici (0 : ℝ) := by ext y; simp [mem_Ici]
      rw [hset]
      exact measurableSet_Ici
    · exact measurable_const.mul h_tail_meas
  have h_e_meas : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y))) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (by continuity : Continuous (fun y : ℝ => -s * y)))).measurable
  have hH_eq : ∀ y : ℝ, (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) =
      ENNReal.ofReal (Real.exp (-s * y)) * ρ (Ioi y) := fun y => setLIntegral_const _ _
  have h_ind : (dens * fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y))) =
      (Ici (0 : ℝ)).indicator (fun y : ℝ => ENNReal.ofReal d * (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) := by
    funext y
    simp only [Pi.mul_apply]
    by_cases hy0 : 0 ≤ y
    · simp only [hdens, if_pos hy0, Set.indicator_of_mem (mem_Ici.mpr hy0), hH_eq y]
      rw [mul_assoc, mul_comm (ρ (Ioi y)) _]
    · simp only [hdens, if_neg hy0, Set.indicator_of_notMem (fun h => hy0 (mem_Ici.mp h)), zero_mul]
  have hH_meas : Measurable (fun y : ℝ => ∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) := by
    have hH_fun : (fun y : ℝ => ∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) =
        (fun y : ℝ => ENNReal.ofReal (Real.exp (-s * y)) * ρ (Ioi y)) := funext hH_eq
    rw [hH_fun]
    exact h_e_meas.mul h_tail_meas
  rw [lintegral_withDensity_eq_lintegral_mul volume h_dens_meas h_e_meas, h_ind,
    lintegral_indicator measurableSet_Ici, lintegral_const_mul _ hH_meas]
