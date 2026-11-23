-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_boundary_energy_quadrature
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:54:01.150971+00:00
-- url     : https://prove2.me/submissions/d43a16f1-ac79-44bb-991a-eb63696b15f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_gauss_four_panel_upper_error
import Theorems.Thm_GrothendieckLB_Supplement_cq_energy_gauss_node_sum
import Theorems.Thm_GrothendieckLB_Supplement_cq_energy_panel_eighth_derivative_bounds
import Theorems.Thm_GrothendieckLB_Supplement_cq_energy_panels_smooth
import Mathlib

open GrothendieckLB.Supplement CQBoundary GaussFour MeasureTheory

theorem solution :
    Real.pi⁻¹ * (∫ θ in (0:ℝ)..Real.pi, CQBoundary.energy θ) ≤ 126.80385221 := by
  let D : ℝ := Real.pi/1024
  let a (i : ℕ) : ℝ := (i:ℝ)*D
  have hD : D ≠ 0 := div_ne_zero Real.pi_ne_zero (by norm_num)
  have hcts : Continuous energy := by
    have he : energy = fun t : ℝ => panel 0 (t/D) := by
      funext t
      unfold panel
      simp only [Nat.cast_zero,zero_mul,zero_add]
      congr 1
      change t=D*(t/D)
      field_simp
    rw [he]
    exact (cq_energy_panels_smooth 0).continuous.comp (continuous_id.div_const D)
  have eqpanel (i : ℕ) : D*(∫ x in (0:ℝ)..1, panel i x) = ∫ θ in a i..a (i+1), energy θ := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a:=(0:ℝ)) (b:=1) energy D (a i)
    change D*(∫ x in (0:ℝ)..1, energy (a i+D*x)) = ∫ θ in a i+D*0..a i+D*1, energy θ at h
    rw [mul_zero,add_zero,mul_one] at h
    simpa only [panel,a,Nat.cast_add,Nat.cast_one,add_mul,one_mul,D] using h
  have he : D*(∑ i ∈ Finset.range 1024, ∫ x in (0:ℝ)..1, panel i x)=∫ θ in (0:ℝ)..Real.pi, energy θ := by
    rw [Finset.mul_sum]
    simp_rw [eqpanel]
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hcts.intervalIntegrable (a k) (a (k+1)))]
    have hp : a 1024=Real.pi := by dsimp [a,D]; ring
    rw [hp,show a 0=0 by simp [a]]
  obtain ⟨B,hB,hrem⟩ := cq_energy_panel_eighth_derivative_bounds
  have hsum := Finset.sum_le_sum (s:=Finset.range 1024) (fun i hi =>
    gauss_four_panel_upper_error (panel i) (B i) (cq_energy_panels_smooth i) (hB i (Finset.mem_range.mp hi)))
  rw [Finset.sum_add_distrib] at hsum
  have hnorm : Real.pi⁻¹*(∫ θ in (0:ℝ)..Real.pi, energy θ)=
      (∑ i ∈ Finset.range 1024, ∫ x in (0:ℝ)..1, panel i x)/1024 := by
    rw [←he,←mul_assoc]
    dsimp [D]
    field_simp
  rw [hnorm]
  linarith only [hsum,hrem,cq_energy_gauss_node_sum]
