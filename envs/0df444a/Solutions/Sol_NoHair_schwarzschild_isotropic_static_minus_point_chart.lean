-- Prove2me | solution 1 for NoHair.schwarzschild_isotropic_static_minus_point_chart
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:42:50.396121+00:00
-- url     : https://prove2.me/submissions/4fc949df-3637-4712-95ff-1e30ca95257b

import Theorems.Thm_NoHair_static_point_chart_of_smooth_kelvin_factor
open NoHair Set Filter Metric
open scoped Topology ContDiff
private abbrev X := ADMPoint
private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

theorem solution (Ω : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (R m : ℝ) (hR : 0 < R) (hm : 0 < m)
    (tail : ∀ x : ADMPoint, R<‖x‖ → x∈Ω ∧
      N x = (1-m/(2*‖x‖))/(1+m/(2*‖x‖)) ∧
      h x = (1+m/(2*‖x‖))^4 • (1:Matrix (Fin 3) (Fin 3) ℝ)) :
    ∃ a : StaticMinusPointChart Ω N h, a.radius = 1/R ∧
      (∀ y, a.change y = EuclideanGeometry.inversion (0:ADMPoint) 1 y) ∧
      ∀ y, a.coeff y = (m/2)^4 • (1:Matrix (Fin 3) (Fin 3) ℝ) := by
  apply static_point_chart_of_smooth_kelvin_factor Ω N h R hR (fun _ => m/2)
    contDiffOn_const (fun _ _ => half_pos hm) (fun x hx => (tail x hx).1)
  intro x hx
  obtain ⟨_,hl,hh⟩:=tail x hx
  have hn : 0<‖x‖ := hR.trans hx
  have hp : 0<1+m/(2*‖x‖) := by positivity
  have scalar : ((1+ -((1-m/(2*‖x‖))/(1+m/(2*‖x‖))))/2)^4 * (1+m/(2*‖x‖))^4 =
      (m/2/‖x‖)^4 := by
    rw [←mul_pow]
    congr 1
    field_simp [hp.ne',hn.ne'] <;> ring
  ext i j
  simp only [staticPositiveMetric,hl,hh,Matrix.smul_apply,smul_eq_mul]
  rw [←mul_assoc,scalar]
