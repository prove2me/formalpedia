-- Prove2me | solution 1 for HairerSPDE.exists_measurableSet_gaussianReal_sub_ge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T17:20:52.650761+00:00
-- url     : https://prove2.me/submissions/55718ffd-967e-4766-9980-28acb8aef6c3

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HairerSPDE

private lemma gaussianPDFReal_mean_le_midpoint_bound {m x : ℝ}
    (hx : m * (x - m / 2) ≤ 0) :
    gaussianPDFReal m 1 x ≤
      Real.exp (-m ^ 2 / 8) * gaussianPDFReal (m / 2) 1 x := by
  rw [gaussianPDFReal]
  have he : -(x - m) ^ 2 / (2 * (1 : ℝ)) ≤
      -m ^ 2 / 8 + -(x - m / 2) ^ 2 / (2 * (1 : ℝ)) := by
    nlinarith
  have := Real.exp_le_exp.mpr he
  rw [Real.exp_add] at this
  calc
    (√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * (1 : ℝ))) ≤
        (√(2 * Real.pi * (1 : ℝ)))⁻¹ *
          (Real.exp (-m ^ 2 / 8) * Real.exp (-(x - m / 2) ^ 2 / (2 * (1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    _ = Real.exp (-m ^ 2 / 8) *
        ((√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - m / 2) ^ 2 / (2 * (1 : ℝ)))) := by ring

private lemma gaussianPDFReal_zero_le_midpoint_bound {m x : ℝ}
    (hx : 0 ≤ m * (x - m / 2)) :
    gaussianPDFReal 0 1 x ≤
      Real.exp (-m ^ 2 / 8) * gaussianPDFReal (m / 2) 1 x := by
  rw [gaussianPDFReal]
  have he : -(x - 0) ^ 2 / (2 * (1 : ℝ)) ≤
      -m ^ 2 / 8 + -(x - m / 2) ^ 2 / (2 * (1 : ℝ)) := by
    nlinarith
  have := Real.exp_le_exp.mpr he
  rw [Real.exp_add] at this
  calc
    (√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤
        (√(2 * Real.pi * (1 : ℝ)))⁻¹ *
          (Real.exp (-m ^ 2 / 8) * Real.exp (-(x - m / 2) ^ 2 / (2 * (1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    _ = Real.exp (-m ^ 2 / 8) *
        ((√(2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - m / 2) ^ 2 / (2 * (1 : ℝ)))) := by ring

theorem gaussianTVProof (m : ℝ) :
    ∃ A : Set ℝ, MeasurableSet A ∧
      1 - Real.exp (-m ^ 2 / 8)
        ≤ (gaussianReal 0 1 A).toReal - (gaussianReal m 1 A).toReal := by
  let A : Set ℝ := {x | m * (x - m / 2) ≤ 0}
  have hA : MeasurableSet A := by
    exact measurableSet_le (measurable_const.mul (measurable_id.sub measurable_const)) measurable_const
  refine ⟨A, hA, ?_⟩
  have hp_int : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal _ _
  have hq_int : Integrable (gaussianPDFReal m 1) := integrable_gaussianPDFReal _ _
  have hr_int : Integrable (fun x ↦ Real.exp (-m ^ 2 / 8) *
      gaussianPDFReal (m / 2) 1 x) :=
    (integrable_gaussianPDFReal (m / 2) 1).const_mul _
  have htail :
      (∫ x in Aᶜ, gaussianPDFReal 0 1 x) +
          (∫ x in A, gaussianPDFReal m 1 x) ≤ Real.exp (-m ^ 2 / 8) := by
    calc
      (∫ x in Aᶜ, gaussianPDFReal 0 1 x) +
          (∫ x in A, gaussianPDFReal m 1 x)
          = ∫ x, ((Aᶜ).indicator (gaussianPDFReal 0 1) x +
              A.indicator (gaussianPDFReal m 1) x) := by
                rw [integral_add (hp_int.indicator hA.compl) (hq_int.indicator hA),
                  integral_indicator hA.compl, integral_indicator hA]
      _ ≤ ∫ x, Real.exp (-m ^ 2 / 8) * gaussianPDFReal (m / 2) 1 x := by
        apply integral_mono
        · exact (hp_int.indicator hA.compl).add (hq_int.indicator hA)
        · exact hr_int
        · intro x
          by_cases hx : x ∈ A
          · have hx' : m * (x - m / 2) ≤ 0 := hx
            simpa [Set.indicator, hx] using gaussianPDFReal_mean_le_midpoint_bound hx'
          · have hx' : 0 ≤ m * (x - m / 2) := le_of_not_ge hx
            have hxc : x ∈ Aᶜ := hx
            simpa [Set.indicator, hx] using gaussianPDFReal_zero_le_midpoint_bound hx'
      _ = Real.exp (-m ^ 2 / 8) := by
        rw [integral_const_mul, integral_gaussianPDFReal_eq_one (m / 2) (by norm_num)]
        ring
  have hpA_nonneg : 0 ≤ ∫ x in A, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x)
  have hqA_nonneg : 0 ≤ ∫ x in A, gaussianPDFReal m 1 x :=
    integral_nonneg (fun x ↦ gaussianPDFReal_nonneg m 1 x)
  rw [gaussianReal_apply_eq_integral 0 (by norm_num) A,
    gaussianReal_apply_eq_integral m (by norm_num) A,
    ENNReal.toReal_ofReal hpA_nonneg, ENNReal.toReal_ofReal hqA_nonneg]
  have hp_split :
      (∫ x in A, gaussianPDFReal 0 1 x) +
          (∫ x in Aᶜ, gaussianPDFReal 0 1 x) = 1 := by
    rw [integral_add_compl hA hp_int,
      integral_gaussianPDFReal_eq_one 0 (by norm_num)]
  linarith

end HairerSPDE

theorem solution (m : ℝ) :
    ∃ A : Set ℝ, MeasurableSet A ∧
      1 - Real.exp (-m ^ 2 / 8)
        ≤ (gaussianReal 0 1 A).toReal - (gaussianReal m 1 A).toReal :=
  HairerSPDE.gaussianTVProof m
