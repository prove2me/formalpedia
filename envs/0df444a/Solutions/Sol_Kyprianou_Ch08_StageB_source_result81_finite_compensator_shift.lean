-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_finite_compensator_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:47:42.429589+00:00
-- url     : https://prove2.me/submissions/55b69851-d762-4043-9098-88a2f4507676

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hneg : ν (Ici (0 : ℝ)) = 0) :
    let C := ∫ y, (Ioo (-1 : ℝ) 0).indicator id y ∂ν
    (∀ ξ : ℝ, Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ν →
      (∫ y, levyCompensatedIntegrand ξ y ∂ν) =
        (∫ y : ℝ, (Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ∂ν) -
          ((ξ : ℂ) * Complex.I) * (C : ℂ)) ∧
    (∀ β : ℝ, Integrable (fun y => Real.exp (β * y) - 1) ν →
      (∫ y, Real.exp (β * y) - 1 - (if -1 < y then β * y else 0) ∂ν) =
        (∫ y, Real.exp (β * y) - 1 ∂ν) - β * C) := by
  let g : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator id
  have hb : IntegrableOn (id : ℝ → ℝ) (Icc (-1) 0) ν := continuous_id.integrableOn_Icc
  have hg : Integrable g ν :=
    (integrable_indicator_iff measurableSet_Ioo).2 (hb.mono_set Ioo_subset_Icc_self)
  have hn : ∀ᵐ y ∂ν, y < 0 := (ae_iff).2 (by
    simpa only [not_lt, Set.Ici] using hneg)
  have hgj : ∀ᵐ y ∂ν, g y = if -1 < y then y else 0 :=
    hn.mono fun y hy => by simp [g, Set.indicator, mem_Ioo, hy]
  refine ⟨?_, ?_⟩
  · intro ξ hi
    let z : ℂ := (ξ : ℂ) * Complex.I
    have heq : levyCompensatedIntegrand ξ =ᵐ[ν] fun y =>
        Complex.exp ((ξ : ℂ) * y * Complex.I) - 1 - z * (g y : ℂ) := by
      filter_upwards [hn, hgj] with y hy hgy
      have hs : |y| < 1 ↔ -1 < y := by rw [abs_of_neg hy, neg_lt]
      by_cases h : -1 < y <;>
        simp [levyCompensatedIntegrand, z, hs, h, hgy, mul_comm, mul_left_comm, mul_assoc]
    have h : (∫ x, (↑(g x) : ℂ) ∂ν) = (↑(∫ x, g x ∂ν) : ℂ) :=
      integral_ofReal (𝕜 := ℂ) (μ := ν) (f := g)
    rw [integral_congr_ae heq,
      integral_sub hi (by simpa using (Complex.ofRealCLM.integrable_comp hg).const_mul z),
      integral_const_mul,
      h]
  · intro β hi
    have heq : (fun y => Real.exp (β * y) - 1 - (if -1 < y then β * y else 0)) =ᵐ[ν]
        fun y => Real.exp (β * y) - 1 - β * g y :=
      hgj.mono fun y hy => by by_cases h : -1 < y <;> simp [h, hy]
    rw [integral_congr_ae heq, integral_sub hi (hg.const_mul β), integral_const_mul]
