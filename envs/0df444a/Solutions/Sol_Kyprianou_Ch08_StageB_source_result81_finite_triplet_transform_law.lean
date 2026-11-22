-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_finite_triplet_transform_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:21:17.76919+00:00
-- url     : https://prove2.me/submissions/5d0a476f-e7ce-4ef3-abe4-1a5eaad5a694

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_negative_jump_transforms
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_finite_compensator_shift
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hneg : ν (Ici (0 : ℝ)) = 0)
    (b σ : ℝ) (v t : ℝ≥0) (hσ : σ ^ 2 = (v : ℝ)) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, charFun (μ : Measure ℝ) ξ =
        Complex.exp (((t : ℝ) : ℂ) * (Complex.I * ((b * ξ : ℝ) : ℂ) -
          (((v : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) + ∫ y, levyCompensatedIntegrand ξ y ∂ν))) ∧
      (∀ β : ℝ, 0 ≤ β →
        Integrable (fun x => Real.exp (β * x)) (μ : Measure ℝ) ∧
        (∫ x, Real.exp (β * x) ∂(μ : Measure ℝ)) =
          Real.exp ((t : ℝ) * tripletLaplace (-b) σ ν β)) := by
  let C : ℝ := ∫ y, (Ioo (-1 : ℝ) 0).indicator id y ∂ν
  let G := gaussianReal ((t : ℝ) * (b - C)) (t * v)
  obtain ⟨hc, hr⟩ := source_result81_finite_compensator_shift ν hneg
  obtain ⟨J, hchar, hreal⟩ := source_result81_finite_negative_jump_transforms ν hneg t
  refine ⟨⟨G.conv (J : Measure ℝ), inferInstance⟩, ?_, ?_⟩
  · intro ξ
    change charFun (G.conv (J : Measure ℝ)) ξ = _
    rw [charFun_conv, charFun_gaussianReal, (hchar ξ).2, ← Complex.exp_add, hc ξ (hchar ξ).1]
    congr 1
    dsimp [G, C]
    push_cast
    ring
  · intro β hβ
    let F (x : ℝ) := Real.exp (β * x)
    have hadd (x y : ℝ) : F (x + y) = F x * F y := by simp [F, mul_add, Real.exp_add]
    obtain ⟨hν, hJ, hJexp⟩ := hreal β hβ
    have hG : Integrable F G := integrable_exp_mul_gaussianReal β
    have hi : Integrable F (G.conv (J : Measure ℝ)) := by
      change Integrable F ((G.prod (J : Measure ℝ)).map fun p => p.1 + p.2)
      rw [integrable_map_measure (by fun_prop) (by fun_prop)]
      change Integrable (fun p : ℝ × ℝ => F (p.1 + p.2)) (G.prod (J : Measure ℝ))
      simp_rw [hadd]
      exact hG.mul_prod hJ
    have hGexp : (∫ x, F x ∂G) = Real.exp
        ((t : ℝ) * (b - C) * β + (((t * v : ℝ≥0) : ℝ)) * β ^ 2 / 2) := by
      have hmap : G.map (id : ℝ → ℝ) = gaussianReal ((t : ℝ) * (b - C)) (t * v) := by simp [G]
      simpa only [mgf, id_eq, F] using mgf_gaussianReal hmap β
    refine ⟨hi, ?_⟩
    change (∫ x, F x ∂(G.conv (J : Measure ℝ))) = _
    rw [integral_conv hi]
    simp_rw [hadd, integral_const_mul]
    rw [integral_mul_const, hGexp, hJexp, ← Real.exp_add, tripletLaplace, hσ, hr β hν]
    congr 1
    push_cast
    ring
