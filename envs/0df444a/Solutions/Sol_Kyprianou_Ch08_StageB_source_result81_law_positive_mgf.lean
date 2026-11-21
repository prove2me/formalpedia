-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_law_positive_mgf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:02:55.35219+00:00
-- url     : https://prove2.me/submissions/c3a52ff5-88a1-48e8-9bfa-e1aa1ea75d3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_weak_moment_transfer
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_triplet_finite_jump_approximation
import Mathlib.MeasureTheory.Measure.LevyConvergence
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (t : ℝ≥0) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun ω => Real.exp (β * D.X t ω)) P ∧
      (∫ ω, Real.exp (β * D.X t ω) ∂P) =
        Real.exp ((t : ℝ) *
          tripletLaplace (-D.triplet.drift) D.gaussianCoefficient D.triplet.levyMeasure β) := by
  have hX : AEMeasurable (D.X t) P := by
    have hi := (D.levy.stationary_increments 0 t).aemeasurable_snd
    change AEMeasurable (fun ω => D.X t ω - D.X 0 ω) P at hi
    simpa only [D.levy.start_zero, sub_zero] using hi
  let μ : ProbabilityMeasure ℝ := ⟨P.map (D.X t), Measure.isProbabilityMeasure_map hX⟩
  obtain ⟨μs, hchar, hmoment⟩ := source_result81_triplet_finite_jump_approximation
    D.triplet D.negativeJumps D.gaussianCoefficient D.gaussianVarianceMatch t
  have hweak : Tendsto μs atTop (nhds μ) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro ξ
    change Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop
      (nhds (charFun (P.map (D.X t)) ξ))
    rw [D.characteristic]
    exact hchar ξ
  let f : ℝ → ℝ := fun x => Real.exp (β * x)
  let L (b : ℝ) := Real.exp ((t : ℝ) *
    tripletLaplace (-D.triplet.drift) D.gaussianCoefficient D.triplet.levyMeasure b)
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨hint, hlim⟩ := hmoment β hβ
  obtain ⟨hint₂, hlim₂⟩ := hmoment (2 * β) (by positivity)
  have hsq : ∀ᶠ n in atTop, Integrable (fun x => f x ^ 2) (μs n : Measure ℝ) ∧
      (∫ x, f x ^ 2 ∂(μs n : Measure ℝ)) ≤ L (2 * β) + 1 := by
    have heq : (fun x => f x ^ 2) = (fun x => Real.exp ((2 * β) * x)) := by
      funext x
      dsimp [f]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact (hlim₂.eventually_le_const (lt_add_of_pos_right (L (2 * β)) zero_lt_one)).mono
      (fun n hn => ⟨hint₂ n, hn⟩)
  obtain ⟨hi, he⟩ := source_result81_weak_moment_transfer μs μ hweak f hf
    (fun x => (Real.exp_pos (β * x)).le) hint (L (2 * β) + 1) (L β) hsq hlim
  change Integrable f (P.map (D.X t)) at hi
  change (∫ x, f x ∂P.map (D.X t)) = L β at he
  exact ⟨hi.comp_aemeasurable hX, (integral_map hX hi.aestronglyMeasurable).symm.trans he⟩
