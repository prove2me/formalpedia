-- Prove2me | solution 1 for Kyprianou.Ch02.realLawEqOfAETendstoApproximantsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:03:44.821999+00:00
-- url     : https://prove2.me/submissions/7691126b-d6c2-497e-b5af-cfc84ac27ea9

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Weak limits preserve equality of the laws of a.s.-convergent real approximants. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F G : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hX : Measurable X) (hY : Measurable Y)
    (hLaw : ∀ n, P.map (F n) = P.map (G n))
    (hFlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (X ω)))
    (hGlim : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (Y ω))) :
    P.map X = P.map Y := by
  haveI : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro q
  rw [integral_map hX.aemeasurable q.continuous.aestronglyMeasurable,
    integral_map hY.aemeasurable q.continuous.aestronglyMeasurable]
  have hFt : Tendsto (fun n => ∫ ω, q (F n ω) ∂P) atTop
      (𝓝 (∫ ω, q (X ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖q‖)
      (fun n => (q.continuous.measurable.comp (hF n)).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun ω => q.norm_coe_le_norm _) ?_
    exact hFlim.mono fun ω hω =>
      (q.continuous.tendsto (X ω)).comp hω
  have hGt : Tendsto (fun n => ∫ ω, q (G n ω) ∂P) atTop
      (𝓝 (∫ ω, q (Y ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖q‖)
      (fun n => (q.continuous.measurable.comp (hG n)).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun ω => q.norm_coe_le_norm _) ?_
    exact hGlim.mono fun ω hω =>
      (q.continuous.tendsto (Y ω)).comp hω
  have hEq (n : ℕ) :
      (∫ ω, q (F n ω) ∂P) = (∫ ω, q (G n ω) ∂P) := by
    calc
      (∫ ω, q (F n ω) ∂P) =
        ∫ x, q x ∂(P.map (F n)) :=
        (integral_map (hF n).aemeasurable
          q.continuous.aestronglyMeasurable).symm
      _ = ∫ x, q x ∂(P.map (G n)) := by rw [hLaw n]
      _ = ∫ ω, q (G n ω) ∂P :=
        integral_map (hG n).aemeasurable
          q.continuous.aestronglyMeasurable
  have hEqSeq : (fun n => ∫ ω, q (F n ω) ∂P) =
      (fun n => ∫ ω, q (G n ω) ∂P) := by
    funext n
    exact hEq n
  have hFt' : Tendsto (fun n => ∫ ω, q (G n ω) ∂P) atTop
      (𝓝 (∫ ω, q (X ω) ∂P)) := by
    simpa only [hEqSeq] using hFt
  exact tendsto_nhds_unique hFt' hGt
