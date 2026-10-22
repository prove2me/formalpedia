-- Prove2me | solution 1 for GeomDL.Blueprint.linear_invariant_eq_comp_average
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T15:59:56.175259+00:00
-- url     : https://prove2.me/submissions/b3379a1d-b700-404a-8997-37228e072340

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open MeasureTheory GeomDL.Blueprint

theorem solution {G Ω Y : Type*} [Group G] [MulAction G Ω] [Fintype Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [MeasurableInv G] [MeasurableSMul G Ω]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (f : (Ω → ℝ) →ₗ[ℝ] Y) (hf : IsInvariant (G := G) f) (x : Ω → ℝ) :
    f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (act g x) ∂μ ∧
    f x = f (groupAverage μ x) := by
  have ht : (μ Set.univ).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨by simpa [Measure.measure_univ_eq_zero] using hμ, measure_ne_top μ _⟩
  have h1 : f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (act g x) ∂μ := by
    simp_rw [hf _ x]
    rw [integral_const, smul_smul, measureReal_def, inv_mul_cancel₀ ht, one_smul]
  refine ⟨h1, ?_⟩
  let fc : (Ω → ℝ) →L[ℝ] Y := LinearMap.toContinuousLinearMap f
  have hmeas : Measurable (fun g : G => act g x) := by
    apply measurable_pi_lambda
    intro u
    exact (measurable_of_countable x).comp ((measurable_smul_const u).comp measurable_inv)
  have hint : Integrable (fun g : G => act g x) μ := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable ‖x‖ (Filter.Eventually.of_forall ?_)
    intro g
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 ?_
    intro u
    exact norm_le_pi_norm x _
  have hcomm : f (∫ g, act g x ∂μ) = ∫ g, f (act g x) ∂μ := by
    have := fc.integral_comp_comm hint
    simpa [fc] using this.symm
  rw [groupAverage, map_smul, hcomm, ← h1]
