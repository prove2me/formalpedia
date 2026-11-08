-- Prove2me | solution 1 for GeometricDL.GroupAverage.linear_invariant_factors_through_average
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:03:20.525205+00:00
-- url     : https://prove2.me/submissions/b6649ac7-3ec7-466d-a3ec-e880bb99dde1

import Mathlib
import Definitions.Def_GeometricDL_GroupAverage_IsGInvariant
import Definitions.Def_GeometricDL_GroupAverage_groupAverage
open MeasureTheory

set_option autoImplicit false

open MeasureTheory GeometricDL.GroupAverage in
theorem solution {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) [IsFiniteMeasure μ] [NeZero μ]
    (ρ : G →* (E →L[ℝ] E)) (f : E →L[ℝ] Y) (hf : IsGInvariant ρ f) :
    (∀ x : E, Integrable (fun g => ρ g x) μ →
        f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ ∧
        (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ =
          f ((μ Set.univ).toReal⁻¹ • ∫ g, ρ g x ∂μ)) ∧
    (∀ x : E, Integrable (fun g => ρ g x) μ → f x = f (groupAverage μ ρ x)) ∧
    (∀ x y : E, Integrable (fun g => ρ g x) μ → Integrable (fun g => ρ g y) μ →
        groupAverage μ ρ x = groupAverage μ ρ y → f x = f y) := by
  have hc : (μ Set.univ).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨Measure.measure_univ_ne_zero.mpr (NeZero.ne μ), measure_ne_top μ _⟩
  have P1 : ∀ x : E, Integrable (fun g => ρ g x) μ →
      f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ ∧
      (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ =
        f ((μ Set.univ).toReal⁻¹ • ∫ g, ρ g x ∂μ) := by
    intro x hx
    have hconst : ∫ g, f (ρ g x) ∂μ = (μ Set.univ).toReal • f x := by
      have : (fun g => f (ρ g x)) = fun _ => f x := funext fun g => hf g x
      rw [this, integral_const, measureReal_def]
    refine ⟨?_, ?_⟩
    · rw [hconst, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · rw [map_smul, ContinuousLinearMap.integral_comp_comm f hx]
  have P2 : ∀ x : E, Integrable (fun g => ρ g x) μ → f x = f (groupAverage μ ρ x) := by
    intro x hx
    obtain ⟨h1, h2⟩ := P1 x hx
    rw [groupAverage, ← h2, ← h1]
  refine ⟨P1, P2, ?_⟩
  intro x y hx hy hxy
  rw [P2 x hx, P2 y hy, hxy]
