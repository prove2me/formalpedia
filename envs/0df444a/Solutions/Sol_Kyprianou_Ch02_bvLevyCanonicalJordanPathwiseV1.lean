-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:16:00.808871+00:00
-- url     : https://prove2.me/submissions/6cf30554-6d47-494f-92fb-67fd9ec5936a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    (∀ᵐ ω ∂P, Monotone (fun t => Spos t ω)) ∧
    (∀ᵐ ω ∂P, Monotone (fun t => Sneg t ω)) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = Spos t ω - Sneg t ω) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hBV] with ω hω
    intro a b hab
    have h := variationOnFromTo.add_self_monotoneOn hω
      (Set.mem_univ (0 : ℝ≥0)) (Set.mem_univ a) (Set.mem_univ b) hab
    exact div_le_div_of_nonneg_right h (by norm_num)
  · filter_upwards [hBV] with ω hω
    intro a b hab
    have h := variationOnFromTo.sub_self_monotoneOn hω
      (Set.mem_univ (0 : ℝ≥0)) (Set.mem_univ a) (Set.mem_univ b) hab
    exact div_le_div_of_nonneg_right h (by norm_num)
  · exact Filter.Eventually.of_forall (fun ω t => by ring)
