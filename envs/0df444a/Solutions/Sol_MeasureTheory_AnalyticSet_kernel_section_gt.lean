-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.kernel_section_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:50.931163+00:00
-- url     : https://prove2.me/submissions/bbf016ec-625e-4736-a5a6-a8f39dfa84c7

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_cap_kernel_exists_bound
import Theorems.Thm_cap_kernel_le_of_bound
import Theorems.Thm_cap_measurable_layer

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
open ProbabilityTheory
variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {A : Set (X × Y)} (hA : AnalyticSet A)
    (κ : Kernel X Y) [IsFiniteKernel κ] (c : ℝ≥0∞) :
    AnalyticSet {x | c < κ x (Prod.mk x ⁻¹' A)} := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨π, hπ_cont, hπ_range⟩
  · have hempty : {x : X | c < κ x (Prod.mk x ⁻¹' (∅ : Set (X × Y)))} = ∅ := by
      ext x; simp
    rw [hempty]; exact analyticSet_empty
  subst hπ_range
  have main : {x | c < κ x (Prod.mk x ⁻¹' range π)}
      = ⋃ q : ℚ, Prod.fst ''
          {p : X × (ℕ → ℕ) | c < (Real.toNNReal q : ℝ≥0∞) ∧
            ∀ n, (Real.toNNReal q : ℝ≥0∞)
              < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_image, Prod.exists]
    constructor
    · intro hc
      obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hc
      obtain ⟨β, hβ⟩ := cap_kernel_exists_bound hπ_cont κ hq2
      exact ⟨q, x, β, ⟨hq1, hβ⟩, rfl⟩
    · rintro ⟨q, x', β, ⟨hq1, hβ⟩, rfl⟩
      exact lt_of_lt_of_le hq1 (cap_kernel_le_of_bound hπ_cont κ hβ)
  rw [main]
  refine AnalyticSet.iUnion fun q => ?_
  refine AnalyticSet.image_of_continuous ?_ continuous_fst
  refine MeasurableSet.analyticSet ?_
  by_cases hcq : c < (Real.toNNReal q : ℝ≥0∞)
  · have heq : {p : X × (ℕ → ℕ) | c < (Real.toNNReal q : ℝ≥0∞) ∧
        ∀ n, (Real.toNNReal q : ℝ≥0∞)
          < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)}
        = ⋂ n, {p : X × (ℕ → ℕ) | (Real.toNNReal q : ℝ≥0∞)
            < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by
      ext p; simp [hcq]
    rw [heq]
    exact MeasurableSet.iInter fun n => cap_measurable_layer π κ _ n
  · have heq : {p : X × (ℕ → ℕ) | c < (Real.toNNReal q : ℝ≥0∞) ∧
        ∀ n, (Real.toNNReal q : ℝ≥0∞)
          < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} = ∅ := by
      ext p; simp [hcq]
    rw [heq]
    exact MeasurableSet.empty
end MeasureTheory.AnalyticSet
