-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.nullMeasurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:54.795054+00:00
-- url     : https://prove2.me/submissions/233867e7-0359-4107-81b8-83d17bbc828d

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_MeasureTheory_AnalyticSet_measure_eq_iSup_isCompact

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ := by
  -- inner approximation by compacts, within 1/(k+1)
  have key : ∀ k : ℕ, ∃ K : Set X,
      IsCompact K ∧ K ⊆ A ∧ μ A ≤ μ K + ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro k
    by_cases h0 : μ A = 0
    · exact ⟨∅, isCompact_empty, empty_subset A, by simp [h0]⟩
    have hε : ((k : ℝ≥0∞) + 1)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (by finiteness)
    have hlt : μ A - ((k : ℝ≥0∞) + 1)⁻¹
        < ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K :=
      lt_of_lt_of_le (ENNReal.sub_lt_self (measure_ne_top μ A) h0 hε)
        (le_of_eq (hA.measure_eq_iSup_isCompact μ))
    obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hcpt, hK2⟩ := lt_iSup_iff.mp hK
    obtain ⟨hsub, hK3⟩ := lt_iSup_iff.mp hK2
    exact ⟨K, hcpt, hsub, tsub_le_iff_right.mp hK3.le⟩
  choose K hcpt hsub hge using key
  -- B = ⋃ K k is a Borel subset of A of full outer measure
  have hBmeas : MeasurableSet (⋃ k, K k) :=
    MeasurableSet.iUnion fun k => (hcpt k).isClosed.measurableSet
  have hBsub : (⋃ k, K k) ⊆ A := iUnion_subset hsub
  have hBeq : μ (⋃ k, K k) = μ A := by
    refine le_antisymm (measure_mono hBsub) ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt
      (show (ε : ℝ≥0∞) ≠ 0 from by exact_mod_cast hε.ne')
    have hk1 : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) :=
      le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.mpr le_self_add) hk)
    calc μ A ≤ μ (K k) + ((k : ℝ≥0∞) + 1)⁻¹ := hge k
      _ ≤ μ (⋃ j, K j) + (ε : ℝ≥0∞) := by
          gcongr
          exact subset_iUnion K k
  -- measurable hull H ⊇ A; then A \ B ⊆ H \ B is null
  obtain ⟨H, hAH, hHmeas, hHeq⟩ := exists_measurable_superset μ A
  have hnull : μ (H \ ⋃ k, K k) = 0 := by
    rw [measure_sdiff (hBsub.trans hAH) hBmeas.nullMeasurableSet
      (measure_ne_top μ _), hHeq, hBeq]
    exact tsub_self _
  have hABnull : μ (A \ ⋃ k, K k) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hAH) hnull
  rw [← union_sdiff_cancel hBsub]
  exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hABnull)
end MeasureTheory.AnalyticSet
