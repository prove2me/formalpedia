-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:02.639306+00:00
-- url     : https://prove2.me/submissions/f7eee38f-5b15-4cdc-b1a4-6a9d86305892

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Theorems.Thm_MeasureTheory_AnalyticSet_compactCap_eq
public import Theorems.Thm_MeasureTheory_MeasurableSet_compactCap_eq


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
namespace MeasureTheory.AnalyticSet
theorem _root_.solution
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ μ.real s < μ.real K + ε := by
  intro ε hε
  have hcap := hs.compactCap_eq (μ := μ)
  have hfin : μ s ≠ ⊤ := measure_ne_top μ s
  have hε_ennreal : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hε_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Get K with μ s < μ K + ε in ENNReal
  -- By contradiction: if all r ∈ S satisfy r + ε ≤ μ s, then sSup S + ε ≤ μ s,
  -- but sSup S = μ s, contradiction.
  have hmem : ∃ r ∈ {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K},
      μ s < r + ENNReal.ofReal ε := by
    by_contra h
    push Not at h
    -- Every r in S satisfies r + ε ≤ μ s, hence r ≤ μ s - ε
    have hbound : sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} ≤ μ s - ENNReal.ofReal ε := by
      apply sSup_le
      intro r hr
      exact ENNReal.le_sub_of_add_le_right hε_ne_top (h r hr)
    -- But sSup S = compactCap μ s = μ s, so μ s ≤ μ s - ε
    have : MeasureTheory.compactCap μ s = sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} := rfl
    rw [← this, hcap] at hbound
    -- μ s - ε < μ s when μ s ≠ 0 and ε ≠ 0 and μ s ≠ ⊤
    by_cases hμs : μ s = 0
    · -- When μ s = 0, use K = ∅: μ ∅ = 0 = μ s, so μ s < μ ∅ + ε iff 0 < ε, which is true.
      -- So the by_contra path is impossible when μ s = 0: h says ∀ r ∈ S, r + ε ≤ 0 = μ s,
      -- but 0 ∈ S (via K = ∅) and 0 + ε = ε > 0 = μ s, contradiction.
      have hmem : (0 : ENNReal) ∈ {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
        ⟨∅, isCompact_empty, Set.empty_subset _, by simp⟩
      have hle := h 0 hmem
      rw [hμs, zero_add] at hle
      exact absurd hle (not_le.mpr hε_ennreal)
    · exact absurd hbound (not_le.mpr (ENNReal.sub_lt_self hfin hμs hε_ennreal.ne'))
  obtain ⟨r, ⟨K, hKc, hKs, rfl⟩, hlt⟩ := hmem
  refine ⟨K, hKc, hKs, ?_⟩
  have hKfin : μ K ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hKs)
  rw [Measure.real, Measure.real]
  calc (μ s).toReal < (μ K + ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal hfin (ENNReal.add_ne_top.mpr ⟨hKfin, hε_ne_top⟩)).mpr hlt
    _ = (μ K).toReal + ε := by
        rw [ENNReal.toReal_add hKfin hε_ne_top, ENNReal.toReal_ofReal hε.le]
end MeasureTheory.AnalyticSet
