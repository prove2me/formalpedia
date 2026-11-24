-- Prove2me | solution 1 for MeasureTheory.exists_isCompact_disjoint_of_null
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:40.544159+00:00
-- url     : https://prove2.me/submissions/07c93983-c931-4f7c-a281-13f486b8b6b1

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {G : Set (ℕ → Bool)} (hG : cantorMeasure G = 0) :
    ∃ K : Set (ℕ → Bool), IsCompact K ∧ cantorMeasure K ≠ 0 ∧ Disjoint K G := by
  obtain ⟨U, hGU, hU, hμU⟩ := G.exists_isOpen_le_add cantorMeasure (ε := 2⁻¹) (by simp)
  refine ⟨Uᶜ, hU.isClosed_compl.isCompact, fun h0 ↦ ?_,
    disjoint_compl_left.mono_right hGU⟩
  have h1 : cantorMeasure U = 1 := by
    have := measure_add_measure_compl (μ := cantorMeasure) hU.measurableSet
    rwa [h0, add_zero, measure_univ] at this
  rw [hG, zero_add, h1] at hμU
  exact absurd hμU (by simp)
end MeasureTheory
