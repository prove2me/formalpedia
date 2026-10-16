-- Prove2me | solution 2 for OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:43:16.629031+00:00
-- url     : https://prove2.me/submissions/02e1919e-ef8d-486c-9978-001baeea78fa

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExposureUnionBound.lean:L14-L50
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExposureUnionBound ----
namespace OAI

universe u_Ω u_A u_I

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem310.ExposureUnionBound

/-- Averaging conditional bounds over a finite exposure does not introduce a
factor for the number of possible exposure values. The event itself need not
be measurable, since the proof uses only outer-measure subadditivity. -/
theorem measure_le_of_finite_exposure
    {Ω : Type u_Ω} {A : Type u_A} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (hf : ∀ a, MeasurableSet {ω | f ω = a})
    (E : Set Ω) (good : Set A) (badBound goodBound : ENNReal)
    (hbad : μ {ω | f ω ∉ good} ≤ badBound)
    (hgood : ∀ a ∈ good,
      μ (E ∩ {ω | f ω = a}) ≤ goodBound * μ {ω | f ω = a}) :
    μ E ≤ badBound + goodBound := by
  classical
  let localEvent : A → Set Ω := fun a =>
    if a ∈ good then E ∩ {ω | f ω = a} else ∅
  have hcover : E ⊆ {ω | f ω ∉ good} ∪ ⋃ a, localEvent a := by
    intro ω hω
    by_cases hg : f ω ∈ good
    · right
      exact Set.mem_iUnion.mpr ⟨f ω, by simp [localEvent, hg, hω]⟩
    · exact Or.inl hg
  have hlocal (a : A) : μ (localEvent a) ≤ goodBound * μ {ω | f ω = a} := by
    by_cases ha : a ∈ good
    · simpa [localEvent, ha] using hgood a ha
    · simp [localEvent, ha]
  have hmass : (∑ a : A, μ {ω | f ω = a}) = 1 := by
    have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset A)
      (f := f) (fun a _ => hf a)
    simpa [Set.preimage] using h
  calc
    μ E ≤ μ ({ω | f ω ∉ good} ∪ ⋃ a, localEvent a) := measure_mono hcover
    _ ≤ μ {ω | f ω ∉ good} + μ (⋃ a, localEvent a) := measure_union_le _ _
    _ ≤ badBound + ∑ a : A, μ (localEvent a) :=
      add_le_add hbad (measure_iUnion_fintype_le μ localEvent)
    _ ≤ badBound + ∑ a : A, goodBound * μ {ω | f ω = a} :=
      add_le_add le_rfl (Finset.sum_le_sum fun a _ => hlocal a)
    _ = badBound + goodBound := by rw [← Finset.mul_sum, hmass, mul_one]

end Problem310.ExposureUnionBound

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.ExposureUnionBound
open MeasureTheory
open scoped BigOperators


theorem solution.{u_Ω,u_A} : type_of% @_root_.OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure.{u_Ω,u_A} := @_root_.OAI.Problem310.ExposureUnionBound.measure_le_of_finite_exposure.{u_Ω,u_A}
