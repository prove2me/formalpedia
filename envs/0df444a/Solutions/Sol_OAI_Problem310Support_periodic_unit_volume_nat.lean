-- Prove2me | solution 1 for OAI.Problem310Support.periodic_unit_volume_nat
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:01:30.731294+00:00
-- url     : https://prove2.me/submissions/c73c573a-4752-48a4-a28b-de0828d8dadf

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/PeriodicMeasure.lean:L21-L37
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.periodic_unit_volume_nat. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Iterating a period-one membership equivalence. -/
theorem periodic_mem_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) (x : ℝ) :
    x + (n : ℝ) ∈ H ↔ x ∈ H := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
      (hH (x + (n : ℝ))).trans ih

/-- Integer translates of a unit cell have the same occupied volume. -/
theorem periodic_unit_volume_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) =
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hset : (fun x : ℝ => x + (n : ℝ)) ⁻¹'
      (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) = H ∩ Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Icc, periodic_mem_nat hH]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
  simpa only [hset] using
    (measure_preimage_add_right volume (n : ℝ)
      (H ∩ Icc (n : ℝ) ((n : ℝ) + 1))).symm

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.periodic_unit_volume_nat := @_root_.OAI.Problem310Support.periodic_unit_volume_nat
