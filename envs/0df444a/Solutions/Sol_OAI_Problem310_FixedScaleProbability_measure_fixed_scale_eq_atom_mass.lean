-- Prove2me | solution 1 for OAI.Problem310.FixedScaleProbability.measure_fixed_scale_eq_atom_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:38:25.048517+00:00
-- url     : https://prove2.me/submissions/34485f15-4cde-43ed-8167-d475ceb27078

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FixedScaleProbability.lean:L99-L125
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FixedScaleProbability.measure_fixed_scale_eq_atom_mass. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_AdaptiveLabels_measure_injective_constraints
import Theorems.Thm_OAI_Problem310_FixedScaleProbability_measure_fixed_scale_on_center_atom

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FixedScaleProbability ----
namespace OAI

universe u_A u_I u_K u_C u_S u_T

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FixedScaleProbability

/-- The preceding identity with the actual center-atom mass as coefficient,
ready for summation over center exposure values. -/
theorem measure_fixed_scale_eq_atom_mass
    {C : Type u_C} {I : Type u_I} {S : Type u_S} {T : Type u_T} [Fintype C] [Fintype I] [Fintype S] [Fintype T]
    (νs νt : Measure Bool) [IsProbabilityMeasure νs] [IsProbabilityMeasure νt]
    (hfalse : νs {false} = 1 / 2) (htrue : νs {true} = 1 / 2)
    (center : C → S) (fresh : I → S)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → Bool)
    (addr : (S → Bool) → I → T) (haddr : ∀ a, Function.Injective (addr a))
    (p : ℝ) (hp : p ≤ 1) (hterminal : νt {false} = ENNReal.ofReal (1 - p)) :
    ((Measure.pi (fun _ : S => νs)).prod (Measure.pi (fun _ : T => νt)))
      {z : (S → Bool) × (T → Bool) |
        (∀ c, z.1 (center c) = value c) ∧
        ∀ i, z.1 (fresh i) = true → z.2 (addr z.1 i) = false} =
      (Measure.pi (fun _ : S => νs)) {a | ∀ c, a (center c) = value c} *
        (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  rw [measure_fixed_scale_on_center_atom νs νt hfalse htrue
    center fresh hinj value addr haddr p hp hterminal]
  congr 1
  have hcenter : Function.Injective center := by
    intro c d h
    exact Sum.inl.inj (hinj (show Sum.elim center fresh (Sum.inl c) =
      Sum.elim center fresh (Sum.inl d) from h))
  symm
  simpa only [Set.mem_singleton_iff] using
    AdaptiveLabels.measure_injective_constraints νs center hcenter
      (fun c => {value c}) (fun c => measurableSet_singleton (value c))

end Problem310.FixedScaleProbability

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FixedScaleProbability
open MeasureTheory ProbabilityTheory
open scoped BigOperators


theorem solution.{u_I,u_C,u_S,u_T} : type_of% @_root_.OAI.Problem310.FixedScaleProbability.measure_fixed_scale_eq_atom_mass.{u_I,u_C,u_S,u_T} := @_root_.OAI.Problem310.FixedScaleProbability.measure_fixed_scale_eq_atom_mass.{u_I,u_C,u_S,u_T}
