-- Prove2me | solution 1 for OAI.Problem310.SelectorMoment.independent_boolean_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:33:08.057858+00:00
-- url     : https://prove2.me/submissions/785208d3-caf0-41ff-83ec-270dbfd596c7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/SelectorMoment.lean:L19-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.SelectorMoment.independent_boolean_moment. The node keeps its source
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

-- ---- from OAI.MeasureTheory.DyadicAvoidance.SelectorMoment ----
namespace OAI

universe u_I u_Ω u_K

noncomputable section

namespace Problem310.SelectorMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

lemma product_eq_pow_active {I : Type u_I} [Fintype I] [DecidableEq I]
    (a : I → Bool) (q : ℝ≥0∞) :
    (∏ i, if a i then q else 1) = q ^ Fintype.card {i // a i = true} := by
  simp [Finset.prod_ite, Fintype.card_subtype]

/-- Exponential moment of the number of active independent Boolean trials. -/
theorem independent_boolean_moment
    {Ω : Type u_Ω} {I : Type u_I} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Bool)
    (X : I → Ω → Bool) (hX : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (hmap : ∀ i, μ.map (X i) = ν)
    (q : ℝ≥0∞) :
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by
  classical
  let g : Bool → ℝ≥0∞ := fun b => if b then q else 1
  have hg : Measurable g := measurable_of_countable g
  have hind : iIndepFun (fun i => g ∘ X i) μ := hX.comp (fun _ => g) (fun _ => hg)
  have hsingle (i : I) : (∫⁻ ω, g (X i ω) ∂μ) = ν {false} + q * ν {true} := by
    rw [← lintegral_map hg (hXm i), hmap i, lintegral_fintype]
    simp [g, add_comm]
  calc
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
        ∫⁻ ω, ∏ i, g (X i ω) ∂μ := by
      apply lintegral_congr
      intro ω
      exact (product_eq_pow_active (fun i => X i ω) q).symm
    _ = ∏ i, ∫⁻ ω, g (X i ω) ∂μ := by
      exact lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
        (fun i => g ∘ X i) hind (fun i => hg.comp (hXm i))
    _ = (ν {false} + q * ν {true}) ^ Fintype.card I := by simp_rw [hsingle]; simp

end Problem310.SelectorMoment

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.SelectorMoment
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal


theorem solution.{u_I,u_Ω} : type_of% @_root_.OAI.Problem310.SelectorMoment.independent_boolean_moment.{u_I,u_Ω} := @_root_.OAI.Problem310.SelectorMoment.independent_boolean_moment.{u_I,u_Ω}
