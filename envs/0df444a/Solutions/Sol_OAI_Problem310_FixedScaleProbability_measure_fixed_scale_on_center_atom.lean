-- Prove2me | solution 1 for OAI.Problem310.FixedScaleProbability.measure_fixed_scale_on_center_atom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:36:31.40326+00:00
-- url     : https://prove2.me/submissions/5279d122-99d6-4643-aa8d-c93683408079

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/FixedScaleProbability.lean:L64-L97
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.FixedScaleProbability.measure_fixed_scale_on_center_atom. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_AdaptiveLabels_measure_adaptive_failures
import Theorems.Thm_OAI_Problem310_CenterExposure_map_fresh_restrict_center_atom
import Theorems.Thm_OAI_Problem310_SelectorMoment_lookup_fair_failure_moment

-- ---- from OAI.MeasureTheory.DyadicAvoidance.CenterExposure ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

universe u_C u_I u_K u_B

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Problem310.CenterExposure

/-- Any nonnegative measurable function of the fresh vector has the same
moment on a center atom, up to multiplication by the atom mass. -/
theorem lintegral_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B)
    (F : (I → B) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (fun i => ω (fresh i)) ∂
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c})) =
      (∏ c, ν {value c}) * ∫⁻ v, F v ∂Measure.pi (fun _ : I => ν) := by
  have hg : Measurable (fun ω : K → B => fun i => ω (fresh i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (fresh i))
  rw [← lintegral_map hF hg, map_fresh_restrict_center_atom ν center fresh hinj value,
    lintegral_smul_measure, smul_eq_mul]

end Problem310.CenterExposure

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.FixedScaleProbability ----
namespace OAI

universe u_A u_I u_K u_C u_S u_T

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.FixedScaleProbability

/-- Exposing selector coordinates does not change the adaptive terminal-label
calculation: first restrict the selector measure, then integrate out terminals. -/
theorem measure_exposed_adaptive_failures_eq_lintegral
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) [SFinite μ] (ν : Measure Bool) [IsProbabilityMeasure ν]
    (E : Set A) (addr : A → I → K)
    (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | z.1 ∈ E ∧
        ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a in E, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by
  have h := AdaptiveLabels.measure_adaptive_failures (μ.restrict E) ν
    addr hinj active hmeas
  rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply hmeas] at h
  convert h using 1
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_univ, and_true]
  exact and_comm

/-- Exact fixed-scale miss probability on a center-exposure atom. Selector
lookups are fair, fresh and pairwise distinct. Terminal addresses may depend
on all selectors, but their injectivity must hold for every selector outcome.
This is the finite-product version of the conditional estimate. -/
theorem measure_fixed_scale_on_center_atom
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
      (∏ c, νs {value c}) * (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  classical
  have hcalc := measure_exposed_adaptive_failures_eq_lintegral
    (Measure.pi (fun _ : S => νs)) νt
    {a | ∀ c, a (center c) = value c} addr haddr
    (fun a i => a (fresh i) = true) MeasurableSet.of_discrete
  simp only [Set.mem_ofPred_eq] at hcalc
  rw [hcalc]
  have hmoment := CenterExposure.lintegral_fresh_restrict_center_atom
    νs center fresh hinj value
    (fun v => (νt {false}) ^ (Finset.univ.filter (fun i => v i = true)).card)
    (measurable_of_countable _)
  rw [hmoment]
  congr 1
  rw [hterminal]
  simpa only [Fintype.card_subtype, id_eq] using
    SelectorMoment.lookup_fair_failure_moment νs hfalse htrue
      (id : I → I) Function.injective_id p hp

end Problem310.FixedScaleProbability

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.FixedScaleProbability
open MeasureTheory ProbabilityTheory
open scoped BigOperators


theorem solution.{u_I,u_C,u_S,u_T} : type_of% @_root_.OAI.Problem310.FixedScaleProbability.measure_fixed_scale_on_center_atom.{u_I,u_C,u_S,u_T} := @_root_.OAI.Problem310.FixedScaleProbability.measure_fixed_scale_on_center_atom.{u_I,u_C,u_S,u_T}
