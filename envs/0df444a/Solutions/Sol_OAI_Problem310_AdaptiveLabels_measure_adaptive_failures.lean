-- Prove2me | solution 1 for OAI.Problem310.AdaptiveLabels.measure_adaptive_failures
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:26:23.817311+00:00
-- url     : https://prove2.me/submissions/a42a9d66-f1a6-4364-b1c9-bdb140c550ce

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/AdaptiveLabels.lean:L54-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.AdaptiveLabels.measure_adaptive_failures. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Theorems.Thm_OAI_Problem310_AdaptiveLabels_measure_injective_constraints

-- ---- from OAI.MeasureTheory.DyadicAvoidance.AdaptiveLabels ----
namespace OAI

universe u_I u_K u_B u_A

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem310.AdaptiveLabels

/-- An address choice may depend arbitrarily on a separate selector outcome.
After fixing that outcome, injectivity is the only required terminal-table fact. -/
theorem measure_adaptive_constraints
    {A : Type u_A} {I : Type u_I} {K : Type u_K} {B : Type u_B} [MeasurableSpace A] [Fintype I] [Fintype K]
    [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (s : A → I → Set B) (hs : ∀ a i, MeasurableSet (s a i))
    (hmeas : MeasurableSet {z : A × (K → B) |
      ∀ i, z.2 (addr z.1 i) ∈ s z.1 i}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → B) | ∀ i, z.2 (addr z.1 i) ∈ s z.1 i} =
      ∫⁻ a, ∏ i, ν (s a i) ∂μ := by
  rw [Measure.prod_apply hmeas]
  apply lintegral_congr
  intro a
  exact measure_injective_constraints ν (addr a) (hinj a) (s a) (hs a)

/-- The conditional failure probability of adaptively addressed Boolean tests.
Only active tests impose a zero label; distinct active addresses suffice here
because we assume the stronger, routing-friendly injectivity of all addresses. -/
theorem measure_adaptive_failures
    {A : Type u_A} {I : Type u_I} {K : Type u_K} [MeasurableSpace A] [Fintype I] [Fintype K]
    (μ : Measure A) (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : A → I → K) (hinj : ∀ a, Function.Injective (addr a))
    (active : A → I → Prop) [∀ a i, Decidable (active a i)]
    (hmeas : MeasurableSet {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false}) :
    (μ.prod (Measure.pi (fun _ : K => ν)))
      {z : A × (K → Bool) | ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      ∫⁻ a, (ν {false}) ^ (Finset.univ.filter (active a)).card ∂μ := by
  classical
  let s : A → I → Set Bool := fun a i => if active a i then {false} else Set.univ
  have hset : {z : A × (K → Bool) |
      ∀ i, active z.1 i → z.2 (addr z.1 i) = false} =
      {z : A × (K → Bool) | ∀ i, z.2 (addr z.1 i) ∈ s z.1 i} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    apply forall_congr'
    intro i
    by_cases h : active z.1 i <;> simp [s, h]
  rw [hset] at hmeas ⊢
  rw [measure_adaptive_constraints μ ν addr hinj s
    (fun _ _ => MeasurableSet.of_discrete) hmeas]
  apply lintegral_congr
  intro a
  simp only [s, apply_ite, measure_univ]
  simp [Finset.prod_ite]

end Problem310.AdaptiveLabels

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.AdaptiveLabels
open MeasureTheory ProbabilityTheory
open scoped BigOperators


theorem solution.{u_I,u_K,u_A} : type_of% @_root_.OAI.Problem310.AdaptiveLabels.measure_adaptive_failures.{u_I,u_K,u_A} := @_root_.OAI.Problem310.AdaptiveLabels.measure_adaptive_failures.{u_I,u_K,u_A}
