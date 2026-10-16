-- Prove2me | solution 1 for OAI.Problem310.CenterExposure.map_fresh_restrict_center_atom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:27:56.631004+00:00
-- url     : https://prove2.me/submissions/190ab26c-45e5-47d8-947f-ec343420edf9

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/CenterExposure.lean:L79-L109
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.CenterExposure.map_fresh_restrict_center_atom. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Theorems.Thm_OAI_Problem310_AdaptiveLabels_measure_injective_constraints

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

/-- Center constraints do not alter the product law of distinct fresh
coordinates. This unnormalized identity avoids all conditional-expectation
bookkeeping and applies to arbitrary coordinate label spaces. -/
theorem measure_center_and_fresh
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K]
    [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh))
    (s : C → Set B) (t : I → Set B)
    (hs : ∀ c, MeasurableSet (s c)) (ht : ∀ i, MeasurableSet (t i)) :
    (Measure.pi (fun _ : K => ν))
      {ω | (∀ c, ω (center c) ∈ s c) ∧ (∀ i, ω (fresh i) ∈ t i)} =
      (∏ c, ν (s c)) * ∏ i, ν (t i) := by
  have h := AdaptiveLabels.measure_injective_constraints ν
    (Sum.elim center fresh) hinj (Sum.elim s t) (by
      intro k
      cases k with
      | inl c => exact hs c
      | inr i => exact ht i)
  simpa only [Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_sum_type] using h

/-- Specialization to an atom specifying all exposed center entries. -/
theorem measure_center_atom_and_fresh
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh))
    (value : C → B) (t : I → Set B)
    (ht : ∀ i, MeasurableSet (t i)) :
    (Measure.pi (fun _ : K => ν))
      {ω | (∀ c, ω (center c) = value c) ∧ (∀ i, ω (fresh i) ∈ t i)} =
      (∏ c, ν {value c}) * ∏ i, ν (t i) := by
  simpa only [Set.mem_singleton_iff] using
    measure_center_and_fresh ν center fresh hinj (fun c => {value c}) t
      (fun c => measurableSet_singleton (value c)) ht

/-- The whole fresh coordinate vector has its original product law after
restricting to a center atom, multiplied only by the atom's mass. This
form permits arbitrary fresh-vector events and moments, not just cylinders. -/
theorem map_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B) :
    Measure.map (fun ω : K → B => fun i => ω (fresh i))
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c}) =
      (∏ c, ν {value c}) • Measure.pi (fun _ : I => ν) := by
  have hg : Measurable (fun ω : K → B => fun i => ω (fresh i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (fresh i))
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply hg (measurableSet_singleton v),
    Measure.restrict_apply (hg (measurableSet_singleton v))]
  have heq :
      (fun ω : K → B => fun i => ω (fresh i)) ⁻¹' {v} ∩
        {ω | ∀ c, ω (center c) = value c} =
      {ω : K → B | (∀ c, ω (center c) = value c) ∧
        (∀ i, ω (fresh i) ∈ ({v i} : Set B))} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, funext_iff]
    exact and_comm
  rw [heq, measure_center_atom_and_fresh ν center fresh hinj value
    (fun i => {v i}) (fun i => measurableSet_singleton (v i))]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_singleton]

end Problem310.CenterExposure

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.CenterExposure
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal


theorem solution.{u_C,u_I,u_K,u_B} : type_of% @_root_.OAI.Problem310.CenterExposure.map_fresh_restrict_center_atom.{u_C,u_I,u_K,u_B} := @_root_.OAI.Problem310.CenterExposure.map_fresh_restrict_center_atom.{u_C,u_I,u_K,u_B}
