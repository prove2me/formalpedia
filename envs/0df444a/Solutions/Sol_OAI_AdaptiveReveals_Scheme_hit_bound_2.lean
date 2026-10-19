-- Prove2me | solution 2 for OAI.AdaptiveReveals.Scheme.hit_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:44:18.586667+00:00
-- url     : https://prove2.me/submissions/ffbd7863-bba4-44f8-b5dd-ae3c9c3cd1dd

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/AdaptiveReveals.lean:L80-L139
-- (upload_full_project.md Phase 4): solution for node OAI.AdaptiveReveals.Scheme.hit_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Theorems.Thm_OAI_InfiniteConditioning_measure_select

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uF

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem measurableSet_pattern (J : Finset E) (ξ : E → Bool) : MeasurableSet (pattern J ξ) := by
  simp only [pattern, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const))

omit [Countable E] in
theorem pattern_extend_iff (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left e.2] using h e e.2
  · intro h e he
    have hh := congrFun h ⟨e,he⟩
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left he] using hh

theorem sum_pattern_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) :
    ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) = 1 := by
  simpa only [Set.mem_univ,Set.ofPred_true,probReal_univ,mul_one] using
    (measure_select p J (fun _ => Set.univ) (fun _ => MeasurableSet.univ)).symm

theorem measurableSet_select (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    MeasurableSet {ω | ω ∈ A (J.restrict ω)} := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun a => (measurableSet_pattern _ _).inter (hA a))

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.AdaptiveReveals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uF

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

namespace Scheme
variable (P : Scheme E V S)

omit [Countable E] [DecidableEq V] in
theorem weight_nonneg (s : S) (a : P.reveal s → Bool) : 0 ≤ P.weight s a := measureReal_nonneg

omit [DecidableEq V] in
theorem weight_sum (s : S) : ∑ a : P.reveal s → Bool, P.weight s a = 1 :=
  sum_pattern_real _ _

theorem measurableSet_hit (n : ℕ) (s : S) (U : Finset V) : MeasurableSet (P.hit n s U) := by
  induction n generalizing s U with
  | zero => simp only [hit]; split_ifs <;> simp
  | succ n ih =>
    simp only [hit]
    split
    · split_ifs <;> simp
    · rename_i v hv
      apply measurableSet_select (P.reveal s)
        (fun a => {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})
      intro a
      by_cases h : v ∈ U → P.bad s a = true
      · convert ih (P.child s a) (U.erase v) using 1
        ext ω; exact and_iff_right h
      · simp only [h,false_and,Set.ofPred_false]; exact MeasurableSet.empty

/-- The only probabilistic hypotheses are the local bad probability and the
exact next-history product law.  Invalid zero-mass histories need no promise. -/
theorem hit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (n : ℕ) (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (P.hit n s U) ≤ f^U.card := by
  induction n generalizing s U with
  | zero =>
    by_cases hu : U = ∅
    · simp [hit,hu,probReal_univ]
    · simp only [hit,ite_eq_right hu,measureReal_empty]
      exact pow_nonneg hf _
  | succ n ih =>
    cases hv : P.vertex s with
    | none =>
      by_cases hu : U = ∅
      · simp [hit,hv,hu,probReal_univ]
      · simp only [hit,hv,ite_eq_right hu,measureReal_empty]
        exact pow_nonneg hf _
    | some v =>
      let A : (P.reveal s → Bool) → Set (E → Bool) :=
        fun a => {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)}
      have hA (a) : MeasurableSet (A a) := by
        by_cases ha : v ∈ U → P.bad s a = true
        · convert P.measurableSet_hit n (P.child s a) (U.erase v) using 1
          ext ω; exact and_iff_right ha
        · simp only [A,ha,false_and,Set.ofPred_false]; exact MeasurableSet.empty
      simp only [hit,hv]
      change (ProductCylinder.law (P.parameter s)).real
        {ω | ω ∈ A ((P.reveal s).restrict ω)} ≤ _
      rw [measure_select _ _ A hA]
      change (∑ a, P.weight s a *
        (ProductCylinder.law (fixedParameter (P.parameter s) (P.reveal s)
          (ProductCylinder.extend (P.reveal s) a))).real (A a)) ≤ _
      simp_rw [←P.parameter_child]
      have hterm (a) : P.weight s a *
          (ProductCylinder.law (P.parameter (P.child s a))).real (A a) ≤
          (if v ∈ U → P.bad s a = true then P.weight s a else 0) * f^(U.erase v).card := by
        by_cases hw : P.weight s a = 0
        · simp [hw]
        have hpos : 0 < P.weight s a := lt_of_le_of_ne (P.weight_nonneg s a) (Ne.symm hw)
        by_cases ha : v ∈ U → P.bad s a = true
        · have heqA : A a = P.hit n (P.child s a) (U.erase v) := by
            ext ω; exact and_iff_right ha
          rw [heqA,ite_eq_left ha]
          exact mul_le_mul_of_nonneg_left (ih (P.child s a) (hchild s hs a hpos) (U.erase v))
            (P.weight_nonneg s a)
        · simp only [A,ha,false_and,Set.ofPred_false,measureReal_empty,ite_false,mul_zero,zero_mul]
          exact le_rfl
      apply (Finset.sum_le_sum (fun a _ => hterm a)).trans
      rw [←Finset.sum_mul]
      by_cases hmem : v ∈ U
      · simp only [hmem,true_implies]
        change P.badMass s * f^(U.erase v).card ≤ f^U.card
        have hcard : (U.erase v).card + 1 = U.card := Finset.card_erase_add_one hmem
        rw [←hcard,pow_succ']
        exact mul_le_mul_of_nonneg_right (hbad s hs) (pow_nonneg hf _)
      · simp only [hmem,false_implies,ite_true,P.weight_sum,one_mul,Finset.erase_eq_of_notMem hmem]
        exact le_rfl

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

namespace History
end History
end InfiniteConditioning

end OAI

-- ---- platform node ----
open OAI OAI.AdaptiveReveals OAI.AdaptiveReveals.Scheme
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning


theorem solution : type_of% @_root_.OAI.AdaptiveReveals.Scheme.hit_bound := @_root_.OAI.AdaptiveReveals.Scheme.hit_bound
