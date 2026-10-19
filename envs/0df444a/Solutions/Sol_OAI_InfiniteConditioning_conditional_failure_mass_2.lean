-- Prove2me | solution 2 for OAI.InfiniteConditioning.conditional_failure_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:39:34.409291+00:00
-- url     : https://prove2.me/submissions/556d05c2-1fd1-49f1-9c40-d59b7877d1d0

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ConditionalQuality.lean:L25-L75
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteConditioning.conditional_failure_mass. The node keeps its source
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
import Theorems.Thm_OAI_InfiniteConditioning_measure_select

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem determinedBy_eq_extend {J : Finset E} {f : (E → Bool) → F}
    (hf : DeterminedBy J f) (ω : E → Bool) : f ω = f (extend J (J.restrict ω)) := by
  apply hf
  intro e he
  simp [extend,he,Finset.restrict]

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

omit [Countable E] in
theorem fixedParameter_congr (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    {ξ ξ' : E → Bool} (h : ∀ e ∈ J, ξ e = ξ' e) :
    fixedParameter p J ξ = fixedParameter p J ξ' := by
  funext e
  by_cases he : e ∈ J
  · simp only [fixedParameter,he,ite_true,h e he]
  · simp only [fixedParameter,he,ite_false]

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

-- ---- from OAI.Probability.CriticalZ3.ConditionalQuality ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem conditionalProbability_determined (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) :
    ProductCylinder.DeterminedBy J (conditionalProbability p J C) := by
  intro ω ω' h
  unfold conditionalProbability
  rw [fixedParameter_congr p J h]

/-- Reveal-wise tower/Markov bound, valid also for histories of zero mass. -/
theorem conditional_failure_mass (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ : ℝ} (_hδ : 0 ≤ δ) :
    δ * (ProductCylinder.law p).real
      {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤
    (ProductCylinder.law p).real (H ∩ Cᶜ) := by
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set (E → Bool) :=
    if ξ a ∈ H ∧ conditionalProbability p J C (ξ a) ≤ 1-δ then Set.univ else ∅
  let B (a : J → Bool) : Set (E → Bool) := if ξ a ∈ H then Cᶜ else ∅
  have hA (a) : MeasurableSet (A a) := by dsimp only [A]; split_ifs <;> measurability
  have hB (a) : MeasurableSet (B a) := by
    dsimp only [B]; split_ifs
    · exact hC.compl
    · exact MeasurableSet.empty
  have heA : {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    have hh := ProductCylinder.determinedBy_eq_extend hH ω
    have hc := ProductCylinder.determinedBy_eq_extend (conditionalProbability_determined p J C) ω
    change conditionalProbability p J C ω = conditionalProbability p J C (ξ (J.restrict ω)) at hc
    change (ω ∈ H) = (ξ (J.restrict ω) ∈ H) at hh
    simp only [Set.mem_ofPred_eq,A,hh,hc]
    split_ifs <;> simp_all
  have heB : H ∩ Cᶜ = {ω | ω ∈ B (J.restrict ω)} := by
    ext ω
    have hh := ProductCylinder.determinedBy_eq_extend hH ω
    change (ω ∈ H) = (ξ (J.restrict ω) ∈ H) at hh
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,B,hh]
    split_ifs <;> simp_all
  rw [heA,heB,measure_select p J A hA,measure_select p J B hB,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hcomp : (ProductCylinder.law (fixedParameter p J (ξ a))).real Cᶜ =
      1-conditionalProbability p J C (ξ a) := by
    simpa only [conditionalProbability,probReal_univ] using
      (measureReal_compl (μ := ProductCylinder.law (fixedParameter p J (ξ a))) hC)
  have hlocal : δ*(ProductCylinder.law (fixedParameter p J (ξ a))).real (A a) ≤
      (ProductCylinder.law (fixedParameter p J (ξ a))).real (B a) := by
    by_cases hha : ξ a ∈ H
    · simp only [A,B,hha,true_and,ite_true]
      split_ifs with hc
      · rw [probReal_univ,mul_one,hcomp]; linarith
      · rw [measureReal_empty,mul_zero]; exact measureReal_nonneg
    · simp only [A,B,hha,false_and,ite_false,measureReal_empty,mul_zero,le_refl]
  let hw := (ProductCylinder.law p).real (pattern J (ξ a))
  calc
    _ = hw*(δ*(ProductCylinder.law (fixedParameter p J (ξ a))).real (A a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlocal measureReal_nonneg

end InfiniteConditioning

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.InfiniteConditioning.conditional_failure_mass := @_root_.OAI.InfiniteConditioning.conditional_failure_mass
