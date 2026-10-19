-- Prove2me | solution 2 for OAI.FiniteAssociation.prob_forall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:16:47.746992+00:00
-- url     : https://prove2.me/submissions/0e8e0cb6-24be-46fe-985a-3ee0d8ba0ba8

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ProductCylinder.lean:L235-L249
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteAssociation.prob_forall. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Theorems.Thm_OAI_FiniteAssociation_increasing

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

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

/-- Harris association also holds for decreasing observables. -/
theorem decreasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Antitone f) (hg : Antitone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  have h := increasing p (fun ω => -f ω) (fun ω => -g ω) hf.neg hg.neg
  simpa only [mean,integral_neg,neg_mul_neg] using h

theorem prob_nonneg [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : 0 ≤ prob p P := integral_nonneg (by intro ω; dsimp; split_ifs <;> norm_num)

theorem indicator_antitone {P : (E → Bool) → Prop} (hP : Antitone P) :
    Antitone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω'
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Antitone P) (hQ : Antitone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := decreasing p _ _ (indicator_antitone hP) (indicator_antitone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]

/-- The finite-family decreasing-event Harris inequality used for 24 quarter-faces. -/
theorem prob_forall [Fintype E] {I : Type uI} (p : E → Set.Icc (0 : ℝ) 1)
    (s : Finset I) (P : I → (E → Bool) → Prop) (hP : ∀ i ∈ s, Antitone (P i)) :
    (∏ i ∈ s, prob p (P i)) ≤ prob p (fun ω => ∀ i ∈ s, P i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob,mean]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hs : ∀ j ∈ s, Antitone (P j) := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    have h := mul_le_mul_of_nonneg_left (ih hs) (prob_nonneg p (P i))
    refine h.trans ?_
    have hh := prob_and p (hP i (Finset.mem_insert_self i s))
      (fun ω ω' h h' j hj => hs j hj h (h' j hj))
    simpa only [Finset.mem_insert,forall_eq_or_imp] using hh

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- platform node ----
open OAI OAI.FiniteAssociation
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical


theorem solution.{uI,u} : type_of% @_root_.OAI.FiniteAssociation.prob_forall.{uI,u} := @_root_.OAI.FiniteAssociation.prob_forall.{uI,u}
