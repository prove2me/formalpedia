-- Prove2me | solution 2 for OAI.InfiniteConditioning.select_probability_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:37:58.13114+00:00
-- url     : https://prove2.me/submissions/c50e1dc8-5f2c-4ed0-be4b-a77288b75001

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Conditioning.lean:L375-L402
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteConditioning.select_probability_lower. The node keeps its source
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
import Theorems.Thm_OAI_InfiniteConditioning_measure_select

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

/-- Exact lower bound after a selected reveal; null histories are included. -/
theorem select_probability_lower (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (P : (J → Bool) → Prop) (A : (J → Bool) → Set (E → Bool))
    (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, P a → b ≤
      (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a)) :
    b * (ProductCylinder.law p).real {ω | P (J.restrict ω)} ≤
      (ProductCylinder.law p).real {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} := by
  classical
  let B : (J → Bool) → Set (E → Bool) := fun a => if P a then Set.univ else ∅
  let C : (J → Bool) → Set (E → Bool) := fun a => if P a then A a else ∅
  have hPm : {ω | P (J.restrict ω)} = {ω | ω ∈ B (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [B,h]
  have hAm : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
      {ω | ω ∈ C (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [C,h]
  have hB (a) : MeasurableSet (B a) := by dsimp [B]; split_ifs <;> measurability
  have hC (a) : MeasurableSet (C a) := by dsimp [C]; split_ifs; exact hA a; exact MeasurableSet.empty
  rw [hPm,hAm,measure_select p J B hB,measure_select p J C hC,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P a
  · simp only [B,C,ha,ite_true,probReal_univ,mul_one]
    calc
      _ = (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a))*b := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb a ha) measureReal_nonneg
  · simp only [B,C,ha,ite_false,measureReal_empty,mul_zero]
    exact le_rfl

end InfiniteConditioning

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.InfiniteConditioning.select_probability_lower := @_root_.OAI.InfiniteConditioning.select_probability_lower
