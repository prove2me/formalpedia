-- Prove2me | solution 2 for OAI.InfiniteConditioning.measure_select
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:34:36.547794+00:00
-- url     : https://prove2.me/submissions/afeaeef4-90e3-4b89-b6d2-889b91350c74

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Conditioning.lean:L143-L161
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteConditioning.measure_select. The node keeps its source
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
import Theorems.Thm_OAI_InfiniteConditioning_pattern_inter

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

theorem pattern_inter_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    (ProductCylinder.law p).real (pattern J ξ ∩ A) =
      (ProductCylinder.law p).real (pattern J ξ) *
        (ProductCylinder.law (fixedParameter p J ξ)).real A := by
  simp only [Measure.real_def,pattern_inter p J ξ A hA,ENNReal.toReal_mul]

omit [Countable E] in
theorem pattern_extend_iff (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left e.2] using h e e.2
  · intro h e he
    have hh := congrFun h ⟨e,he⟩
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left he] using hh

/-- Partition a finite reveal without conditioning on any unrevealed event. -/
theorem measure_select (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} =
      ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) *
        (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a) := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq,measureReal_iUnion_fintype]
  · exact Finset.sum_congr rfl (fun a _ => pattern_inter_real p J _ _ (hA a))
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (((pattern_extend_iff J a ω).mp ha.1).symm.trans
      ((pattern_extend_iff J b ω).mp hb.1))
  · intro a; exact (measurableSet_pattern _ _).inter (hA a)

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

-- ---- platform node ----
open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.InfiniteConditioning.measure_select := @_root_.OAI.InfiniteConditioning.measure_select
