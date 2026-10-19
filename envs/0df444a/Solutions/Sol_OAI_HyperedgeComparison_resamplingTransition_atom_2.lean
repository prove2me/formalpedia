-- Prove2me | solution 2 for OAI.HyperedgeComparison.resamplingTransition_atom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:01:32.71426+00:00
-- url     : https://prove2.me/submissions/22ae1fad-cfb7-4cfa-85ac-c717acdb5946

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L960-L986
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.resamplingTransition_atom. The node keeps its source
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

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

omit [Fintype E] in
/-- Closing every hyperedge isolates every node, in every deletion graph. -/
theorem cluster_all_closed (H : Hypergraph V E) (D : Set V) (s : V) :
    cluster H (fun _ => false) D s = {s} := by
  ext y
  constructor
  · intro hy
    change y = s
    induction hy with
    | refl => rfl
    | tail _ h _ => obtain ⟨e, he, _⟩ := h; simp at he
  · rintro rfl
    exact .refl

/-- A uniform positive atom, without discarding any zero-mass cluster states. -/
theorem resamplingTransition_atom [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (hs : s ∉ S)
    (U : ClusterDomain s S) :
    (law p).real {fun _ => false} ≤ (resamplingTransition H p s S).weight U
      ⟨{s}, ⟨by simp, by simpa using hs⟩⟩ := by
  classical
  let z : ClusterDomain s S := ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
  have hi : (∫ ω' : E → Bool, if ω' = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  have hj (ω : E → Bool) : (law p).real {fun _ => false} ≤
      ∫ ω', if nextState H s S U ω ω' = z then (1:ℝ) else 0 ∂law p := by
    rw [← hi]
    apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
    intro ω'
    by_cases hc : ω' = (fun _ => false)
    · subst ω'
      have heq : nextState H s S U ω (fun _ => false) = z := by
        apply Subtype.ext
        exact cluster_all_closed H _ s
      simp [heq]
    · simp only [hc, ite_false]
      split_ifs <;> norm_num
  have h := integral_mono (μ := law p) (Integrable.of_finite) (Integrable.of_finite) hj
  simpa [resamplingTransition, z] using h

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.resamplingTransition_atom.{uE,uV} := @_root_.OAI.HyperedgeComparison.resamplingTransition_atom.{uE,uV}
