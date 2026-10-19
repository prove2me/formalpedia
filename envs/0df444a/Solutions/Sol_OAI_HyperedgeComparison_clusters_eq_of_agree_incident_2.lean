-- Prove2me | solution 2 for OAI.HyperedgeComparison.clusters_eq_of_agree_incident
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:39:18.139923+00:00
-- url     : https://prove2.me/submissions/67b1df1f-b464-4bd6-94d1-e4dceb7956b5

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L134-L165
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.clusters_eq_of_agree_incident. The node keeps its source
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

/-- Changing bits on hyperedges disjoint from C(S) cannot change C(S).
This is the key measurability assertion required for exact-cluster conditioning. -/
theorem clusters_eq_of_agree_incident {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V}
    (hagree : ∀ e, ¬ Disjoint (H e) (clusters H ω D S) → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  have hnew : clusters H ω' D S ⊆ clusters H ω D S := by
    rintro y ⟨x, hx, hy⟩
    have hr : ∀ z, Connected H ω' D x z → Connected H ω D x z := by
      intro z hz
      induction hz with
      | refl => exact .refl
      | @tail a b _ hab ia =>
        obtain ⟨e, he, hd, ha, hb⟩ := hab
        have hi : ¬ Disjoint (H e) (clusters H ω D S) := by
          intro h
          exact Set.disjoint_left.mp h ha ⟨x, hx, ia⟩
        exact ia.tail ⟨e, (hagree e hi) ▸ he, hd, ha, hb⟩
    exact ⟨x, hx, hr y hy⟩
  apply Set.Subset.antisymm hnew
  rintro y ⟨x, hx, hy⟩
  have hr : ∀ z, Connected H ω D x z → Connected H ω' D x z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | @tail a b hxa hab ia =>
      obtain ⟨e, he, hd, ha, hb⟩ := hab
      have hi : ¬ Disjoint (H e) (clusters H ω D S) := by
        intro h
        exact Set.disjoint_left.mp h ha ⟨x, hx, hxa⟩
      exact ia.tail ⟨e, (hagree e hi).trans he, hd, ha, hb⟩
  exact ⟨x, hx, hr y hy⟩

section FiniteLaw
variable [Fintype E]

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.clusters_eq_of_agree_incident.{uE,uV} := @_root_.OAI.HyperedgeComparison.clusters_eq_of_agree_incident.{uE,uV}
