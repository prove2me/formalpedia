-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.intersection_card_ge_le_subsets
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:50:18.734581+00:00
-- url     : https://prove2.me/submissions/12157001-c356-485d-8f4f-89ef7d296398

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/SpreadCounting.lean:L37-L67
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.intersection_card_ge_le_subsets. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction

-- ---- from OAI.Combinatorics.GraphThreshold.SpreadCounting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Exact intersection counting for a finite, weighted spread family.

No injectivity of the label map and no strict positivity of individual weights
is required. The fixed target is an arbitrary finite set, and may be empty.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- If the intersection has at least `r` points, it contains an `r`-set
from the target. This is the weighted finite union bound. -/
theorem intersection_card_ge_le_subsets (μ : FiniteLaw B) (A : B → Finset X)
    (T : Finset X) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      ∑ J ∈ T.powersetCard r, μ.prob (fun c => J ⊆ A c) := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c hc
  by_cases hcr : r ≤ (A c ∩ T).card
  · rw [ite_eq_left hcr]
    obtain ⟨J, hJ, hJr⟩ := Finset.exists_subset_card_eq hcr
    have hJA : J ⊆ A c := hJ.trans Finset.inter_subset_left
    have hJT : J ⊆ T := hJ.trans Finset.inter_subset_right
    have hm : J ∈ T.powersetCard r := Finset.mem_powersetCard.mpr ⟨hJT, hJr⟩
    have hsingle := Finset.single_le_sum
      (f := fun J : Finset X => if J ⊆ A c then μ.weight c else 0)
      (fun J _ => by split_ifs <;>
        first | exact μ.nonneg c | exact le_rfl) hm
    have hsingle' : μ.weight c ≤
        ∑ J ∈ T.powersetCard r, if J ⊆ A c then μ.weight c else 0 := by
      simpa only [ite_eq_left hJA] using hsingle
    refine hsingle'.trans_eq ?_
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hLA : L ⊆ A c <;> simp [hLA]
  · rw [ite_eq_right hcr]
    exact Finset.sum_nonneg fun J _ => by
      split_ifs <;> first | exact μ.nonneg c | exact le_rfl

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.intersection_card_ge_le_subsets := @_root_.OAI.LeanBlast.SecondKahnKalai.intersection_card_ge_le_subsets
