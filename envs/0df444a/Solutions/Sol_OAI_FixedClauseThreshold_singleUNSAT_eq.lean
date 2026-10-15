-- Prove2me | solution 1 for OAI.FixedClauseThreshold.singleUNSAT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:25:52.501519+00:00
-- url     : https://prove2.me/submissions/14ebe395-4fb3-41ba-b126-1ad572a41ee1

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/ClauseProcess.lean:L306-L319
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.singleUNSAT_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess

-- ---- from OAI.Probability.RandomSAT.Clauses ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.ClauseProcess ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem kills_iff_addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    KillsSolutions S C ↔ ¬ (addClause S C).Nonempty := by
  change (∀ σ ∈ S, ¬ SatisfiesClause σ C) ↔ ¬ ∃ σ, σ ∈ addClause S C
  simp only [mem_addClause, not_exists, not_and]

theorem singleUNSAT_eq {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    uniformProbability (fun C : ProperClause n k => KillsSolutions S C) =
      1 - survival k 1 S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [uniformProbability_eq_mean, survival_succ]
  simp only [survival_zero]
  calc
    _ = uniformMean (fun C : ProperClause n k => 1 - alive (addClause S C)) := by
      apply uniformMean_congr
      intro C
      rw [kills_iff_addClause]
      unfold alive
      by_cases h : (addClause S C).Nonempty <;> simp [h]
    _ = _ := by rw [uniformMean_sub, uniformMean_const]

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.singleUNSAT_eq := @_root_.OAI.FixedClauseThreshold.singleUNSAT_eq
