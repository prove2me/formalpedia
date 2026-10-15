-- Prove2me | solution 1 for OAI.FixedClauseThreshold.clauseHead_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:27:06.670721+00:00
-- url     : https://prove2.me/submissions/7ce8ee75-83c2-41e3-814f-aa50d81872ad

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/ClauseProcess.lean:L397-L419
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.clauseHead_mean. The node keeps its source
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

theorem uniformMean_sum_type {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α ⊕ β → ℝ) :
    uniformMean f =
      ((Fintype.card α : ℝ) / (Fintype.card α + Fintype.card β)) *
        uniformMean (fun a => f (Sum.inl a)) +
      ((Fintype.card β : ℝ) / (Fintype.card α + Fintype.card β)) *
        uniformMean (fun b => f (Sum.inr b)) := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformMean, Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add]
  field_simp

theorem head_incidence_ratio {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v) :
    ((v.choose (k - 1) * 2 ^ (k - 1) * 2 : ℕ) : ℝ) /
      ((v.choose k * 2 ^ k + v.choose (k - 1) * 2 ^ (k - 1) * 2 : ℕ) : ℝ) =
      (k : ℝ) / (v + 1) := by
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hch : v.choose k + v.choose (k - 1) = (v + 1).choose k := by
    simpa only [Nat.succ_eq_add_one, hks, add_comm] using (Nat.choose_succ_succ v (k - 1)).symm
  have hmult : ((v : ℝ) + 1) * (v.choose (k - 1) : ℝ) =
      ((v + 1).choose k : ℝ) * (k : ℝ) := by
    exact_mod_cast (by simpa only [hks] using Nat.add_one_mul_choose_eq v (k - 1))
  have hpow : (2 : ℝ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, hks]
  have hcpos : (0 : ℝ) < (v + 1).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ v + 1)
  have hvpos : (0 : ℝ) < (v : ℝ) + 1 := by positivity
  push_cast
  simp only [mul_assoc, hpow]
  rw [← add_mul]
  have hc : (v.choose k : ℝ) + v.choose (k - 1) = (v + 1).choose k := by
    exact_mod_cast hch
  rw [hc]
  apply (div_eq_div_iff (by positivity) hvpos.ne').mpr
  nlinarith [congrArg (fun z : ℝ => z * 2 ^ k) hmult]

theorem clauseHead_mean {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (f : (ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)) → ℝ) :
    uniformMean (fun C : ProperClause (v + 1) k => f (clauseHeadSplit hk C)) =
      (1 - (k : ℝ) / (v + 1)) * uniformMean (fun C => f (Sum.inl C)) +
      ((k : ℝ) / (v + 1)) *
        uniformMean (fun Q => uniformMean (fun b : Bool => f (Sum.inr (Q, b)))) := by
  let : Nonempty (ProperClause v k) := nonempty_properClause hkv
  let : Nonempty (ProperClause v (k - 1)) := nonempty_properClause (by omega)
  change uniformMean (fun C => f (clauseHeadEquiv hk C)) = _
  rw [uniformMean_equiv, uniformMean_sum_type, uniformMean_prod]
  have hr := head_incidence_ratio hk hkv
  have ht : (0 : ℝ) < Fintype.card (ProperClause v k) +
      Fintype.card (ProperClause v (k - 1) × Bool) := by
    exact add_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hr' : (Fintype.card (ProperClause v (k - 1) × Bool) : ℝ) /
      (Fintype.card (ProperClause v k) + Fintype.card (ProperClause v (k - 1) × Bool)) =
      (k : ℝ) / (v + 1) := by
    simpa only [Fintype.card_prod, Fintype.card_bool, card_properClause, Nat.cast_add] using hr
  rw [hr', ← hr']
  congr 1
  apply congrArg (fun x : ℝ => x * uniformMean (fun C => f (Sum.inl C)))
  field_simp
  ring

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.clauseHead_mean := @_root_.OAI.FixedClauseThreshold.clauseHead_mean
