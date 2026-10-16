-- Prove2me | solution 1 for OAI.RandomKSAT.support_probability_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:35:35.608025+00:00
-- url     : https://prove2.me/submissions/000b24dc-0a57-4db0-a250-1a247936cabe

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/SupportProbabilities.lean:L43-L55
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.support_probability_scaled. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities

-- ---- from OAI.Probability.SATVariance.ClauseCombinatorics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma support_card (n k : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = k} = n.choose k := by
  classical
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro s; simp)]
  simp

lemma clause_card (n k : ℕ) : Fintype.card (Clause n k) = n.choose k * 2 ^ k := by
  classical
  change Fintype.card ((s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  trans ∑ _ : {s : Finset (Fin n) // s.card = k}, 2 ^ k
  · apply Finset.sum_congr rfl
    intro s _
    rw [s.property]
  · rw [Finset.sum_const, Finset.card_univ, support_card, smul_eq_mul]

lemma clause_nonempty (n k : ℕ) (hkn : k ≤ n) : Nonempty (Clause n k) := by
  rw [← Fintype.card_pos_iff, clause_card]
  exact Nat.mul_pos (Nat.choose_pos hkn) (pow_pos (by decide) _)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sum.{u_1, u_2} {α : Type u_1} {ι : Type u_2} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    favg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, favg (f i) := by
  simp only [favg, Finset.sum_div]
  exact Finset.sum_comm

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.SupportProbabilities ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma mem_renameClause {n m k : ℕ} (e : Fin n ≃ Fin m) (c : Clause n k) (v : Fin m) :
    v ∈ (renameClause e c).1.1 ↔ e.symm v ∈ c.1.1 := by simp [renameClause]

lemma renameClauseEquiv_apply {n m k : ℕ} (e : Fin n ≃ Fin m) (c : Clause n k) :
    renameClauseEquiv e c = renameClause e c := rfl

lemma support_probability_uniform {n k : ℕ} (v w : Fin n) :
    favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0) =
    favg (fun c : Clause n k => if w ∈ c.1.1 then (1 : ℝ) else 0) := by
  have hh := favg_equiv (renameClauseEquiv (k := k) (Equiv.swap v w))
    (fun c : Clause n k => if w ∈ c.1.1 then (1 : ℝ) else 0)
  simpa only [renameClauseEquiv_apply, mem_renameClause, Equiv.symm_swap, Equiv.swap_apply_right] using hh

lemma support_probability_scaled {n k : ℕ} (hkn : k ≤ n) (v : Fin n) :
    (n : ℝ)*favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0) = k := by
  let := clause_nonempty n k hkn
  have he (c : Clause n k) : (∑ w : Fin n, if w ∈ c.1.1 then (1 : ℝ) else 0) = k := by
    simp only [Finset.sum_boole]
    have hh : Finset.univ.filter (fun w => w ∈ c.1.1) = c.1.1 := by ext w; simp
    rw [hh, c.1.2]
  have hh : favg (fun c : Clause n k => ∑ w : Fin n, if w ∈ c.1.1 then (1 : ℝ) else 0) = k := by
    simp only [he, favg_const]
  rw [favg_sum] at hh
  have hew (w : Fin n) := support_probability_uniform (k := k) w v
  simp only [hew, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact hh

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.support_probability_scaled := @_root_.OAI.RandomKSAT.support_probability_scaled
