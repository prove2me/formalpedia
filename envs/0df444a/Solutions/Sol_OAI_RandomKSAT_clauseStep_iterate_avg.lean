-- Prove2me | solution 1 for OAI.RandomKSAT.clauseStep_iterate_avg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:32:43.708373+00:00
-- url     : https://prove2.me/submissions/328b21ca-b72d-4deb-b696-53b14a863c56

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/MarkovReplacement.lean:L117-L130
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.clauseStep_iterate_avg. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma residual_cons {u s m : ℕ} (S : Finset (Assignment u)) (c : Clause u s)
    (cs : Fin m → Clause u s) :
    residual S (Fin.cons c cs) = residual (S.filter (Satisfies c)) cs := by
  ext a
  simp [residual, Fin.forall_fin_succ, and_assoc]

lemma clauseStep_iterate_avg (u s m : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) :
    (clauseStep u s)^[m] f S = favg (fun cs : Fin m → Clause u s => f (residual S cs)) := by
  induction m generalizing S with
  | zero => simp [residual, favg]
  | succ m ih =>
    rw [Function.iterate_succ_apply', clauseStep]
    simp_rw [ih]
    rw [← favg_prod (fun p : Clause u s × (Fin m → Clause u s) =>
      f (residual (S.filter (Satisfies p.1)) p.2)),
      ← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Clause u s))]
    congr 1
    funext p
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, residual_cons]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.clauseStep_iterate_avg := @_root_.OAI.RandomKSAT.clauseStep_iterate_avg
