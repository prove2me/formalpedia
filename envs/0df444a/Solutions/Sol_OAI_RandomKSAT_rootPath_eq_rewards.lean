-- Prove2me | solution 1 for OAI.RandomKSAT.rootPath_eq_rewards
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:17:23.196425+00:00
-- url     : https://prove2.me/submissions/9935ea89-3ce1-463c-a645-4e3a6b4df3a4

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/PairEvolution.lean:L170-L185
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.rootPath_eq_rewards. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution

-- ---- from OAI.Probability.SATVariance.PairEvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma pairPrefix_zero {u k M : ℕ} (S : PairState u k) (ps : Fin M → RootData u k) :
    pairPrefix S ps 0 = S := by ext x; simp [pairPrefix]

lemma pairPrefix_cons {u k M : ℕ} (S : PairState u k) (p : RootData u k)
    (ps : Fin M → RootData u k) (m : ℕ) :
    pairPrefix S (Fin.cons p ps) (m+1) = pairPrefix (dataStep p S) ps m := by
  ext x
  simp only [pairPrefix, dataStep, Finset.mem_filter, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.val_zero, Nat.zero_lt_succ, true_implies,
    Fin.cons_succ, Fin.val_succ, Nat.succ_lt_succ_iff]
  tauto

lemma dataRewards_cons {u k M : ℕ} (f : PairState u k → ℝ) (S : PairState u k)
    (p : RootData u k) (ps : Fin M → RootData u k) :
    dataRewards f S (Fin.cons p ps) = f S+dataRewards f (dataStep p S) ps := by
  rw [dataRewards, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pairPrefix_zero, pairPrefix_cons]
  rfl

lemma rootPath_eq_rewards {u k : ℕ} (a : Assignment k) (env : ℕ → RootData u k)
    (f : PairState u k → ℝ) (M : ℕ) (z : Fin M → RefreshNoise u k) (S : PairState u k) :
    pathReward (pairEvolution a env) f M z S =
      dataRewards f S (fun i => refreshData a (env i) (z i)) := by
  induction M generalizing env S with
  | zero => simp [pathReward, dataRewards]
  | succ M ih =>
    have he : (fun i : Fin (M+1) => refreshData a (env i) (z i)) =
        Fin.cons (refreshData a (env 0) (z 0))
          (fun i : Fin M => refreshData a (env (i+1)) (Fin.tail z i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he, dataRewards_cons, pathReward]
    change f S + pathReward (pairEvolution a (fun i => env (i+1))) f M (Fin.tail z)
      (dataStep (refreshData a (env 0) (z 0)) S) = _
    rw [ih]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.rootPath_eq_rewards := @_root_.OAI.RandomKSAT.rootPath_eq_rewards
