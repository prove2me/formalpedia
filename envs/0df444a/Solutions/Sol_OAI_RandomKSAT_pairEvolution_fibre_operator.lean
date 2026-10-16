-- Prove2me | solution 1 for OAI.RandomKSAT.pairEvolution_fibre_operator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:16:05.410961+00:00
-- url     : https://prove2.me/submissions/77ef38a4-be54-40c9-8126-a3ce0ab9242f

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/PairEvolution.lean:L101-L119
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.pairEvolution_fibre_operator. The node keeps its source
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

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.PairEvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma fibre_dataStep {u k : ℕ} (p : RootData u k) (a : Assignment k) (S : PairState u k) :
    fibre a (dataStep p S) = fibre a S ∩ dataMask p a := by
  ext b
  simp [fibre, dataStep, dataMask]

lemma rootSatisfies_zero {k : ℕ} (t : RootType k) (h : rootSize t = 0) (a : Assignment k) :
    ¬ RootSatisfies t a := by
  rintro ⟨j,hj⟩
  have hm : j ∈ rootSupport t := by simp [rootSupport, hj]
  have he : rootSupport t = ∅ := Finset.card_eq_zero.mp h
  rw [he] at hm
  exact Finset.notMem_empty j hm

lemma satisfies_cast {u s t : ℕ} (h : s = t) (c : Clause u s) (b : Assignment u) :
    Satisfies (clauseCastEquiv h c) b ↔ Satisfies c b := by
  subst t
  rfl

lemma fibre_refreshData {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) (S : PairState u k) :
    fibre a (dataStep (refreshData a p z) S) =
      if rootSize p.1 = 0 then (fibre a S).filter (Satisfies z.1)
      else fibre a S ∩ dataMask p a := by
  ext b
  by_cases h : rootSize p.1 = 0
  · simp [fibre_dataStep, dataMask, DataSatisfies, refreshData, refreshPart, h,
      rootSatisfies_zero p.1 h a, satisfies_cast]
  · by_cases ht : rootSize p.1 = 1 ∧ RootSatisfies p.1 a
    · simp [fibre_dataStep, dataMask, DataSatisfies, refreshData, refreshPart, ht]
    · simp [fibre_dataStep, dataMask, DataSatisfies, refreshData, refreshPart, h, ht]

lemma pairEvolution_fibre_operator {u k : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : ℕ → RootData u k) (i : ℕ) (f : Finset (Assignment u) → ℝ) (S : PairState u k) :
    uniformStep (pairEvolution a env) i (fun T => f (fibre a T)) S =
      scheduledStep u k (fun i => rootSize (env i).1 = 0) (fun i => dataMask (env i) a) i f (fibre a S) := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  unfold uniformStep pairEvolution
  simp_rw [fibre_refreshData]
  by_cases h : rootSize (env i).1 = 0
  · simp only [scheduledStep, h, ite_true]
    rw [favg_prod]
    dsimp only
    have hc (c : Clause u k) :
        favg (fun _ : Fin k → Clause u (k-1) => f ((fibre a S).filter (Satisfies c))) =
        f ((fibre a S).filter (Satisfies c)) := favg_const _
    simp_rw [hc]
    rfl
  · simp only [scheduledStep, h, ite_false]
    exact favg_const _

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.pairEvolution_fibre_operator := @_root_.OAI.RandomKSAT.pairEvolution_fibre_operator
