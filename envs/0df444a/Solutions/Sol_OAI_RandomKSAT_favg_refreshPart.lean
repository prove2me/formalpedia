-- Prove2me | solution 1 for OAI.RandomKSAT.favg_refreshPart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:09:51.430758+00:00
-- url     : https://prove2.me/submissions/e19fe631-0c6e-413c-b112-3d55dd3b2e4e

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiberRefresh.lean:L88-L115
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.favg_refreshPart. The node keeps its source
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

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_pi_eval.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : α → ℝ) : favg (fun x : ι → α => f (x i)) = favg f := by
  classical
  have he := favg_equiv (Equiv.funSplitAt i α).symm (fun x : ι → α => f (x i))
  rw [← he, favg_prod]
  simp only [Equiv.funSplitAt_symm_apply]
  simp only [dite_true]
  simp_rw [favg_const]

lemma favg_refreshPart {u k : ℕ} (hku : k ≤ u) (t : RootType k) (a : Assignment k)
    (f : Clause u (k-rootSize t) → ℝ) :
    favg (fun c => favg (fun z : RefreshNoise u k => f (refreshPart t a c z))) = favg f := by
  let := clause_nonempty u k hku
  let := clause_nonempty u (k-1) (by omega)
  let := clause_nonempty u (k-rootSize t) (by omega)
  by_cases h : rootSize t = 0
  · simp only [refreshPart, dite_eq_left h]
    have he :
        favg (fun z : RefreshNoise u k => f (clauseCastEquiv (by omega) z.1)) = favg f := by
      rw [favg_prod]
      dsimp only
      simp_rw [favg_const]
      exact favg_equiv (clauseCastEquiv (by omega)) f
    simp_rw [he]
    exact favg_const _
  · simp only [refreshPart, dite_eq_right h]
    by_cases h' : rootSize t = 1 ∧ RootSatisfies t a
    · simp only [dite_eq_left h']
      rw [favg_const]
      rw [favg_prod]
      dsimp only
      have hp := favg_pi_eval (trueRoot t a h'.2)
        (fun c : Clause u (k-1) => f (clauseCastEquiv (show k-1 = k-rootSize t by omega) c))
      rw [favg_const]
      exact hp.trans (favg_equiv (clauseCastEquiv (u := u) (s := k-1) (t := k-rootSize t) (by omega)) f)
    · simp only [dite_eq_right h']
      simp_rw [favg_const]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.favg_refreshPart := @_root_.OAI.RandomKSAT.favg_refreshPart
