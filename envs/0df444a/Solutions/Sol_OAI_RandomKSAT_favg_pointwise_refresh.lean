-- Prove2me | solution 1 for OAI.RandomKSAT.favg_pointwise_refresh
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:12:27.750641+00:00
-- url     : https://prove2.me/submissions/e1c1aa4f-192f-44c9-844a-da43986043ad

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiberRefresh.lean:L155-L193
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.favg_pointwise_refresh. The node keeps its source
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

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_equiv.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    favg (fun a => f (e a)) = favg f := by
  rw [favg, favg, e.sum_comp f, Fintype.card_congr e]

lemma favg_comm.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    favg (fun a => favg (f a)) = favg (fun b => favg (fun a => f a b)) := by
  simp only [favg, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

lemma favg_prod.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    favg f = favg (fun a => favg fun b => f (a,b)) := by
  simp only [favg, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

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

lemma favg_cons.{u_1} {α : Type u_1} [Fintype α] {m : ℕ} (f : (Fin (m+1) → α) → ℝ) :
    favg f = favg (fun t : Fin m → α => favg (fun a : α => f (Fin.cons a t))) := by
  rw [← favg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => α)) f, favg_prod, favg_comm]
  rfl

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiberRefresh ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_pointwise_refresh.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β]
    (R : α → β → α)
    (hR : ∀ f : α → ℝ, favg (fun a => favg (fun b => f (R a b))) = favg f)
    (m : ℕ) (f : (Fin m → α) → ℝ) :
    favg (fun x : Fin m → α => favg (fun z : Fin m → β => f (fun i => R (x i) (z i)))) =
      favg f := by
  induction m with
  | zero =>
    simp only [favg, Fintype.sum_unique, Fintype.card_unique, Nat.cast_one, div_one]
    congr 1
    funext i
    exact i.elim0
  | succ m ih =>
    rw [favg_cons]
    simp_rw [favg_cons (α := β)]
    have he (x : Fin m → α) (a : α) (z : Fin m → β) (b : β) :
        (fun i : Fin (m+1) => R ((Fin.cons a x : Fin (m+1) → α) i) ((Fin.cons b z : Fin (m+1) → β) i)) =
        Fin.cons (R a b) (fun i => R (x i) (z i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hf (x : Fin m → α) (a : α) (z : Fin m → β) (b : β) :
        f (fun i => R ((Fin.cons a x : Fin (m+1) → α) i) ((Fin.cons b z : Fin (m+1) → β) i)) =
        f (Fin.cons (R a b) (fun i => R (x i) (z i))) := congrArg f (he x a z b)
    simp_rw [hf]
    conv_lhs => arg 1; intro x; rw [favg_comm]
    have hsingle (x : Fin m → α) (z : Fin m → β) :
        favg (fun a => favg (fun b => f (Fin.cons (R a b) (fun i => R (x i) (z i))))) =
        favg (fun c => f (Fin.cons c (fun i => R (x i) (z i)))) :=
      hR (fun c : α => f (Fin.cons c (fun i : Fin m => R (x i) (z i))))
    simp_rw [hsingle]
    conv_lhs => arg 1; intro x; rw [favg_comm]
    rw [favg_comm]
    have htail (c : α) :
        favg (fun x : Fin m → α => favg (fun z : Fin m → β =>
          f (Fin.cons c (fun i => R (x i) (z i))))) =
        favg (fun x : Fin m → α => f (Fin.cons c x)) :=
      ih (fun x : Fin m → α => f (Fin.cons c x))
    simp_rw [htail]
    rw [favg_cons, favg_comm]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.favg_pointwise_refresh := @_root_.OAI.RandomKSAT.favg_pointwise_refresh
