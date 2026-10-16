-- Prove2me | solution 1 for OAI.RandomKSAT.favg_pi_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:08:20.653451+00:00
-- url     : https://prove2.me/submissions/09fe6d92-d578-4e18-8cd1-62a3c9fbdba4

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FiberRefresh.lean:L46-L63
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.favg_pi_restrict. The node keeps its source
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
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_pi_restrict.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (p : ι → Prop) [DecidablePred p] (f : ({i // p i} → α) → ℝ) :
    favg (fun x : ι → α => f (fun i => x i)) = favg f := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : ι => α)
  have he := favg_equiv e.symm (fun x : ι → α => f (fun i : {i // p i} => x i))
  rw [← he, favg_prod]
  have hh : (fun a : {i // p i} → α =>
      favg (fun b : {i // ¬p i} → α => f (fun i => e.symm (a,b) i))) =
      fun a => f a := by
    funext a
    have hi : ∀ b : {i // ¬p i} → α, (fun i : {i // p i} => e.symm (a,b) i) = a := by
      intro b
      funext i
      simp [e, Equiv.piEquivPiSubtypeProd, i.property]
    simp_rw [hi]
    exact favg_const _
  rw [hh]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.favg_pi_restrict := @_root_.OAI.RandomKSAT.favg_pi_restrict
