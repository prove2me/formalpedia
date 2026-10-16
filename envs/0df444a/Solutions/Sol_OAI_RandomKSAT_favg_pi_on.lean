-- Prove2me | solution 1 for OAI.RandomKSAT.favg_pi_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:36:42.529237+00:00
-- url     : https://prove2.me/submissions/37d42bbd-7375-4605-9a57-e0e2fad70d84

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/HallSatisfiability.lean:L85-L102
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.favg_pi_on. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

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

lemma favg_pi_product.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℝ) :
    favg (fun x : ι → α => ∏ i, f i (x i)) = ∏ i, favg (f i) := by
  classical
  unfold favg
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.HallSatisfiability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_pi_on.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (I : Finset ι) (f : α → ℝ) :
    favg (fun w : ι → α => ∏ i ∈ I, f (w i)) = (favg f)^I.card := by
  have he (w : ι → α) : (∏ i ∈ I, f (w i)) = ∏ i, if i ∈ I then f (w i) else 1 := by
    symm
    rw [← Finset.prod_filter]
    congr 1
    ext i
    simp
  simp only [he]
  change favg (fun w : ι → α => ∏ i, (fun i a => if i ∈ I then f a else 1) i (w i)) = _
  rw [favg_pi_product (fun i a => if i ∈ I then f a else 1)]
  have hh (i : ι) : favg (fun a => if i ∈ I then f a else 1) = if i ∈ I then favg f else 1 := by
    split_ifs <;> simp [favg_const]
  simp only [hh]
  rw [← Finset.prod_filter]
  have he' : Finset.univ.filter (fun i => i ∈ I) = I := by ext i; simp
  rw [he', Finset.prod_const]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.favg_pi_on := @_root_.OAI.RandomKSAT.favg_pi_on
