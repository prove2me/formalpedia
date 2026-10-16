-- Prove2me | solution 1 for OAI.RandomKSAT.insertion_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:51:56.229638+00:00
-- url     : https://prove2.me/submissions/7d5fa4c9-4779-4e66-b11a-e936df3b255b

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/InsertionVariance.lean:L195-L214
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.insertion_moments. The node keeps its source
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
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.InsertionVariance ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_fin_lt {L t : ℕ} (ht : t ≤ L) :
    favg (fun i : Fin L => if i.val < t then (1:ℝ) else 0) = (t:ℝ)/L := by
  unfold favg
  simp only [Fintype.card_fin]
  congr 1
  have he : {i : Fin L // i.val < t} ≃ Fin t :=
    { toFun := fun i => ⟨i.1.val,i.2⟩
      invFun := fun i => ⟨⟨i.val,i.isLt.trans_le ht⟩,i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_subtype] using congrArg (fun x : ℕ => (x:ℝ)) (Fintype.card_congr he)

lemma insertion_moments {L t : ℕ} (hL : 0 < L) (ht : t ≤ L) :
    favg (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      (1+1/(L:ℝ))*t ∧
    fvariance (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      (t:ℝ)*((L:ℝ)-t)/(L:ℝ)^2 := by
  let : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  let f : Fin L → ℝ := fun i => if i.val < t then 1 else 0
  have hf : favg f = (t:ℝ)/L := favg_fin_lt ht
  have hf2 : (fun i => f i ^ 2) = f := by funext i; simp only [f]; split_ifs <;> norm_num
  have he : (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      fun i => (t:ℝ)+f i := by funext i; simp only [Nat.cast_add,f]; split_ifs <;> norm_num
  have he2 : (fun i => ((t:ℝ)+f i)^2) = fun i => (t:ℝ)^2+(2*t)*f i+f i^2 := by
    funext i; ring
  rw [he]
  constructor
  · rw [favg_add,favg_const,hf]; ring
  · simp only [fvariance, he2, favg_add, favg_const, favg_mul, hf2, hf]
    field_simp
    ring

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.insertion_moments := @_root_.OAI.RandomKSAT.insertion_moments
