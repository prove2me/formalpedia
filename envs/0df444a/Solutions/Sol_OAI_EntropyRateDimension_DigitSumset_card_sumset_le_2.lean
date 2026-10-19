-- Prove2me | solution 2 for OAI.EntropyRateDimension.DigitSumset.card_sumset_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:02:09.059314+00:00
-- url     : https://prove2.me/submissions/c525e9b9-dda0-413f-8e5b-6d520aee4b32

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/DigitSumset.lean:L41-L59
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.DigitSumset.card_sumset_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

-- ---- from OAI.MeasureTheory.SelfSimilar.DigitSumset ----
namespace OAI

universe uα uβ

section

open scoped BigOperators
namespace EntropyRateDimension
namespace DigitSumset

theorem counts_expand {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] {k : ℕ}
    (v : β → α → ℝ) (w : Fin k → β → α) :
    ∑ t, ∑ j, v j (w t j) = ∑ j, ∑ a, ((counts w j a).val : ℝ)*v j a := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_fiberwise Finset.univ (fun t : Fin k => w t j)]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ t ∈ Finset.univ.filter (fun t : Fin k => w t j=a), v j (w t j) =
        ∑ _t ∈ Finset.univ.filter (fun t : Fin k => w t j=a), v j a := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = _ := by simp [counts]

theorem card_sumset_le {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β]
    (S : Finset ℝ) (v : β → α → ℝ)
    (hS : ∀ x ∈ S, ∃ w : β → α, x=∑ j, v j (w j)) (k : ℕ) :
    (sumset S k).card ≤ (k+1)^(Fintype.card β*Fintype.card α) := by
  classical
  let F : (β → α → Fin (k+1)) → ℝ := fun c => ∑ j, ∑ a, ((c j a).val : ℝ)*v j a
  have hin : sumset S k ⊆ Finset.univ.image F := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    choose w hw using (fun t => hS (u t) (u t).property)
    apply Finset.mem_image.mpr
    refine ⟨counts w,Finset.mem_univ _,?_⟩
    change (∑ j, ∑ a, ((counts w j a).val : ℝ)*v j a)=∑ t, (u t : ℝ)
    rw [← counts_expand]
    exact Finset.sum_congr rfl (fun t _ => (hw t).symm)
  calc
    (sumset S k).card ≤ (Finset.univ.image F).card := Finset.card_le_card hin
    _ ≤ (Finset.univ : Finset (β → α → Fin (k+1))).card := Finset.card_image_le
    _ = _ := by simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,← pow_mul]; rw [Nat.mul_comm]

end DigitSumset
end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.DigitSumset
open scoped BigOperators


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.DigitSumset.card_sumset_le.{uα,uβ} := @_root_.OAI.EntropyRateDimension.DigitSumset.card_sumset_le.{uα,uβ}
