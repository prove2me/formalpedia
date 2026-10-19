-- Prove2me | solution 1 for OAI.EntropyRateDimension.DigitSumset.card_sumset_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:05:59.102118+00:00
-- url     : https://prove2.me/submissions/017e45d9-d57b-4e7b-a682-592f2eff30fe

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.DigitSumset
universe uα uβ
open scoped BigOperators


theorem solution {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β]
    (S : Finset ℝ) (v : β → α → ℝ)
    (hS : ∀ x ∈ S, ∃ w : β → α, x=∑ j, v j (w j)) (k : ℕ) :
    (sumset S k).card ≤ (k+1)^(Fintype.card β*Fintype.card α) := by
  classical
  choose σ hσ using hS
  let F : (β → α → Fin (k+1)) → ℝ := fun c => ∑ j, ∑ a, ((c j a : ℕ) : ℝ) * v j a
  have hsub : sumset S k ⊆ Finset.univ.image F := by
    intro y hy
    simp only [sumset] at hy
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
    let τ : Fin k → β → α := fun t => σ (w t) (w t).2
    have h1 : ∀ t, ((w t : ℝ)) = ∑ j, v j (τ t j) := fun t => hσ _ (w t).2
    let c : β → α → Fin (k+1) := fun j a => ⟨(Finset.univ.filter (fun t => τ t j = a)).card,
      Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (Finset.card_fin k))⟩
    refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
    calc F c = ∑ j, ∑ t, v j (τ t j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_fiberwise Finset.univ (fun t => τ t j) (fun t => v j (τ t j))]
          apply Finset.sum_congr rfl
          intro a _
          have hfa : ∀ t ∈ Finset.univ.filter (fun t => τ t j = a), v j (τ t j) = v j a :=
            fun t ht => by rw [(Finset.mem_filter.mp ht).2]
          rw [Finset.sum_congr rfl hfa, Finset.sum_const, nsmul_eq_mul]
          try rfl
      _ = ∑ t, ∑ j, v j (τ t j) := Finset.sum_comm
      _ = ∑ t, (w t : ℝ) := Finset.sum_congr rfl (fun t _ => (h1 t).symm)
  calc (sumset S k).card ≤ (Finset.univ.image F).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (β → α → Fin (k+1))).card := Finset.card_image_le
    _ = (k+1)^(Fintype.card β*Fintype.card α) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul,
          mul_comm]

