-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:28:43.235532+00:00
-- url     : https://prove2.me/submissions/7f58039c-1f72-4bf0-b96a-1c6c77b29b5e

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => f ia.2) =
      observableEntropy s (fun a => ∑ i ∈ t, w i*p i a) f := by
  classical
  have hm : ∀ b, mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => f ia.2) b =
      mass s (fun a => ∑ i ∈ t, w i*p i a) f b := by
    intro b
    simp only [mass, Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  unfold observableEntropy entropy
  simp only [hm]
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨ia, hia, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image_of_mem f (Finset.mem_product.mp hia).2
  · intro b _ hb
    rw [← hm, mass_eq_zero_of_not_mem _ _ _ hb, Real.negMulLog_zero]

