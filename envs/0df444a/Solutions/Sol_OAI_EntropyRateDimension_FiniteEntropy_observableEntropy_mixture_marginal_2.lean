-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:41:41.662723+00:00
-- url     : https://prove2.me/submissions/3b8050aa-21bf-40f3-8b1d-f46ab2871b27

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L784-L799
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

theorem observableEntropy_mixture_marginal {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => f ia.2) =
      observableEntropy s (fun a => ∑ i ∈ t, w i*p i a) f := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (s.image f) _ _ (by
    intro x hx; exact Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2)]
  unfold observableEntropy entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  simp only [mass, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a = b <;> simp [hf]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal.{uι,uα,uβ} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_marginal.{uι,uα,uβ}
