-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:46:05.442877+00:00
-- url     : https://prove2.me/submissions/fbbf0ed9-5418-4106-9786-45559be2163a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L867-L898
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general. The node keeps its source
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

theorem entropy_scale {α : Type uα} (s : Finset α) (p : α → ℝ) (c : ℝ) :
    entropy s (fun a => c * p a) =
      (∑ a ∈ s, p a) * Real.negMulLog c + c * entropy s p := by
  simp only [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

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

theorem observableEntropy_mixture_joint_general {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      ∑ i ∈ t, ((∑ a ∈ s, p i a)*Real.negMulLog (w i)+
        w i*observableEntropy s (p i) f) := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (t ×ˢ s.image f) _ _ (by
    intro x hx
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hx).1,
      Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2⟩)]
  have hm : ∀ i ∈ t, ∀ b : β,
      mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) (i,b) =
        w i * mass s (p i) f b := by
    intro i hi b
    simp only [mass, Finset.sum_filter, Finset.sum_product, Prod.mk.injEq]
    simp_rw [ite_and]
    rw [Finset.sum_eq_single i]
    · simp [Finset.mul_sum, mul_ite]
    · intro j _ hji
      simp [hji]
    · exact fun h => (h hi).elim
  calc
    _ = ∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b) := by
      simp only [entropy, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (hm i hi b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [entropy_scale, mass_sum]
      rfl

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general.{uι,uα,uβ} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general.{uι,uα,uβ}
