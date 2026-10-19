-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:29:04.234833+00:00
-- url     : https://prove2.me/submissions/c19a8958-a943-446b-8ad8-750e4178f783

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_mix_general {ι : Type*} {α : Type*} {β : Type*} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      ∑ i ∈ t, ((∑ a ∈ s, p i a)*Real.negMulLog (w i)+
        w i*observableEntropy s (p i) f) := by
  classical
  have him : (t ×ˢ s).image (fun ia => (ia.1, f ia.2)) = t ×ˢ s.image f := by
    ext ⟨i, b⟩
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨j, a, ⟨hj, ha⟩, rfl, rfl⟩; exact ⟨hj, a, ha, rfl⟩
    · rintro ⟨hi, a, ha, rfl⟩; exact ⟨i, a, ⟨hi, ha⟩, rfl, rfl⟩
  have hm : ∀ i ∈ t, ∀ b, mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2)
      (fun ia => (ia.1, f ia.2)) (i, b) = w i * mass s (p i) f b := by
    intro i hi b
    simp only [mass, Finset.sum_filter, Finset.sum_product, Prod.mk.injEq, Finset.mul_sum]
    rw [Finset.sum_eq_single_of_mem i hi]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [hj]
  unfold observableEntropy
  rw [him]
  unfold entropy
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [hm i hi, Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, mass_sum]

theorem solution {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      ∑ i ∈ t, ((∑ a ∈ s, p i a)*Real.negMulLog (w i)+
        w i*observableEntropy s (p i) f) := by
  exact h44_mix_general t s w p f

