-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:55:01.606739+00:00
-- url     : https://prove2.me/submissions/697ed123-d353-4dd0-896f-036189f7cc11

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses

section
namespace MulticlassOmni.Dev.Basic
open MulticlassOmni.Lipschitz

theorem coe_sum_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

theorem isProper_of {k : ℕ} (ℓ : Loss k)
    (h : ∀ q ∈ stdSimplex ℝ (Fin k), ∀ r ∈ stdSimplex ℝ (Fin k),
      ∑ y, q y * ℓ q y ≤ ∑ y, q y * ℓ r y) : IsProper ℓ := by
  refine ⟨?_, ?_⟩
  · intro p hp i
    simp [toEReal, hp]
  · intro p hp q hq
    have e1 : ∑ i, (q i : EReal) * toEReal ℓ q i = ((∑ y, q y * ℓ q y : ℝ) : EReal) := by
      simp only [toEReal, hq, if_true]
      simp only [← EReal.coe_mul]; rw [coe_sum_ereal]
    have e2 : ∑ i, (q i : EReal) * toEReal ℓ p i = ((∑ y, q y * ℓ p y : ℝ) : EReal) := by
      simp only [toEReal, hp, if_true]
      simp only [← EReal.coe_mul]; rw [coe_sum_ereal]
    rw [e1, e2]
    exact_mod_cast h q hq p hp

end MulticlassOmni.Dev.Basic

namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.Basic

end MulticlassOmni.Lipschitz
end

section
namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.Basic

theorem chk_lemma_2_2 {k : ℕ} (H : (Fin k → ℝ) → ℝ) (gradH : (Fin k → ℝ) → Fin k → ℝ)
    (hH : ConcaveOn ℝ (stdSimplex ℝ (Fin k)) H)
    (hgrad : ∀ r ∈ stdSimplex ℝ (Fin k), ∀ q ∈ stdSimplex ℝ (Fin k),
      H q ≤ H r + dot (gradH r) (q - r)) :
    IsProper (fun r y => H r + dot (gradH r) (unitVec y - r)) := by
  apply isProper_of
  intro q hq r hr
  have key : ∀ s ∈ stdSimplex ℝ (Fin k), ∑ y, q y * (H s + dot (gradH s) (unitVec y - s))
      = H s + dot (gradH s) (q - s) := by
    intro s _
    have h1 : ∑ y, q y = 1 := hq.2
    have hd : ∀ y, dot (gradH s) (unitVec y - s) = gradH s y - dot (gradH s) s := by
      intro y
      simp [dot, unitVec, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    have hq' : dot (gradH s) (q - s) = ∑ y, q y * gradH s y - dot (gradH s) s := by
      simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, mul_comm]
    have : ∑ y, q y * (H s + dot (gradH s) (unitVec y - s))
        = ∑ y, (q y * H s + q y * gradH s y - q y * dot (gradH s) s) := by
      apply Finset.sum_congr rfl; intro y _; rw [hd y]; ring
    rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, h1, hq']
    ring
  rw [key q hq, key r hr]
  have h3 := hgrad r hr q hq
  have h4 : ∀ s ∈ stdSimplex ℝ (Fin k), True := fun _ _ => trivial
  have h5 : dot (gradH q) (q - q) = 0 := by simp [dot]
  rw [h5, add_zero]
  exact h3

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_2_2 := @MulticlassOmni.Lipschitz.chk_lemma_2_2
