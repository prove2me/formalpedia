-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:55:01.770752+00:00
-- url     : https://prove2.me/submissions/ede8bbfa-e0ad-4b5f-902b-1d7e64ba390e

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

theorem chk_lemma_2_1 {k : ℕ} {A : Type*} (c : A → Fin k → ℝ) (a : (Fin k → ℝ) → A)
    (ha : ∀ r ∈ stdSimplex ℝ (Fin k), ∀ a' : A, dot (c (a r)) r ≤ dot (c a') r) :
    IsProper (fun r y => c (a r) y) := by
  apply isProper_of
  intro q hq r hr
  have := ha q hq (a r)
  simp only [dot] at this
  simpa [mul_comm] using this

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_2_1 := @MulticlassOmni.Lipschitz.chk_lemma_2_1
