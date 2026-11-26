-- Prove2me | solution 1 for LogLogJam.Supplement.photon_number_povm
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:28.157301+00:00
-- url     : https://prove2.me/submissions/55d32612-49fa-4a3b-8073-07f98e6cdb03

import Mathlib
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open MeasureTheory BosonicLearn
open scoped Classical
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)



/-- The photon-number measurement used in §8.3.3 is a single-copy Fock POVM.
Its integer outcomes are recorded in the real outcome space of Theorem 8.16. -/
theorem solution :
    ∃ M : FockPOVM (Occupation (Fin 1)) ℝ, ∀ B : Set ℝ, ∀ i j,
      M.effect B i j = if i = j ∧ (i 0 : ℝ) ∈ B then 1 else 0 := by
  classical
  let I := Occupation (Fin 1)
  let E : Set ℝ → Matrix I I ℂ := fun B i j =>
    if i = j ∧ (i 0 : ℝ) ∈ B then 1 else 0
  have hform (B : Set ℝ) (s : Finset I) (z : I → ℂ) :
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j) =
        ∑ i ∈ s, ((if (i 0 : ℝ) ∈ B then ‖z i‖ ^ 2 else 0 : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single_of_mem i hi]
    · by_cases h : (i 0 : ℝ) ∈ B
      · simp [E, h, Complex.conj_mul']
      · simp [E, h]
    · intro j _ hji
      simp [E, Ne.symm hji]
  have hEntry (i j : I) (f : ℕ → Set ℝ) (hd : Pairwise (Function.onFun Disjoint f)) :
      HasSum (fun n => E (f n) i j) (E (⋃ n, f n) i j) := by
    by_cases eq : i = j
    · subst j
      by_cases mem : (i 0 : ℝ) ∈ ⋃ n, f n
      · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp mem
        have hout : ∀ n ≠ a, (i 0 : ℝ) ∉ f n := by
          intro n hn h
          exact Set.disjoint_left.mp (hd hn) h ha
        simpa [E, mem, ha] using (hasSum_single a
          (fun n hn => by simp [E, hout n hn]) : HasSum (fun n => E (f n) i i) (E (f a) i i))
      · have hout (n : ℕ) : (i 0 : ℝ) ∉ f n := fun h => mem (Set.mem_iUnion_of_mem n h)
        simp [E, mem, hout]
    · simp [E, eq]
  obtain ⟨M, he⟩ := fockPOVM_of_effect E (by
    intro B _ s z
    rw [hform B s z, ← Complex.ofReal_sum]
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact ⟨Finset.sum_nonneg (fun i _ => by split <;> positivity),
      Finset.sum_le_sum (fun i _ => by split <;> first | exact le_rfl | positivity)⟩)
    (by ext i j; by_cases h : i = j <;> simp [E, h, Matrix.one_apply]) (by
      intro i j f _ hd
      exact hEntry i j f hd)
  exact ⟨M, fun B i j => congrFun (congrFun (congrFun he B) i) j⟩
