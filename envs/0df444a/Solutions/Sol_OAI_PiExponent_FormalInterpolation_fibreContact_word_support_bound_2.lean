-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.fibreContact_word_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:32:26.139771+00:00
-- url     : https://prove2.me/submissions/3367b1f8-79b3-477d-8636-9839f9991ba2

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib

section

open OAI.PiExponent.FormalInterpolation

namespace PiL18

lemma pderiv_bound {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex) (hF : fibreContactSupportBound W N F)
    (hW : ∀ i, 0 ≤ (W i : Real)) (i : Fin m) :
    fibreContactSupportBound W N (MvPolynomial.pderiv i F) := by
  classical
  intro b hb
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hb
  have hmem : b + Finsupp.single i 1 ∈ F.support := by
    rw [MvPolynomial.mem_support_iff]; intro h; rw [h, zero_mul] at hb; exact hb rfl
  have h1 := hF _ hmem
  have : ∑ k : Fin m, (((b + Finsupp.single i 1 : Fin m →₀ ℕ) k : ℕ) : Real) * (W k : Real) =
      (∑ k : Fin m, (b k : Real) * (W k : Real)) + W i := by
    simp only [Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib, Finsupp.single_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  rw [this] at h1
  linarith [hW i]

theorem word_bound {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound W N F)
    (word : List (Fin m))
    (hW : ∀ i, 0 ≤ (W i : Real)) :
    fibreContactSupportBound W N (fibreContactWord word F) := by
  induction word with
  | nil => simpa [fibreContactWord] using hF
  | cons i word ih =>
    have : fibreContactWord (i :: word) F = MvPolynomial.pderiv i (fibreContactWord word F) := by
      simp [fibreContactWord]
    rw [this]
    exact pderiv_bound W N _ ih hW i

end PiL18

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (W : Fin m → Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hF : fibreContactSupportBound W N F)
    (word : List (Fin m))
    (hW : ∀ i, 0 ≤ (W i : Real)) :
    fibreContactSupportBound W N (fibreContactWord word F) := by
  apply PiL18.word_bound <;> assumption
