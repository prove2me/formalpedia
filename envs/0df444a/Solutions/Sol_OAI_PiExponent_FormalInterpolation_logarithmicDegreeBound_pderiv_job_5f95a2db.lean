-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv_job_5f95a2db
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:21:28.298587+00:00
-- url     : https://prove2.me/submissions/37b227a9-c354-451c-b1b3-cbf2daac4ad4

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace S105LDB

theorem add {d : Nat} (w : Fin d → Rat) (H : Real)
    (F G : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w H F)
    (hG : logarithmicDegreeBound w H G) :
    logarithmicDegreeBound w H (F + G) := by
  classical
  intro a ha
  rcases Finset.mem_union.1 (MvPolynomial.support_add ha) with h | h
  · exact hF a h
  · exact hG a h

theorem zero {d : Nat} (w : Fin d → Rat) (H : Real) :
    logarithmicDegreeBound w H (0 : MvPolynomial (Fin d) Complex) := by
  intro a ha; simp at ha

theorem fsum {d : Nat} (w : Fin d → Rat) (H : Real)
    {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin d) Complex)
    (hf : ∀ j ∈ s, logarithmicDegreeBound w H (f j)) :
    logarithmicDegreeBound w H (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero w H
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add w H _ _ (hf a (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem monomial_bound {d : Nat} (w : Fin d → Rat) (H : Real) (s : Fin d →₀ ℕ) (c : Complex)
    (hs : (∑ i, (w i : Real) * (s i : Real)) ≤ H) :
    logarithmicDegreeBound w H (MvPolynomial.monomial s c) := by
  classical
  intro a ha
  have := MvPolynomial.support_monomial_subset ha
  rw [Finset.mem_singleton] at this
  subst this; exact hs

theorem le_of_le {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (s' s : Fin d →₀ ℕ) (h : s' ≤ s) :
    (∑ i, (w i : Real) * (s' i : Real)) ≤ (∑ i, (w i : Real) * (s i : Real)) := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i).le
  exact_mod_cast h i

theorem pderiv {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F) :
    logarithmicDegreeBound w H (MvPolynomial.pderiv i F) := by
  classical
  conv_rhs => rw [F.as_sum]
  rw [map_sum]
  apply fsum
  intro s hs
  rw [MvPolynomial.pderiv_monomial]
  apply monomial_bound
  exact (le_of_le w hw _ _ tsub_le_self).trans (hF s hs)

theorem eulerTerm {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    (hw : ∀ i, 0 < (w i : Real))
    (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w H F) :
    logarithmicDegreeBound w H
      (MvPolynomial.X i * MvPolynomial.pderiv i F) := by
  classical
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum]
  apply fsum
  intro s hs
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  by_cases h0 : s i = 0
  · simp [h0]; exact zero w H
  · apply monomial_bound
    have : Finsupp.single i 1 + (s - Finsupp.single i 1) = s := by
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hj]
    rw [this]; exact hF s hs

end S105LDB

theorem solution {m : Nat} (w : Fin (m + 1) → Rat) (H : Real) (hw : ∀ i, 0 < (w i : Real)) (i : Fin (m + 1)) (F : MvPolynomial (Fin (m + 1)) Complex) (hF : logarithmicDegreeBound w H F) : logarithmicDegreeBound w H (MvPolynomial.pderiv i F) :=
  S105LDB.pderiv w H hw i F hF
