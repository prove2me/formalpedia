-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_pderiv_support_v2
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-21T17:02:32.968252+00:00
-- url     : https://prove2.me/submissions/b75c3ee4-774d-4ceb-be75-2f6c8ddc57e3

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F) (i : Fin d) :
    logarithmicDegreeBound w N (MvPolynomial.pderiv i F) := by
  classical
  intro a ha
  have hcoeff : (MvPolynomial.pderiv i F).coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hfc : F.coeff (a + Finsupp.single i (1 : ℕ)) ≠ 0 := by
    intro hz
    exact hcoeff (by simp [hz])
  have hb : a + Finsupp.single i (1 : ℕ) ∈ F.support := MvPolynomial.mem_support_iff.mpr hfc
  have h2 : (∑ j, (w j : Real) * ((Finsupp.single i (1 : ℕ)) j : Real)) = (w i : Real) := by
    calc
      (∑ j, (w j : Real) * ((Finsupp.single i (1 : ℕ)) j : Real))
          = ∑ j, if i = j then (w j : Real) else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : i = j <;> simp [h]
      _ = (w i : Real) := by
        rw [Finset.sum_ite_eq Finset.univ i (fun j => (w j : Real))]
        simp
  have hsum : (∑ j, (w j : Real) * ((a + Finsupp.single i (1 : ℕ)) j : Real))
      = (∑ j, (w j : Real) * (a j : Real)) + (w i : Real) := by
    calc
      (∑ j, (w j : Real) * ((a + Finsupp.single i (1 : ℕ)) j : Real))
          = ∑ j, (w j : Real) * ((a j : Real) + ((Finsupp.single i (1 : ℕ)) j : Real)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finsupp.add_apply, Nat.cast_add]
      _ = ∑ j, ((w j : Real) * (a j : Real) + (w j : Real) * ((Finsupp.single i (1 : ℕ)) j : Real)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j, (w j : Real) * (a j : Real)) + (∑ j, (w j : Real) * ((Finsupp.single i (1 : ℕ)) j : Real)) :=
            Finset.sum_add_distrib
      _ = (∑ j, (w j : Real) * (a j : Real)) + (w i : Real) := by rw [h2]
  have hbound : (∑ j, (w j : Real) * ((a + Finsupp.single i (1 : ℕ)) j : Real)) ≤ N :=
    hF (a + Finsupp.single i (1 : ℕ)) hb
  rw [hsum] at hbound
  linarith [hw i]
