-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fractionField_trdeg_eq_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:32:08.358275+00:00
-- url     : https://prove2.me/submissions/29390599-7e22-4517-b836-d26aa0012cbd

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem solution {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] : Algebra.trdeg Complex (FractionRing (MvPolynomial (Fin (Nat.succ m)) Complex ⧸ P)) = Algebra.trdeg Complex (MvPolynomial (Fin (Nat.succ m)) Complex ⧸ P) := by
  set B := MvPolynomial (Fin (Nat.succ m)) Complex ⧸ P
  have hL : Algebra.trdeg B (FractionRing B) = 0 := by
    have : Algebra.IsAlgebraic B (FractionRing B) :=
      IsLocalization.isAlgebraic (FractionRing B) (nonZeroDivisors B)
    exact trdeg_eq_zero
  have hadd := trdeg_add_eq (R := Complex) (S := B) (A := FractionRing B)
  rw [hL, add_zero] at hadd
  exact hadd.symm
