-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_interpolant_coeff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:08:58.184986+00:00
-- url     : https://prove2.me/submissions/783ea73d-3af4-446d-a928-7efc62df43bb

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib

section

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

namespace PiL12

theorem interp_coeff (nu : Real) (d : FixedData nu) (H : Real) (f : Column d H → Complex) (c : Column d H) : (∑ c' : Column d H, MvPolynomial.C (f c') * MvPolynomial.monomial (InterpolationMatrix.exponentVector c'.1) 1).coeff (InterpolationMatrix.exponentVector c.1) = f c := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    rw [if_neg, mul_zero]
    intro h
    apply hc'
    apply Subtype.ext
    simpa [InterpolationMatrix.exponentVector] using h
  · simp

theorem shear {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    truncatedPolynomialJet c T
      (MvPolynomial.aeval
        (fun i : Fin (m + 1) =>
          Fin.cases (MvPolynomial.X 0 - 1)
            (fun j => MvPolynomial.X j.succ -
              Polynomial.aeval (MvPolynomial.X 0 - 1)
                (InterpolationMatrix.truncatedLog (T j))) i) Q) =
    MvPolynomial.aeval
      (fun i : Fin (m + 1) =>
        MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h : (fun i : Fin (m + 1) => truncatedPolynomialJet c T
      (Fin.cases (MvPolynomial.X 0 - 1)
            (fun j => MvPolynomial.X j.succ -
              Polynomial.aeval (MvPolynomial.X 0 - 1)
                (InterpolationMatrix.truncatedLog (T j))) i)) =
      (fun i : Fin (m + 1) => MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [truncatedPolynomialJet]
    · simp only [Fin.cases_succ, map_sub, truncatedPolynomialJet, MvPolynomial.aeval_X]
      rw [← Polynomial.aeval_algHom_apply]
      simp
  rw [h]

end PiL12

end

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation


theorem solution (nu : Real) (d : FixedData nu) (H : Real) (f : Column d H → Complex) (c : Column d H) : (∑ c' : Column d H, MvPolynomial.C (f c') * MvPolynomial.monomial (InterpolationMatrix.exponentVector c'.1) 1).coeff (InterpolationMatrix.exponentVector c.1) = f c := by
  apply PiL12.interp_coeff <;> assumption
