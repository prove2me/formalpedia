-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_subcritical_finite_adjoin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-19T03:08:15.545752+00:00
-- url     : https://prove2.me/submissions/268c1157-eefb-4a7c-820e-038103a60668
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_strict_monic_power_certificate
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_of_strict_monic_relations
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 ≤ D ∧ D < (s : Real) * (R : Real) ∧
        ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin (d.m + 1)) Complex,
          (∀ j, f j ∈ (logarithmicCentersIdeal
            (fun j : Fin d.K => fun i =>
              (j.val : Complex) *
                MatrixArithmetic.rationalCenters
                  (finiteNumerators d) (finiteDenominators d) i)
            (fun _ => e 0) e) ^ s) ∧
          (∀ j, ∀ a ∈ (f j).support,
            ∑ i, InterpolationMatrix.columnWeights d.w0
              (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (a i : Real) ≤ D) ∧
          Module.Finite (Algebra.adjoin Complex (Set.range f))
            (MvPolynomial (Fin (d.m + 1)) Complex) := by
  obtain ⟨s, hs, D, hD0, hDs, N, r, f, hN, hf, hmem, hbound, hNbound, hlow, hw⟩ :=
    OAI.PiExponent.FormalInterpolation.fixedData_canonical_strict_monic_power_certificate
      nu hnu d R e hR he hscale
  let w : Fin (d.m + 1) → Real := fun i =>
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i
  have hfinite :=
    OAI.PiExponent.FormalInterpolation.finite_adjoin_of_strict_monic_relations
      w
      (logarithmicCentersIdeal
        (fun j : Fin d.K => fun i =>
          (j.val : Complex) *
            MatrixArithmetic.rationalCenters
              (finiteNumerators d) (finiteDenominators d) i)
        (fun _ => e 0) e)
      s D N r f hN hf hmem hbound hNbound hlow hw
  refine ⟨s, hs, D, hD0, hDs, d.m + 1, f, hmem, ?_, ?_⟩
  · intro j a ha
    simpa [w] using hbound j a ha
  · simpa using hfinite
