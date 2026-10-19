-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_subcritical_logarithmic_power_generation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:36:41.410263+00:00
-- url     : https://prove2.me/submissions/f16e4b89-8812-4968-a468-7b89121a2960
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_bounded_weight_span

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

-- Finite extraction preserves membership in the original generating set.
theorem OAI.PiExponent.FormalInterpolation.finite_subset_span_of_noetherian
    {A : Type*} [CommRing A] [IsNoetherianRing A] (U : Set A) :
    ∃ S : Finset A, (S : Set A) ⊆ U ∧
      Ideal.span (S : Set A) = Ideal.span U := by
  obtain ⟨S, hSU, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := A) U).mp
      (IsNoetherian.noetherian (Submodule.span A U))
  exact ⟨S, hSU, hspan.symm⟩

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ s : Nat, 0 < s ∧ ∃ D : Real, D < (s : Real) * (R : Real) ∧
      ∃ S : Finset (MvPolynomial (Fin (d.m + 1)) Complex),
        Ideal.span (S : Set (MvPolynomial (Fin (d.m + 1)) Complex)) =
          (logarithmicCentersIdeal
          (fun j : Fin d.K => fun i =>
            (j.val : Complex) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
          T e) ^ s ∧
        ∀ P ∈ S, ∀ a ∈ P.support,
          ∑ i, InterpolationMatrix.columnWeights d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) i * (a i : Real) ≤ D := by
  classical
  let I := logarithmicCentersIdeal
    (fun j : Fin d.K => fun i =>
      (j.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
    T e
  let w := InterpolationMatrix.columnWeights d.w0
    (MatrixArithmetic.logWeights (finiteDenominators d))
  obtain ⟨s, hs, D, hD, hspan⟩ :=
    OAI.PiExponent.FormalInterpolation.fixedData_subcritical_bounded_weight_span
      nu hnu d R T e hR he hT hscale
  let U : Set (MvPolynomial (Fin (d.m + 1)) Complex) :=
    {P | P ∈ I ^ s ∧ ∀ a ∈ P.support, ∑ i, w i * (a i : Real) ≤ D}
  have hU : Ideal.span U = I ^ s := hspan
  obtain ⟨S, hSU, hSspan⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_subset_span_of_noetherian U
  refine ⟨s, hs, D, hD, S, ?_, ?_⟩
  · exact hSspan.trans hU
  · intro P hP a ha
    exact (hSU hP).2 a ha
