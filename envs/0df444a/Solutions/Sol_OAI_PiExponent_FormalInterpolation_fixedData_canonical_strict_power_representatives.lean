-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_strict_power_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:57:04.325718+00:00
-- url     : https://prove2.me/submissions/af186c64-3ee5-494e-98bf-e72cb2c3f1d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_power_representatives_of_finite_adjoin
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_canonical_subcritical_finite_adjoin

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu)
    (R : Rat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∃ delta : Real, 0 < delta ∧ delta < (R : Real) ∧
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∀ P : MvPolynomial (Fin (d.m + 1)) Complex,
          ∃ Q : MvPolynomial (Fin (d.m + 1)) Complex,
            P - Q ∈ (logarithmicCentersIdeal
              (fun j : Fin d.K => fun i =>
                (j.val : Complex) *
                  MatrixArithmetic.rationalCenters
                    (finiteNumerators d) (finiteDenominators d) i)
              (fun _ => e 0) e) ^ n ∧
            ∀ a ∈ Q.support,
              ∑ i, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                  (a i : Real) ≤ (n : Real) * delta := by
  obtain ⟨s, hs, D, hD, hstrict, k, f, hmem, hweight, hfinite⟩ :=
    fixedData_canonical_subcritical_finite_adjoin nu hnu d R e hR he hscale
  obtain ⟨B, hB, hrep⟩ :=
    power_representatives_of_finite_adjoin
      (InterpolationMatrix.columnWeights d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)))
      (logarithmicCentersIdeal
        (fun j : Fin d.K => fun i =>
          (j.val : Complex) *
            MatrixArithmetic.rationalCenters
              (finiteNumerators d) (finiteDenominators d) i)
        (fun _ => e 0) e)
      s hs D hD f hmem hweight hfinite
  have hsReal : (0 : Real) < (s : Real) := Nat.cast_pos.mpr hs
  have hRReal : (0 : Real) < (R : Real) := Rat.cast_pos.mpr hR
  have hslope : D / (s : Real) < (R : Real) := by
    apply (div_lt_iff₀ hsReal).mpr
    simpa only [mul_comm] using hstrict
  have hslope_nonneg : 0 ≤ D / (s : Real) := div_nonneg hD hsReal.le
  let delta : Real := (D / (s : Real) + (R : Real)) / 2
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    linarith
  have hdelta_lt : delta < (R : Real) := by
    dsimp [delta]
    linarith
  have hgap : 0 < delta - D / (s : Real) := by
    dsimp [delta]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (B / (delta - D / (s : Real)))
  refine ⟨delta, hdelta_pos, hdelta_lt, N, ?_⟩
  intro n hn P
  obtain ⟨Q, hQ, hQweight⟩ := hrep n P
  refine ⟨Q, hQ, ?_⟩
  intro a ha
  have hNn : (N : Real) ≤ (n : Real) := Nat.cast_le.mpr hn
  have hquot : B / (delta - D / (s : Real)) ≤ (n : Real) :=
    le_trans hN.le hNn
  have hBbound : B ≤ (n : Real) * (delta - D / (s : Real)) :=
    (div_le_iff₀ hgap).mp hquot
  calc
    _ ≤ (n : Real) * (D / (s : Real)) + B := hQweight a ha
    _ ≤ (n : Real) * delta := by nlinarith
