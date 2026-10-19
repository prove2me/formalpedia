-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_bounded_packet_representatives_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:56:17.73745+00:00
-- url     : https://prove2.me/submissions/cd2ee0c3-ac6d-4b75-991c-1041c15aa020
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_subcritical_power_generators
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_logarithmic_power_generation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_colength_and_truncated_packet_lifting
import Mathlib.Tactic.NormNum

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

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
    ∃ N : Nat, ∀ n : Nat, N ≤ n → Function.Surjective
      (fun Q : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)) =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T Q.val) := by
  classical
  have hRreal : (0 : Real) < (R : Real) := by exact_mod_cast hR
  have hw : ∀ i : Fin d.m,
      0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    have hx := d.x_one_le (i.val + 1)
    rw [d.x_log i.val] at hx
    change (0 : Real) < (Nat.ceil (Real.log (d.q i.val)) : Real)
    exact lt_of_lt_of_le zero_lt_one hx
  have hr : ∃ i : Fin d.m,
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
    let i : Fin d.m := ⟨0, lt_of_lt_of_le Nat.zero_lt_one d.m_pos⟩
    refine ⟨i, ?_⟩
    have hp : (d.p i.val : Complex) ≠ 0 := by
      exact_mod_cast (d.approximations i.val).2.1
    have hq : (d.q i.val : Complex) ≠ 0 := by
      exact_mod_cast (show d.q i.val ≠ 0 by
        exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
          (d.approximations i.val).1))
    change 2 * Complex.I * (d.p i.val : Complex) / (d.q i.val : Complex) ≠ 0
    exact div_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  obtain ⟨hfinite, hlift⟩ :=
    finite_colength_and_truncated_packet_lifting d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) (R : Real) e T
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      hRreal he hscale hr
  obtain ⟨s, hs, D, hD, S, hspan, hdeg⟩ :=
    fixedData_subcritical_logarithmic_power_generation nu hnu d R T e hR he hT hscale
  obtain ⟨N, hN⟩ :=
    eventual_representatives_of_subcritical_power_generators d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) d.w0_pos hw
      (logarithmicCentersIdeal
        (fun j : Fin d.K => fun i => (j.val : Complex) *
          MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
        T e)
      hfinite (R : Real) hRreal s hs D hD S hspan hdeg
  refine ⟨N, ?_⟩
  intro n hn f
  obtain ⟨P, hP⟩ := hlift n f
  obtain ⟨Q, hQ⟩ := hN n hn P
  exact ⟨Q, hP Q.val hQ⟩
