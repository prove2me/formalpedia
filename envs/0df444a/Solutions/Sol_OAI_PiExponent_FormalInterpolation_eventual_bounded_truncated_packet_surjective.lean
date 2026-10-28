-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_bounded_truncated_packet_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T20:54:16.217027+00:00
-- url     : https://prove2.me/submissions/d1ce039e-55ef-411c-87d2-5e4d473b3156
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.NormNum
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_logarithmic_power_generation_from_blowup
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_colength_and_truncated_packet_lifting
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_subcritical_power_generators

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

-- The two Open dependencies have existing platform identities. The eventual
-- representatives lemma is recorded Proved in the supplied research snapshot.
-- Only ideal-power inclusion in the packet kernel is used, never its converse.
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
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Function.Surjective
        (fun P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)) =>
          truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P.val) := by
  classical
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  let r := MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  let c : Fin d.K → Fin d.m → Complex := fun j i => (j.val : Complex) * r i
  let I := logarithmicCentersIdeal c T e
  have hRreal : 0 < (R : Real) := by exact_mod_cast hR
  have hw : ∀ i : Fin d.m, 0 < w i := by
    intro i
    have hx := d.x_one_le (i.val + 1)
    rw [d.x_log i.val] at hx
    exact lt_of_lt_of_le zero_lt_one hx
  let i₀ : Fin d.m := ⟨0, d.m_pos⟩
  have hp : (d.p 0 : Complex) ≠ 0 := by
    exact_mod_cast (d.approximations 0).2.1
  have hqnat : d.q 0 ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (d.approximations 0).1)
  have hq : (d.q 0 : Complex) ≠ 0 := by exact_mod_cast hqnat
  have hr : r i₀ ≠ 0 := by
    change 2 * Complex.I * (d.p 0 : Complex) / (d.q 0 : Complex) ≠ 0
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  obtain ⟨hfinite, hlift⟩ :=
    finite_colength_and_truncated_packet_lifting
      d.K d.v0 d.base.theta w (R : Real) e T r hRreal he hscale ⟨i₀, hr⟩
  obtain ⟨s, hs, D, hD, S, hspan, hdeg⟩ :=
    fixedData_subcritical_logarithmic_power_generation_from_blowup
      nu hnu d R T e hR he hT hscale
  obtain ⟨N, hN⟩ :=
    eventual_representatives_of_subcritical_power_generators
      d.w0 w d.w0_pos hw I hfinite (R : Real) hRreal
      s hs D hD S hspan hdeg
  refine ⟨N, ?_⟩
  intro n hn f
  obtain ⟨P, hP⟩ := hlift n f
  obtain ⟨Q, hQ⟩ := hN n hn P
  exact ⟨Q, hP Q.val hQ⟩
