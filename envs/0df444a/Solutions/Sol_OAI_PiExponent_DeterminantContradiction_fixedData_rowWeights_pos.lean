-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.fixedData_rowWeights_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:33:27.944448+00:00
-- url     : https://prove2.me/submissions/0c3cb84b-cb99-4683-af3a-acd6d3e6ed9e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu) :
    ∀ i : Fin (d.m + 1),
      0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [InterpolationMatrix.rowWeights] using d.v0_pos
  · change 0 < MatrixArithmetic.logWeights (finiteDenominators d) j /
      (d.base.theta : Real)
    rw [MatrixArithmetic.logWeights]
    change 0 < (Nat.ceil (Real.log (d.q j.val)) : Real) /
      (d.base.theta : Real)
    have hq_nat : 1 < d.q j.val := by
      have hq := (d.approximations j.val).1
      omega
    have hq : (1 : Real) < (d.q j.val : Real) := by
      exact_mod_cast hq_nat
    have hlog : 0 < Real.log (d.q j.val) := Real.log_pos hq
    have hceil : 0 < (Nat.ceil (Real.log (d.q j.val)) : Real) := by
      exact_mod_cast (Nat.ceil_pos.mpr hlog)
    exact div_pos hceil d.base.theta_pos