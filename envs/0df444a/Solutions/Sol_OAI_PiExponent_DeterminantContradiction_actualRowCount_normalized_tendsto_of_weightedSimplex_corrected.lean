-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto_of_weightedSimplex_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:44:04.214266+00:00
-- url     : https://prove2.me/submissions/53f53701-f827-478d-9c7d-fe6843fa2829

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu)
    (h : Tendsto
      (fun H : Real =>
        ((strictWeightedSimplex
          (InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d))) H).card : Real) /
          H ^ (d.m + 1)) atTop
      (nhds (1 /
        (((d.m + 1).factorial : Real) *
          ∏ i : Fin (d.m + 1),
            InterpolationMatrix.rowWeights d.v0 d.base.theta
              (MatrixArithmetic.logWeights (finiteDenominators d)) i)))) :
    Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) atTop
      (nhds ((d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by
  let w : Fin d.m → Real := MatrixArithmetic.logWeights (finiteDenominators d)
  have hw : ∀ i, 0 < w i := by
    intro i
    dsimp [w, MatrixArithmetic.logWeights, finiteDenominators]
    have hq : 2 ≤ d.q i.val := (d.approximations i.val).1
    have hq' : 1 < d.q i.val := lt_of_lt_of_le (by decide : 1 < 2) hq
    have hqreal : (1 : Real) < (d.q i.val : Real) := by exact_mod_cast hq'
    exact_mod_cast (Nat.ceil_pos.mpr (Real.log_pos hqreal))
  have hprod : 0 < ∏ i : Fin d.m, w i := Finset.prod_pos fun i hi => hw i
  have hrowprod :
      (∏ i : Fin (d.m + 1),
        InterpolationMatrix.rowWeights d.v0 d.base.theta w i) =
        (d.v0 : Real) * (∏ i : Fin d.m, w i) / (d.base.theta : Real) ^ d.m := by
    simp [InterpolationMatrix.rowWeights, Fin.prod_univ_succ,
      Finset.prod_div_distrib]
    <;> ring
  have hcoeff :
      (d.K : Real) *
        (1 /
          (((d.m + 1).factorial : Real) *
            ∏ i : Fin (d.m + 1),
              InterpolationMatrix.rowWeights d.v0 d.base.theta w i)) =
      (d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, w i) := by
    rw [hrowprod]
    field_simp [ne_of_gt d.v0_pos, ne_of_gt d.base.theta_pos,
      ne_of_gt hprod]
    <;> ring
  have hconst : Tendsto (fun _ : Real => (d.K : Real)) atTop (nhds (d.K : Real)) :=
    tendsto_const_nhds
  have hscaled := hconst.mul h
  have hcard (H : Real) :
      (actualRowCount d H : Real) =
        (d.K : Real) *
          ((strictWeightedSimplex (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H).card : Real) := by
    simp [actualRowCount, Row, InterpolationMatrix.Row, w, Fintype.card_prod]
  have hfun :
      (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) =
        (fun H : Real => (d.K : Real) *
          (((strictWeightedSimplex (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H).card : Real) /
            H ^ (d.m + 1))) := by
    funext H
    rw [hcard]
    ring
  have hscaled' : Tendsto
      (fun H : Real => (d.K : Real) *
        (((strictWeightedSimplex (InterpolationMatrix.rowWeights d.v0 d.base.theta w) H).card : Real) /
          H ^ (d.m + 1))) atTop
      (nhds ((d.K : Real) *
        (1 / (((d.m + 1).factorial : Real) *
          ∏ i : Fin (d.m + 1),
            InterpolationMatrix.rowWeights d.v0 d.base.theta w i)))) := by
    simpa only [Pi.mul_apply] using hscaled
  rw [hfun]
  rw [← hcoeff]
  exact hscaled'