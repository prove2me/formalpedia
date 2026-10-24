-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.row_volume_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:19:42.328759+00:00
-- url     : https://prove2.me/submissions/8bacae92-ab5c-45a4-872c-5050e8e9f5f4

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (d.K : ℝ) *
        (1 / ((Nat.factorial (d.m + 1) : ℝ) *
          ∏ i : Fin (d.m + 1),
            OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
              (OAI.PiExponent.MatrixArithmetic.logWeights
                (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i)) =
      ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) /
        ((Nat.factorial (d.m + 1) : ℝ) * (d.v0 : ℝ) *
          ∏ i : Fin d.m, d.x (i.val + 1)) := by
  have hθ : (d.base.theta : ℝ) ≠ 0 := d.base.theta_pos.ne'
  have hv : (d.v0 : ℝ) ≠ 0 := d.v0_pos.ne'
  have hx : (∏ i : Fin d.m, d.x (i.val + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (lt_of_lt_of_le one_pos (d.x_one_le _)).ne'
  have hf : (Nat.factorial (d.m + 1) : ℝ) ≠ 0 := by positivity
  have hp : ∏ i : Fin (d.m + 1),
      OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
        (OAI.PiExponent.MatrixArithmetic.logWeights
          (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) i =
      (d.v0 : ℝ) * ((∏ i : Fin d.m, d.x (i.val + 1)) / (d.base.theta : ℝ) ^ d.m) := by
    rw [Fin.prod_univ_succ]
    simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [d.x_log]
    rfl
  rw [hp]
  field_simp
