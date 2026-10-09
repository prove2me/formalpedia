-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_representative_scale_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T17:08:26.341804+00:00
-- url     : https://prove2.me/submissions/f9c3becf-037b-408c-ae6d-cf3dbf477278

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_rational_weight_vector_scale_exists

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu) :
    exists (R : Rat) (T : Fin d.m -> Nat) (e : Fin (d.m + 1) -> Nat),
      And (0 < R) (And (forall i : Fin (d.m + 1), 0 < e i)
        (And (forall i : Fin d.m,
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <=
          (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
          (forall i : Fin (d.m + 1), (R : Real) = (e i : Real) *
            InterpolationMatrix.rowWeights d.v0 d.base.theta
              (MatrixArithmetic.logWeights (finiteDenominators d)) i))) := by
  let w : Fin (d.m + 1) -> Real :=
    InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))
  have hw : forall i : Fin (d.m + 1), 0 < w i := by
    intro i
    exact Fin.cases d.v0_pos (fun j => by
      change 0 < (Nat.ceil (Real.log (d.q j.val)) : Real) / d.base.theta
      apply div_pos _ d.base.theta_pos
      have hx := d.x_one_le (j.val + 1)
      rw [d.x_log j.val] at hx
      have hceil : 0 < Nat.ceil (Real.log (d.q j.val)) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hx)
      exact_mod_cast hceil) i
  have hrat : forall i : Fin (d.m + 1), exists r : Rat, (r : Real) = w i := by
    intro i
    exact Fin.cases (show exists r : Rat, (r : Real) = d.v0 from ⟨d.v0, rfl⟩)
      (fun j => by
        refine ⟨(Nat.ceil (Real.log (d.q j.val)) : Rat) / d.base.theta, ?_⟩
        change (((Nat.ceil (Real.log (d.q j.val)) : Rat) / d.base.theta : Rat) : Real) =
          (Nat.ceil (Real.log (d.q j.val)) : Real) / (d.base.theta : Real)
        simp) i
  obtain ⟨R, T, e, hR, he, hT, hscale⟩ :=
    OAI.PiExponent.FormalInterpolation.rational_weight_vector_scale_exists w hw hrat
  exact ⟨R, T, e, hR, he, by simpa [w] using hT, by simpa [w] using hscale⟩
