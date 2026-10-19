-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:10:08.895896+00:00
-- url     : https://prove2.me/submissions/f5d36bab-23bf-40ac-b01c-b5d1cbc3442f

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H,
      ∑ i : Fin d.m,
        MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) =
      (actualRowCount d H : ℝ) * H * actualMean d H := by
  classical
  have hzero : (fun _ : Fin (d.m + 1) => 0) ∈
      OAI.PiExponent.strictWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    simp [OAI.PiExponent.strictWeightedSimplex,
      OAI.PiExponent.realWeightedSimplex, hH.le, hH]
  let r : Row d H :=
    ⟨⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 1) d.K_pos⟩,
      ⟨(fun _ : Fin (d.m + 1) => 0), hzero⟩⟩
  have hcard : 0 < actualRowCount d H :=
    Fintype.card_pos_iff.mpr ⟨r⟩
  have hsum :
      (∑ r : Row d H,
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) =
        MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H := by
    unfold MatrixArithmetic.rowWeightedSum
    refine Finset.sum_congr rfl ?_
    intro r hr
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  rw [hsum]
  unfold actualMean actualRowCount MatrixArithmetic.meanRowWeight
  have hden :
      ((Fintype.card (Row d H) : ℝ) * H) ≠ 0 :=
    ne_of_gt (mul_pos (by exact_mod_cast hcard) hH)
  calc
    _ = (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H /
          ((Fintype.card (Row d H) : ℝ) * H)) *
          ((Fintype.card (Row d H) : ℝ) * H) :=
      (div_mul_cancel₀ _ hden).symm
    _ = _ := mul_comm _ _