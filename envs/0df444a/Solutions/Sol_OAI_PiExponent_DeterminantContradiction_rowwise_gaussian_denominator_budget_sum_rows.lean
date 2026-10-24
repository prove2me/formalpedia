-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.rowwise_gaussian_denominator_budget_sum_rows
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:24:19.695266+00:00
-- url     : https://prove2.me/submissions/2f5cfdce-e28f-420f-a88b-d8a58c43345d

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution {nu : Real} (d : FixedData nu) (H : Real) (hH : 0 < H)
    (scale : Row d H → Nat)
    (hrow : ∀ ρ : Row d H,
      Real.log (scale ρ : Real) ≤
        H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
          MatrixArithmetic.logWeights (finiteDenominators d) i) +
          H * d.arithmeticError) :
    (∑ ρ : Row d H, Real.log (scale ρ : Real)) ≤
      ((actualRowCount d H : Real) * H) *
        (1 - actualMean d H + d.arithmeticError) := by
  classical
  have hH0 : 0 ≤ H := le_of_lt hH
  have hzero :
      (fun _ : Fin (d.m + 1) => 0) ∈
        strictWeightedSimplex
          (InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d))) H := by
    simp [strictWeightedSimplex, realWeightedSimplex, hH0, hH]
  have hrows : Nonempty (Row d H) := by
    refine ⟨⟨⟨0, ?_⟩, ⟨(fun _ : Fin (d.m + 1) => 0), hzero⟩⟩⟩
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) d.K_pos
  have hcard : 0 < actualRowCount d H := by
    unfold actualRowCount
    exact Fintype.card_pos_iff.mpr hrows
  have hden : (actualRowCount d H : Real) * H ≠ 0 :=
    ne_of_gt (mul_pos (Nat.cast_pos.mpr hcard) hH)
  have hden' : (Fintype.card (Row d H) : Real) * H ≠ 0 := by
    simpa [actualRowCount] using hden
  have hmean :
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H =
        actualMean d H * ((actualRowCount d H : Real) * H) := by
    change
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H =
        (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
            (finiteDenominators d) H /
          ((Fintype.card (Row d H) : Real) * H)) *
            ((Fintype.card (Row d H) : Real) * H)
    rw [div_mul_cancel₀ _ hden']
  have hsum :
      (∑ ρ : Row d H, Real.log (scale ρ : Real)) ≤
        (actualRowCount d H : Real) * H -
          MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
            (finiteDenominators d) H +
          ((actualRowCount d H : Real) * H) * d.arithmeticError := by
    calc
      (∑ ρ : Row d H, Real.log (scale ρ : Real)) ≤
          ∑ ρ : Row d H,
            (H - (∑ i : Fin d.m, (ρ.2.1 i.succ : Real) *
                MatrixArithmetic.logWeights (finiteDenominators d) i) +
              H * d.arithmeticError) :=
        Finset.sum_le_sum (fun ρ _ => hrow ρ)
      _ = (actualRowCount d H : Real) * H -
            MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
              (finiteDenominators d) H +
            ((actualRowCount d H : Real) * H) * d.arithmeticError := by
        simp [actualRowCount, MatrixArithmetic.rowWeightedSum,
          Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring
  calc
    (∑ ρ : Row d H, Real.log (scale ρ : Real)) ≤
        (actualRowCount d H : Real) * H -
          MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
            (finiteDenominators d) H +
          ((actualRowCount d H : Real) * H) * d.arithmeticError := hsum
    _ = ((actualRowCount d H : Real) * H) *
        (1 - actualMean d H + d.arithmeticError) := by
      rw [hmean]
      ring
