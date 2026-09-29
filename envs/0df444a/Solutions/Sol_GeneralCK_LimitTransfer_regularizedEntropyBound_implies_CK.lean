-- Prove2me | solution 1 for GeneralCK.LimitTransfer.regularizedEntropyBound_implies_CK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:23:27.392324+00:00
-- url     : https://prove2.me/submissions/d6552f3c-563f-45e8-9ac8-08a524a1bf0e

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_information
import Definitions.Def_GeneralCK_limit_transfer
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_Information_mutualInformation_eq
import Theorems.Thm_GeneralCK_Regularization_CK_of_open_lower_half

open scoped BigOperators
namespace GeneralCK
open scoped BigOperators



























theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK
namespace GeneralCK.LimitTransfer
end GeneralCK.LimitTransfer

open GeneralCK GeneralCK.LimitTransfer in
open scoped BigOperators in
theorem solution (hBound : RegularizedEntropyBound) :
    GeneralCourtadeKumar := by
  apply Regularization.CK_of_open_lower_half
  intro n f p hp hp'
  have hleft : Continuous (fun eps : ℝ => H (eps + p - 2 * eps * p)) := by
    apply H_continuous.comp
    fun_prop
  have hright : Continuous (fun eps : ℝ =>
      Information.cubeWeight n * (∑ y, H (regularizedPosterior f p eps y)) +
        1 - H (regularizedMean f eps)) := by
    apply Continuous.sub
    · apply Continuous.add _ continuous_const
      apply Continuous.const_mul
      apply continuous_finsetSum
      intro y _
      apply H_continuous.comp
      unfold regularizedPosterior
      fun_prop
    · apply H_continuous.comp
      unfold regularizedMean
      fun_prop
  have hz : (0 : ℝ) ∈ closure (Set.Ioo 0 (1 / 2 : ℝ)) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1 / 2)]
    exact ⟨le_rfl, by norm_num⟩
  have hlim := ContinuousWithinAt.closure_le hz hleft.continuousAt.continuousWithinAt
    hright.continuousAt.continuousWithinAt
    (fun eps heps => hBound n f eps p heps.1 heps.2 hp hp')
  simp only [regularizedPosterior, regularizedMean, mul_zero, zero_mul, sub_zero,
    one_mul, zero_add] at hlim
  rw [Information.mutualInformation_eq]
  linarith
