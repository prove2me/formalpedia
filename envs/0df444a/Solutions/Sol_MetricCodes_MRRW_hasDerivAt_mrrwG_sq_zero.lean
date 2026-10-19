-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_mrrwG_sq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/2546b488-72c9-461b-82d4-a0119767afb2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_negMulLog_inverseDegree_zero
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_inverseDegree_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution :
    HasDerivAt
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) 0 0 := by
  have hcomplement :
      HasDerivAt
        (fun r : ℝ => Real.negMulLog (1 - inverseDegree r)) 0 0 := by
    have hinner :
        HasDerivAt (fun r : ℝ => 1 - inverseDegree r) 0 0 := by
      change
        HasDerivAt
          ((fun _ : ℝ => (1 : ℝ)) - inverseDegree) 0 0
      simpa using
        (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
          hasDerivAt_inverseDegree_zero
    have houter :
        HasDerivAt Real.negMulLog (-1) (1 - inverseDegree 0) := by
      simpa [inverseDegree] using
        Real.hasDerivAt_negMulLog (by norm_num : (1 : ℝ) ≠ 0)
    simpa [Function.comp_def] using houter.comp 0 hinner
  have hentropy :
      HasDerivAt
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2)
        0 0 := by
    simpa [Function.comp_def] using
      (hasDerivAt_negMulLog_inverseDegree_zero.add
        hcomplement).div_const (Real.log 2)
  have hfunctions :
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) =
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2) := by
    funext r
    unfold MetricCodes.Johnson.mrrwG inverseDegree
    rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [hfunctions]
  exact hentropy
end MetricCodes.MRRW
