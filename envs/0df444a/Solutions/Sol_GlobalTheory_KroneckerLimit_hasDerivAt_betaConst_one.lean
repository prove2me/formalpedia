-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.hasDerivAt_betaConst_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:35.068628+00:00
-- url     : https://prove2.me/submissions/4ab5331b-01dc-44ee-acc3-d2850ceef7b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution : HasDerivAt betaConst (-2 * π * Real.log 2) 1 := by
  have h1 : HasDerivAt Real.Gamma (-√π * (Real.eulerMascheroniConstant + 2 * Real.log 2)) (1 - 1 / 2) := by
    convert Real.hasDerivAt_Gamma_one_half using 1
    norm_num
  have h2 := ((h1.comp_sub_const 1 (1 / 2)).const_mul √π).div Real.hasDerivAt_Gamma_one
    (by rw [Real.Gamma_one]; exact one_ne_zero)
  have hp := Real.mul_self_sqrt Real.pi_pos.le
  have hf : betaConst = (fun y => √π * Real.Gamma (y - 1 / 2)) / Real.Gamma := by
    funext y
    rfl
  rw [hf]
  refine h2.congr_deriv ?_
  rw [Real.Gamma_one, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
  linear_combination (-(2 * Real.log 2)) * hp
end GlobalTheory.KroneckerLimit
