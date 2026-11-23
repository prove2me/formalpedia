-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.betaConst_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:35.000053+00:00
-- url     : https://prove2.me/submissions/8104d9c5-9fb6-4578-bff0-b3dcc044a844

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
theorem _root_.solution : betaConst 1 = π := by
  unfold betaConst
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq, Real.Gamma_one, div_one,
    Real.mul_self_sqrt Real.pi_pos.le]
end GlobalTheory.KroneckerLimit
