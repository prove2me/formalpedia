-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.tendsto_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:37.651598+00:00
-- url     : https://prove2.me/submissions/f649a0f0-4a32-4682-90f1-07ce2d9468bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole

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
theorem _root_.solution {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => r ^ (-s)) (𝓝[>] 1) (𝓝 (r ^ (-1 : ℝ))) :=
  ((Real.continuousAt_const_rpow hr.ne').comp (f := fun s : ℝ => -s)
    continuous_neg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
end GlobalTheory.KroneckerLimit
