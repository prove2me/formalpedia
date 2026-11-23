-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.eventually_mem_Ioc_one_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:34.947225+00:00
-- url     : https://prove2.me/submissions/a5c34475-2e42-44da-a8e4-62aa06d2c9a9

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
theorem _root_.solution : ∀ᶠ s : ℝ in 𝓝[>] 1, 1 < s ∧ s ≤ 2 :=
  Ioc_mem_nhdsGT (by norm_num)
end GlobalTheory.KroneckerLimit
