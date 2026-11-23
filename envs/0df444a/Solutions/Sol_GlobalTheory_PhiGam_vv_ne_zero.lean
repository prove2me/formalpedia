-- Prove2me | solution 1 for GlobalTheory.PhiGam.vv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:08.725337+00:00
-- url     : https://prove2.me/submissions/2aed8fb2-6d66-4d95-af7b-a1a46fc0e4bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable (k : Type) [Field k]
namespace GlobalTheory.PhiGam
theorem _root_.solution : vv k ≠ 0 := by simp [vv]
end GlobalTheory.PhiGam
