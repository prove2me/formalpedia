-- Prove2me | solution 1 for GlobalTheory.OnePoint.algebraMap_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:22.041042+00:00
-- url     : https://prove2.me/submissions/5021f11e-f52f-4cfd-8f07-2ec5a24bf0b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution : algebraMap K K⸨X⸩ = HahnSeries.C := by
  ext1 c
  simp [HahnSeries.algebraMap_apply']
end GlobalTheory.OnePoint
