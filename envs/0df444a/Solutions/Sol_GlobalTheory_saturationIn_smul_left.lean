-- Prove2me | solution 1 for GlobalTheory.saturationIn_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:15.250855+00:00
-- url     : https://prove2.me/submissions/2bad3ac1-cb0c-43c6-9576-b9bf9a9a1fe9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_smul_inf_restrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable {K}
namespace GlobalTheory
theorem _root_.solution (M N : Submodule R V) {c : K} (hc : c ≠ 0) :
    saturationIn (c • M) N = c • saturationIn M N := by
  rw [saturationIn_eq_inf_span K, saturationIn_eq_inf_span K, smul_inf_restrictScalars M _ hc]
end GlobalTheory
