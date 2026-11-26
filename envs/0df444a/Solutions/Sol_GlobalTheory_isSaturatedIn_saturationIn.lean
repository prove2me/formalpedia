-- Prove2me | solution 1 for GlobalTheory.isSaturatedIn_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:29:47.53658+00:00
-- url     : https://prove2.me/submissions/afad12ee-767b-434c-a6e6-1945c8a0941c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
theorem _root_.solution (M N : Submodule R V) : IsSaturatedIn M (saturationIn M N) := by
  first
    | (unfold GlobalTheory.IsSaturatedIn GlobalTheory.saturationIn
       rw [GlobalTheory.saturation_inf, GlobalTheory.saturation_saturation, ← inf_assoc]
       congr 1
       exact inf_eq_left.2 (GlobalTheory.le_saturation M))

