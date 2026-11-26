-- Prove2me | solution 1 for GlobalTheory.saturation_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:29:46.861796+00:00
-- url     : https://prove2.me/submissions/fb71289b-7a48-4904-b525-d787914a5949

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
theorem _root_.solution {M N : Submodule R V} (h : N ≤ M) :
    saturation (saturationIn M N) = saturation N := by
  first
    | (unfold GlobalTheory.saturationIn
       rw [GlobalTheory.saturation_inf, GlobalTheory.saturation_saturation]
       exact inf_eq_right.2 (GlobalTheory.saturation_mono h))

