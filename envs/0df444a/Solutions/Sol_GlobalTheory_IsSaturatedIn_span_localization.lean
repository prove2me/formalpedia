-- Prove2me | solution 1 for GlobalTheory.IsSaturatedIn.span_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:49.236832+00:00
-- url     : https://prove2.me/submissions/9a20ebbe-07f6-4854-a311-a3a55af3fbbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_span_localization_saturationIn

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
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]
include p
namespace GlobalTheory
namespace IsSaturatedIn
theorem _root_.solution (hp : p ≤ R⁰) {M N : Submodule R V}
    (h : IsSaturatedIn M N) :
    IsSaturatedIn (Submodule.span S (M : Set V)) (Submodule.span S (N : Set V)) := by
  unfold IsSaturatedIn
  rw [← span_localization_saturationIn S p hp, h.saturationIn_eq]
end IsSaturatedIn
end GlobalTheory
