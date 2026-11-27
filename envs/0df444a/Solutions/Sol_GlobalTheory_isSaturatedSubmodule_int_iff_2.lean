-- Prove2me | solution 2 for GlobalTheory.isSaturatedSubmodule_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:38.166992+00:00
-- url     : https://prove2.me/submissions/03c618c7-3388-4b42-988d-6d6050e479eb

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
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution {A : Type*} [AddCommGroup A] (N : Submodule ℤ A) :
    IsSaturatedSubmodule N ↔ N.toAddSubgroup.NSMulSaturated := by
  rw [isSaturatedSubmodule_iff, AddSubgroup.saturated_iff_zsmul]
  constructor
  · intro h n g hg
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (h n hn g hg)
  · intro h a ha x hx
    exact (h a x hx).resolve_left ha
end GlobalTheory
