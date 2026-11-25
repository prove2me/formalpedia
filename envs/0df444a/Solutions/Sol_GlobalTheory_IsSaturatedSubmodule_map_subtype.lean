-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.map_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:54:43.999815+00:00
-- url     : https://prove2.me/submissions/5f541d69-40cb-45d3-b2b4-4b06fff9f8bd

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
namespace IsSaturatedSubmodule
theorem _root_.solution {P : Submodule R M} {N : Submodule R P}
    (hN : IsSaturatedSubmodule N) (hP : IsSaturatedSubmodule P) :
    IsSaturatedSubmodule (N.map P.subtype) := by
  rw [isSaturatedSubmodule_iff'] at hN
  rw [isSaturatedSubmodule_iff'] at hP
  rw [isSaturatedSubmodule_iff']
  intro a ha x hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
  have haxP : a • x ∈ P := by
    rw [← hyx]
    exact y.2
  have hxP : x ∈ P := hP a ha x haxP
  have hy' : a • (⟨x, hxP⟩ : P) = y := Subtype.ext (by simpa using hyx.symm)
  refine Submodule.mem_map.2 ⟨⟨x, hxP⟩, hN a ha _ ?_, rfl⟩
  rw [hy']
  exact hy
end IsSaturatedSubmodule
end GlobalTheory
