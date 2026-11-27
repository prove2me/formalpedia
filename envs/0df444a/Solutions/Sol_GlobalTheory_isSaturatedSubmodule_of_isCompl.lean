-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_of_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:47.70138+00:00
-- url     : https://prove2.me/submissions/4676cf07-b9be-4c72-b76e-a209e43d2c08

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
theorem _root_.solution [IsDomain R] [Module.IsTorsionFree R M]
    {N P : Submodule R M} (h : IsCompl N P) : IsSaturatedSubmodule N := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  have hxs : x ∈ N ⊔ P := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.1 hxs
  have hap : a • p ∈ N := by
    have e : a • p = a • (n + p) - a • n := by rw [smul_add, add_sub_cancel_left]
    rw [e]
    exact N.sub_mem hx (N.smul_mem a hn)
  have h0 : a • p ∈ N ⊓ P := Submodule.mem_inf.2 ⟨hap, P.smul_mem a hp⟩
  rw [h.inf_eq_bot, Submodule.mem_bot] at h0
  rw [(smul_eq_zero_iff_right ha).1 h0, add_zero]
  exact hn
end GlobalTheory
