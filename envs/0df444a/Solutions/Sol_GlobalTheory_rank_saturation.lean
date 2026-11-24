-- Prove2me | solution 1 for GlobalTheory.rank_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:05.619325+00:00
-- url     : https://prove2.me/submissions/003e5db3-54e2-4f32-b8e6-cf51d87a0c43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_isTorsion_saturation_quotient

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
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution (N : Submodule R M) :
    Module.rank R (saturation N) = Module.rank R N := by
  have h1 := rank_quotient_add_rank_of_isDomain (N.submoduleOf (saturation N))
  have h2 : Module.rank R (saturation N ⧸ N.submoduleOf (saturation N)) = 0 := by
    rw [rank_eq_zero_iff]
    intro y
    have ht := isTorsion_saturation_quotient N
    obtain ⟨⟨a, ha⟩, hay⟩ := @ht y
    exact ⟨a, nonZeroDivisors.ne_zero ha, hay⟩
  rw [h2, zero_add, (Submodule.submoduleOfEquivOfLe (le_saturation N)).rank_eq] at h1
  exact h1.symm
end GlobalTheory
