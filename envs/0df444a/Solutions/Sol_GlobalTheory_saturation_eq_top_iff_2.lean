-- Prove2me | solution 2 for GlobalTheory.saturation_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:26.490481+00:00
-- url     : https://prove2.me/submissions/981a94d2-c413-408a-8e91-0cfd283c25e4

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
theorem _root_.solution {N : Submodule R M} :
    saturation N = ⊤ ↔ Module.IsTorsion R (M ⧸ N) := by
  rw [eq_top_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact h (Submodule.mem_top (x := x))
  · intro h x _
    exact @h (N.mkQ x)
end GlobalTheory
