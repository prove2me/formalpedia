-- Prove2me | solution 1 for GlobalTheory.DualFrameSpan.pairing_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:48.662081+00:00
-- url     : https://prove2.me/submissions/f81b43b9-45ee-41d4-80c0-d32f5cca2788

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation
import Theorems.Thm_GlobalTheory_DualFrameSpan_eq_zero_of_trace_adjoint_comp_self
import Theorems.Thm_GlobalTheory_DualFrameSpan_pairing_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace GlobalTheory.DualFrameSpan
theorem _root_.solution (W : Submodule ℂ (H →ₗ[ℂ] H))
    (hW : ∀ X ∈ W, LinearMap.adjoint X ∈ W) : (pairing W).Nondegenerate := by
  have key : ∀ y : W, (∀ x : W, pairing W x y = 0) → y = 0 := by
    intro y hy
    have := hy ⟨LinearMap.adjoint (y : H →ₗ[ℂ] H), hW _ y.2⟩
    rw [pairing_apply] at this
    exact Subtype.ext (eq_zero_of_trace_adjoint_comp_self _ this)
  refine ⟨fun x hx => key x (fun y => ?_), fun y hy => key y hy⟩
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact hx y
end GlobalTheory.DualFrameSpan
