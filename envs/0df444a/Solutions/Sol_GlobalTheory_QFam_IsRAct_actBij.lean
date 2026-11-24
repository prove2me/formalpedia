-- Prove2me | solution 1 for GlobalTheory.QFam.IsRAct.actBij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:44.590805+00:00
-- url     : https://prove2.me/submissions/88891534-0c5f-40fa-acfe-05740d853fba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups ModularForm
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace IsRAct
theorem _root_.solution {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by
  obtain ⟨hone, hmul⟩ := h
  intro γ
  refine Function.bijective_iff_has_inverse.mpr ⟨fun i => act i γ⁻¹, fun i => ?_, fun i => ?_⟩
  · show act (act i γ) γ⁻¹ = i
    rw [hmul, mul_inv_cancel, hone]
  · show act (act i γ⁻¹) γ = i
    rw [hmul, inv_mul_cancel, hone]
end IsRAct
end GlobalTheory.QFam
