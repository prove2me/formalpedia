-- Prove2me | solution 1 for GlobalTheory.RelIndexOfMap.mem_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:44.824465+00:00
-- url     : https://prove2.me/submissions/13623957-c58c-462f-afb9-119144b6ce1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap
namespace GlobalTheory.RelIndexOfMap
theorem _root_.solution {H : Type} [Group H] (J : Subgroup H) (h x : H) :
    x ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H → MulAut H) h)) J ↔
      h⁻¹ * x * h ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩
end GlobalTheory.RelIndexOfMap
