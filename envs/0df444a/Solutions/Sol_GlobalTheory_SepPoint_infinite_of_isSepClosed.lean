-- Prove2me | solution 1 for GlobalTheory.SepPoint.infinite_of_isSepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:39.141043+00:00
-- url     : https://prove2.me/submissions/62233466-6613-4ea1-b704-9cc962b83d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SepPoint
namespace GlobalTheory.SepPoint
theorem _root_.solution (Ω : Type) [Field Ω] [IsSepClosed Ω] : Infinite Ω := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  haveI : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  exact h.false.elim
end GlobalTheory.SepPoint
