-- Prove2me | solution 1 for GlobalTheory.GelfandTrick.InDoubleCoset.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:18.308188+00:00
-- url     : https://prove2.me/submissions/e026c8cf-1fe2-4e2c-9142-38f7f649bcf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GelfandTrick
variable {G : Type} [Group G]
namespace GlobalTheory.GelfandTrick
namespace InDoubleCoset
theorem _root_.solution {J : Subgroup G} {a y z j₁ j₂ : G} (h : InDoubleCoset J a y)
    (h₁ : j₁ ∈ J) (h₂ : j₂ ∈ J) (hz : z = j₁ * y * j₂) : InDoubleCoset J a z := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h
  exact ⟨j₁ * k₁, J.mul_mem h₁ hk₁, k₂ * j₂, J.mul_mem hk₂ h₂, by rw [hz]; group⟩
end InDoubleCoset
end GlobalTheory.GelfandTrick
