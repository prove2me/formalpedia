-- Prove2me | solution 1 for GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:25.80557+00:00
-- url     : https://prove2.me/submissions/ba08cf46-8600-4342-8e5e-917eb29d5f50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMulStatement
import Theorems.Thm_GlobalTheory_hasSum_cosets_smaller_level_relIndex_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  first | exact @GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | exact GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | (intros; apply GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul <;> assumption)
end _root_.GlobalTheory.T
