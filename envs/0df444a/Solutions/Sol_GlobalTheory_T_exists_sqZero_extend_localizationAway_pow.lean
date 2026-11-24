-- Prove2me | solution 1 for GlobalTheory.T.exists_sqZero_extend_localizationAway_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:03.174807+00:00
-- url     : https://prove2.me/submissions/a66a1265-b9a0-4795-9f0f-7ba3fddf9985

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Theorems.Thm_GlobalTheory_SecGlue_exists_sqZero_extend_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  first | exact @GlobalTheory.SecGlue.exists_sqZero_extend_pow | exact GlobalTheory.SecGlue.exists_sqZero_extend_pow | (intros; apply GlobalTheory.SecGlue.exists_sqZero_extend_pow <;> assumption)
end _root_.GlobalTheory.T
