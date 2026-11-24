-- Prove2me | solution 1 for GlobalTheory.T.exists_pow_mul_eq_of_algebraMap_localizationAway_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:54.2511+00:00
-- url     : https://prove2.me/submissions/cf4531a8-ca20-4afa-b833-7fbf2571deb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAway
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Theorems.Thm_GlobalTheory_algHom_eq_mul_pow_of_eq_localizationAway


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
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  first | exact @GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | exact GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway | (intros; apply GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway <;> assumption)
end _root_.GlobalTheory.T
