-- Prove2me | solution 1 for GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:14.585905+00:00
-- url     : https://prove2.me/submissions/827630f4-3bf8-48fc-8334-b33fda683959

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatOfLocalRetractionsModMaximalIdealPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatOfLocalRetractionsModMaximalIdealPowStatement
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_flat_of_retractions_mod_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], (∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _) → (∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) → φ.Flat := by
  first | exact @GlobalTheory.flat_of_retractions_mod_pow | exact GlobalTheory.flat_of_retractions_mod_pow | (intros; apply GlobalTheory.flat_of_retractions_mod_pow <;> assumption)
end _root_.GlobalTheory.T
