-- Prove2me | solution 1 for GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:46.907055+00:00
-- url     : https://prove2.me/submissions/ae167ec2-a40a-4904-85f0-cc5294cc03cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAwayStatement
import Theorems.Thm_P2M_GlobalTheory_adjoin_mem_of_away_localization__6f8afc424f7c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Algebra
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  first | exact @GlobalTheory.adjoin_mem_of_away_localization' | exact GlobalTheory.adjoin_mem_of_away_localization' | (intros; apply GlobalTheory.adjoin_mem_of_away_localization' <;> assumption)
end _root_.GlobalTheory.T
