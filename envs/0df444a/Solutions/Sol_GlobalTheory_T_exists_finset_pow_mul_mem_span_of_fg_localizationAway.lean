-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:58.524932+00:00
-- url     : https://prove2.me/submissions/ffad45a3-12ae-41bc-8c60-dc773dd29250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinsetStatement
import Theorems.Thm_GlobalTheory_fg_localizationAway_span_finset


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
theorem _root_.solution : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  first | exact @GlobalTheory.fg_localizationAway_span_finset | exact GlobalTheory.fg_localizationAway_span_finset | (intros; apply GlobalTheory.fg_localizationAway_span_finset <;> assumption)
end _root_.GlobalTheory.T
