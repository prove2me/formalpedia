-- Prove2me | solution 1 for GlobalTheory.T.localized_presentation_eval_quotient_fraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:40.611022+00:00
-- url     : https://prove2.me/submissions/22be4e07-5588-426f-85c3-3f46cf639ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizedPresentationEvalQuotientFraction
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizedPresentationEvalQuotientFractionStatement
import Theorems.Thm_P2M_GlobalTheory_exists_eval__fraction_of_exists_mod_nilpotent_08ab835b4f0d


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
theorem _root_.solution : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  first | exact @GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | exact GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | (intros; apply GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent <;> assumption)
end _root_.GlobalTheory.T
