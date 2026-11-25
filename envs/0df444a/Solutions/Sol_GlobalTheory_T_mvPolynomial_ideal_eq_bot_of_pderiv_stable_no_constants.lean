-- Prove2me | solution 1 for GlobalTheory.T.mvPolynomial_ideal_eq_bot_of_pderiv_stable_no_constants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:42.88057+00:00
-- url     : https://prove2.me/submissions/6dcfc336-19c5-478d-98c7-2a60c42a6b96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialIdealEqBotOfPderivStableNoConstants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialIdealEqBotOfPderivStableNoConstantsStatement
import Theorems.Thm_GlobalTheory_mvPolynomial_ideal_eq_bot_of_pderiv_stable


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
theorem _root_.solution : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  first | exact @GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | exact GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable | (intros; apply GlobalTheory.mvPolynomial_ideal_eq_bot_of_pderiv_stable <;> assumption)
end _root_.GlobalTheory.T
