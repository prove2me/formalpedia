-- Prove2me | solution 1 for GlobalTheory.T.capelli_left_comatrix_qminor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:35.911009+00:00
-- url     : https://prove2.me/submissions/458045c8-bf1b-444a-88f0-dc4554c2c4ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliLeftComatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliLeftComatrixStatement
import Theorems.Thm_GlobalTheory_capelli_left_comatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (j l : Fin (m + 1)), ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) = if l = j then qdet E u else 0 := by
  first | exact @GlobalTheory.capelli_left_comatrix | exact GlobalTheory.capelli_left_comatrix | (intros; apply GlobalTheory.capelli_left_comatrix <;> assumption)
end _root_.GlobalTheory.T
