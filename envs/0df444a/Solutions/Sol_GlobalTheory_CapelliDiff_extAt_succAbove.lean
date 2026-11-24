-- Prove2me | solution 1 for GlobalTheory.CapelliDiff.extAt_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:14.942767+00:00
-- url     : https://prove2.me/submissions/2950d0fa-00ac-43a2-9bda-e84b58d08538

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory GlobalTheory.CapelliDiff
namespace GlobalTheory.CapelliDiff
theorem _root_.solution {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    extAt k τ (k.succAbove j) = k.succAbove (τ j) := by
  have hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1)) := by
    rw [finSuccAboveEquiv_apply]
  unfold extAt
  rw [hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSuccAboveEquiv_apply]
end GlobalTheory.CapelliDiff
