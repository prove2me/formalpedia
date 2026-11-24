-- Prove2me | solution 1 for GlobalTheory.CapelliDiff.sign_extAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:16.8111+00:00
-- url     : https://prove2.me/submissions/f432b0be-927d-4fe9-aa80-39d9b3d61f78

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
theorem _root_.solution {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by
  unfold extAt
  rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]
end GlobalTheory.CapelliDiff
