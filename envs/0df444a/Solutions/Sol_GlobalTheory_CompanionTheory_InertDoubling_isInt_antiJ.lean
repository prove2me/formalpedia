-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDoubling.isInt_antiJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:11.351947+00:00
-- url     : https://prove2.me/submissions/dfc1d96d-5d6b-45ed-9187-8075e47edb0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertDoubling
theorem _root_.solution (n : ℕ) : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _
end GlobalTheory.CompanionTheory.InertDoubling
