-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDoubling.ring_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:12.818183+00:00
-- url     : https://prove2.me/submissions/936522fa-dae6-484b-a4de-6d4e520933dc

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
namespace GlobalTheory.CompanionTheory.InertDoubling
theorem _root_.solution {R : Type} [Ring R] (J A B U V a b u v S : R) (hJ : J * J = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) = J := by
  have e : a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) =
      (a * (J * J) * u + b * (J * J) * v) * J + (a * J * A) * S - (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : (a * 1 * u + b * 1 * v) * J + (b * J * B) * S - (b * J * B) * S = (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h2, one_mul]
end GlobalTheory.CompanionTheory.InertDoubling
