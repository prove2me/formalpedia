-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDoubling.ring_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:05:11.973796+00:00
-- url     : https://prove2.me/submissions/87207e73-b1f3-422b-9b54-f5b2bd56e851

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
theorem _root_.solution {R : Type} [Ring R] (J A B U V a b u v S s : R) (hJ : J * J = 1) (h1 : U * A + V * B = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * (U * J * u - V * J * v) * J + J * S + s * J := by
  have e : (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * U * (J * J) * J * u * J + J * U * (J * J) * A * S + s * a * (J * J) * u * J + s * (a * J * A) * S
      - J * V * (J * J) * J * v * J + J * V * (J * J) * B * S + s * b * (J * J) * v * J - s * (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : J * U * 1 * J * u * J + J * U * 1 * A * S + s * a * 1 * u * J + s * (b * J * B) * S
      - J * V * 1 * J * v * J + J * V * 1 * B * S + s * b * 1 * v * J - s * (b * J * B) * S =
      J * (U * J * u - V * J * v) * J + J * (U * A + V * B) * S + s * (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h1, h2]
  noncomm_ring
end GlobalTheory.CompanionTheory.InertDoubling
