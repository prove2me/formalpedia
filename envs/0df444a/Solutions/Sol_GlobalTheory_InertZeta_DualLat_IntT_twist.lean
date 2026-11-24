-- Prove2me | solution 1 for GlobalTheory.InertZeta.DualLat.IntT.twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:45:50.836263+00:00
-- url     : https://prove2.me/submissions/f0e75ce3-5a3a-4e57-b559-743f45daff0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.DualLat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.DualLat
namespace IntT
theorem _root_.solution {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {t : L} {x : Fin N → L} (hx : IntT t x) :
    IntT t (tw σ x) := fun j => by
  show Valued.v (t * σ (x j.rev)) ≤ 1
  rw [map_mul, hσ, ← map_mul]; exact hx j.rev
end IntT
end GlobalTheory.InertZeta.DualLat
