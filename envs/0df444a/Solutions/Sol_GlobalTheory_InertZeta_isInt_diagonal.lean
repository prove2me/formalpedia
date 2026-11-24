-- Prove2me | solution 1 for GlobalTheory.InertZeta.isInt_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:45.136494+00:00
-- url     : https://prove2.me/submissions/961d7cca-1732-4952-bf7e-8a130b98c5a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixLengthExistsOfElementaryDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hf i
  · exact zero_mem _
end GlobalTheory.InertZeta
