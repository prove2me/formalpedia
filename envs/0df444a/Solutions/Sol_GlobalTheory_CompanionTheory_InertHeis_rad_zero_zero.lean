-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.rad_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:07.584637+00:00
-- url     : https://prove2.me/submissions/788b9286-201c-470b-bb54-2521c49bac6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
section Entries
variable {u : GU σ (N + 2)}
private theorem mat_apply_eq_one_apply_of_mem_radQ_of_blk_le (hu : u ∈ radQ σ N) (i j : Fin (N + 2)) (h : blk N j ≤ blk N i) :
    mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j :=
  hu i j h
end Entries
section Values
variable (r b : Fin N → L) (c : L)
end Values
end GlobalTheory.CompanionTheory.InertHeis
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
variable {u : GU σ (N + 2)}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution (hu : u ∈ radQ σ N) : mat u 0 0 = 1 := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu 0 0 le_rfl, Matrix.one_apply_eq]
end GlobalTheory.CompanionTheory.InertHeis
