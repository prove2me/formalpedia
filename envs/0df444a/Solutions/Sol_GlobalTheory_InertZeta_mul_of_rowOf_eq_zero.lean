-- Prove2me | solution 1 for GlobalTheory.InertZeta.mul_of_rowOf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:13:28.1455+00:00
-- url     : https://prove2.me/submissions/a5bc574b-6298-4d08-81f5-1e69aa30b6a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
import Theorems.Thm_GlobalTheory_InertZeta_colOf_eq_zero

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
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
variable
  (h1 : ∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧ cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L))
  (h2 : ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u')
include h1
include h2
namespace GlobalTheory.InertZeta
theorem _root_.solution {u z : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hz : z ∈ radQ σ N) (h : rowOf z = 0) :
    rowOf (u * z) = rowOf u ∧ colOf (u * z) = colOf u ∧ cornerOf (u * z) = cornerOf u + cornerOf z := by
  obtain ⟨r, b, c⟩ := h2 u hu z hz
  have hb := colOf_eq_zero h1 hz h
  refine ⟨by rw [r, h, add_zero], by rw [b, hb, add_zero], by rw [c, hb, dotProduct_zero, add_zero]⟩
end GlobalTheory.InertZeta
