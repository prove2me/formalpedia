-- Prove2me | solution 1 for GlobalTheory.InertZeta.rowOf_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:41.085958+00:00
-- url     : https://prove2.me/submissions/600a9696-97f8-4911-882f-038eb240d3f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
import Theorems.Thm_GlobalTheory_InertZeta_rowOf_one
import Theorems.Thm_GlobalTheory_InertZeta_cornerOf_one

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
theorem _root_.solution {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    rowOf u⁻¹ = -rowOf u ∧ cornerOf u⁻¹ = -cornerOf u + rowOf u ⬝ᵥ colOf u := by
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u hu
  rw [inv_mul_cancel, rowOf_one] at r
  rw [inv_mul_cancel, cornerOf_one] at c
  have r' : rowOf u⁻¹ = -rowOf u := eq_neg_of_add_eq_zero_left r.symm
  refine ⟨r', ?_⟩
  rw [r', neg_dotProduct] at c
  linear_combination -c
end GlobalTheory.InertZeta
