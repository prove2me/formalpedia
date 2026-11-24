-- Prove2me | solution 1 for GlobalTheory.InertZeta.inv_mul_of_rowOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:23.898862+00:00
-- url     : https://prove2.me/submissions/27d432e5-b3c6-4dd3-bf37-2722b838f912

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
import Theorems.Thm_GlobalTheory_InertZeta_colOf_eq_of_rowOf_eq
import Theorems.Thm_GlobalTheory_InertZeta_rowOf_inv

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
theorem _root_.solution {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : rowOf (u⁻¹ * u') = 0 ∧ cornerOf (u⁻¹ * u') = cornerOf u' - cornerOf u := by
  obtain ⟨ri, ci⟩ := rowOf_inv h1 h2 hu
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u' hu'
  have hc := colOf_eq_of_rowOf_eq h1 hu hu' h
  refine ⟨by rw [r, ri, h, neg_add_cancel], ?_⟩
  rw [c, ci, ri, ← hc, neg_dotProduct]
  ring
end GlobalTheory.InertZeta
