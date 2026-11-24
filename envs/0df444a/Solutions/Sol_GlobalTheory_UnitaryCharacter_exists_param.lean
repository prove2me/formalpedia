-- Prove2me | solution 1 for GlobalTheory.UnitaryCharacter.exists_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:15.724496+00:00
-- url     : https://prove2.me/submissions/11c2dc5e-e972-49cd-bf5d-725538431743

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegral
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
import Theorems.Thm_GlobalTheory_UnitarySwap_mul_lt_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.UnitarySwap
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCharacter
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L} {B : V →ₛₗ[σ] V →ₗ[L] L}
namespace GlobalTheory.UnitaryCharacter
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {τ : L} (hτ : τ ∈ intL L) (hτ1 : τ + σ τ = 1) {δ : L}
    (hδ : Valued.v δ = 1) (hδ' : σ δ = -δ) {π : L} (hπ0 : π ≠ 0) (hπ : Valued.v π < 1) (hσπ : σ π = π)
    {A : L} (hA : A ∈ intL L) (hA' : σ A = A) :
    ∃ μ : L, μ ≠ 0 ∧ A = μ + σ μ ∧ ∃ m ∈ intL L, μ⁻¹ = π * m ∧ m * (δ + π * (τ * A)) = 1 := by
  have h1 : Valued.v (δ + π * (τ * A)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hδ]; exact mul_lt_one hπ (mul_mem hτ hA)), hδ]
  have h0 : δ + π * (τ * A) ≠ 0 := by
    intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
  refine ⟨π⁻¹ * (δ + π * (τ * A)), mul_ne_zero (inv_ne_zero hπ0) h0, ?_, (δ + π * (τ * A))⁻¹, ?_, ?_,
    inv_mul_cancel₀ h0⟩
  · have : σ τ = 1 - τ := by rw [← hτ1]; ring
    simp only [map_mul, map_add, map_inv₀, hσπ, hδ', hA', this]
    field_simp
    ring
  · rw [mem_int, map_inv₀, h1, inv_one]
  · rw [mul_inv, inv_inv]
end GlobalTheory.UnitaryCharacter
