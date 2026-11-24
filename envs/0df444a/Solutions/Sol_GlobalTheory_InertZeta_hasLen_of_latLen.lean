-- Prove2me | solution 1 for GlobalTheory.InertZeta.hasLen_of_latLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:59.652862+00:00
-- url     : https://prove2.me/submissions/8f8ca3b4-8666-4208-8d36-dfb92584ea03

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_GlobalTheory_InertZeta_row_mem_rowLat
import Theorems.Thm_GlobalTheory_InertZeta_mem_rowLat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {g : Matrix (Fin n) (Fin n) L} {k : ℕ}
    (h : LatLen (rowLat (1 : Matrix (Fin n) (Fin n) L) ⊔ rowLat g) k) : HasLen g k := by
  obtain ⟨M, hM, e⟩ := h
  have h0 : M.det ≠ 0 := fun h => by rw [h, map_zero] at hM; exact WithZero.exp_ne_zero hM.symm
  have hu : IsUnit M.det := h0.isUnit
  have h1 : ∀ i, ∃ ρ ρ' : Fin n → L, (∀ i, ρ i ∈ intL L) ∧ (∀ i, ρ' i ∈ intL L) ∧ M i = ρ + ρ' ᵥ* g := fun i => by
    obtain ⟨x, hx, y, hy, e'⟩ := Submodule.mem_sup.1 (e ▸ row_mem_rowLat M i)
    obtain ⟨ρ, hρ, rfl⟩ := mem_rowLat.1 hx
    obtain ⟨ρ', hρ', rfl⟩ := mem_rowLat.1 hy
    exact ⟨ρ, ρ', hρ, hρ', by rw [← e', Matrix.vecMul_one]⟩
  choose U V hU hV hUV using h1
  have h2 : ∀ A : Matrix (Fin n) (Fin n) L, rowLat A ≤ rowLat M → IsInt (A * M⁻¹) := fun A hA i j => by
    obtain ⟨ρ, hρ, e'⟩ := mem_rowLat.1 (hA (row_mem_rowLat A i))
    have : (A * M⁻¹) i = ρ := by
      rw [show (A * M⁻¹) i = A i ᵥ* M⁻¹ from rfl, e', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
        Matrix.vecMul_one]
    rw [this]
    exact hρ j
  refine ⟨Matrix.of U, Matrix.of V, M⁻¹, ⟨hU, hV, by simpa using h2 1 (e ▸ le_sup_left), h2 g (e ▸ le_sup_right), ?_⟩, ?_⟩
  · rw [show Matrix.of U + Matrix.of V * g = M from funext fun i => (hUV i).symm, Matrix.mul_nonsing_inv _ hu]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, map_inv₀, hM, WithZero.exp_neg]
end GlobalTheory.InertZeta
