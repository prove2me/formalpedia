-- Prove2me | solution 1 for GlobalTheory.CayleyUnitary.cayley_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:11.399337+00:00
-- url     : https://prove2.me/submissions/2dc45b5d-63c6-4a8b-8489-1817484df96c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroup
import Theorems.Thm_P2M_GlobalTheory_CayleyUnitary_cT_add__d8bc2b81d278
import Theorems.Thm_P2M_GlobalTheory_CayleyUnitary_cT_sub__9304f5a5c678

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CayleyUnitary
open Formalism.UG
namespace GlobalTheory.CayleyUnitary
theorem _root_.solution {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J S : Matrix (Fin n) (Fin n) E) :
    J.det ≠ 0 → cT σ S * J + J * S = 0 → (1 - S).det ≠ 0 →
    ∃ γ : GL (Fin n) E, γ ∈ UJ σ J ∧ (γ : Matrix (Fin n) (Fin n) E) = (1 + S) * (1 - S)⁻¹ := by
  intro hJ hS hd
  have hneg : cT σ S * J = -(J * S) := eq_neg_of_add_eq_zero_left hS
  have hBu : IsUnit (1 - S).det := isUnit_iff_ne_zero.mpr hd
  have hBBi : (1 - S) * (1 - S)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  have h1 : cT σ (1 + S) * J = J * (1 - S) := by
    rw [cT_add', cT_one, Matrix.add_mul, Matrix.one_mul, hneg, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
  have h2 : J * (1 + S) = cT σ (1 - S) * J := by
    rw [cT_sub', cT_one, Matrix.sub_mul, Matrix.one_mul, hneg, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  have hc : (1 - S) * (1 + S) = (1 + S) * (1 - S) := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]; abel
  have key : cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J := by
    rw [cT_mul]
    calc cT σ (1 - S)⁻¹ * cT σ (1 + S) * J * ((1 + S) * (1 - S)⁻¹)
        = cT σ (1 - S)⁻¹ * (cT σ (1 + S) * J) * (1 + S) * (1 - S)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * J * ((1 - S) * (1 + S)) * (1 - S)⁻¹ := by
          rw [h1]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - S)⁻¹ * (J * (1 + S)) * ((1 - S) * (1 - S)⁻¹) := by
          rw [hc]; simp only [Matrix.mul_assoc]
      _ = J := by
          rw [h2, hBBi, Matrix.mul_one, ← Matrix.mul_assoc, ← cT_mul, hBBi, cT_one, Matrix.one_mul]
  have hdet : ((1 + S) * (1 - S)⁻¹).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det key
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ this.symm
  refine ⟨Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), ?_, rfl⟩
  show cT σ ((1 + S) * (1 - S)⁻¹) * J * ((1 + S) * (1 - S)⁻¹) = J
  exact key
end GlobalTheory.CayleyUnitary
