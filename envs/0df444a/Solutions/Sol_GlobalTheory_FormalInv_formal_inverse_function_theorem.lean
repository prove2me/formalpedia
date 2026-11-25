-- Prove2me | solution 1 for GlobalTheory.FormalInv.formal_inverse_function_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:40.188273+00:00
-- url     : https://prove2.me/submissions/8dc5ed49-4af9-4699-8b78-409217072444

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_eq_substInv_of_right
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_two_le_order_sub_X_iff
import Theorems.Thm_GlobalTheory_FormalInv_two_le_order_substInv_sub_X
import Theorems.Thm_GlobalTheory_FormalInv_coeff_substInv_mem_of_two_le_order
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
import Theorems.Thm_GlobalTheory_FormalInv_coeff_subst_sumFamily_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
namespace GlobalTheory.FormalInv
theorem _root_.solution :
    (∀ (R : Type) [CommRing R] (n : ℕ) (u : Fin n → MvPowerSeries (Fin n) R),
      (∀ i, constantCoeff (u i) = 0) →
      IsUnit (Matrix.of fun i j => coeff (single j 1) (u i) : Matrix (Fin n) (Fin n) R) →
      ∃! v : Fin n → MvPowerSeries (Fin n) R, (∀ i, constantCoeff (v i) = 0) ∧
        (∀ i, (u i).subst v = X i) ∧ ∀ i, (v i).subst u = X i) ∧
    (∀ (C : Type) [CommRing C] (S : Subring C) (g n m : ℕ)
      (l : Fin n → MvPowerSeries (Fin n) C) (l' : Fin m → MvPowerSeries (Fin m) C),
      (∀ i, (2 : ℕ∞) ≤ (l i - X i).order) → (∀ j, (2 : ℕ∞) ≤ (l' j - X j).order) →
      (∀ i (d : Fin n →₀ ℕ), d.degree < g → coeff d (l i) ∈ S) →
      (∀ j (d : Fin m →₀ ℕ), d.degree < g → coeff d (l' j) ∈ S) →
      ∃ (e : Fin n → MvPowerSeries (Fin n) C) (e' : Fin m → MvPowerSeries (Fin m) C),
        ((∀ i, (2 : ℕ∞) ≤ (e i - X i).order) ∧
          (∀ i, (l i).subst e = X i) ∧ (∀ i, (e i).subst l = X i) ∧
          ∀ i (d : Fin n →₀ ℕ), d.degree < g → coeff d (e i) ∈ S) ∧
        ((∀ j, (2 : ℕ∞) ≤ (e' j - X j).order) ∧
          (∀ j, (l' j).subst e' = X j) ∧ (∀ j, (e' j).subst l' = X j) ∧
          ∀ j (d : Fin m →₀ ℕ), d.degree < g → coeff d (e' j) ∈ S) ∧
        (∀ u : MvPowerSeries (Fin n ⊕ Fin m) S, ∀ (α : Fin n →₀ ℕ) (β : Fin m →₀ ℕ),
          α.degree < g → β.degree < g →
          coeff (α.sumElim β) ((MvPowerSeries.map S.subtype u).subst (sumFamily e e')) ∈ S) ∧
        (∀ v : MvPowerSeries (Fin n ⊕ Fin m) C,
          (∀ (α : Fin n →₀ ℕ) (β : Fin m →₀ ℕ), α.degree < g → β.degree < g →
            coeff (α.sumElim β) v ∈ S) →
          ∀ (α : Fin n →₀ ℕ) (β : Fin m →₀ ℕ), α.degree < g → β.degree < g →
            coeff (α.sumElim β) (v.subst (sumFamily l l')) ∈ S)) := by
  refine ⟨fun R _ n u hu hA => ⟨substInv u, ⟨constantCoeff_substInv hu,
    subst_substInv_right hu hA, subst_substInv_left hu hA⟩,
    fun v hv => eq_substInv_of_right hu hv.1 hv.2.1⟩, ?_⟩
  intro C _ S g n m l l' hl hl' hS hS'
  obtain ⟨h0, h1⟩ := two_le_order_sub_X_iff.1 hl
  obtain ⟨h0', h1'⟩ := two_le_order_sub_X_iff.1 hl'
  have hA : IsUnit (linearPart l) := h1 ▸ isUnit_one
  have hA' : IsUnit (linearPart l') := h1' ▸ isUnit_one
  refine ⟨substInv l, substInv l',
    ⟨two_le_order_substInv_sub_X hl, subst_substInv_right h0 hA, subst_substInv_left h0 hA,
      coeff_substInv_mem_of_two_le_order hl hS⟩,
    ⟨two_le_order_substInv_sub_X hl', subst_substInv_right h0' hA', subst_substInv_left h0' hA',
      coeff_substInv_mem_of_two_le_order hl' hS'⟩, fun u => ?_, fun v hv => ?_⟩
  · exact coeff_subst_sumFamily_mem (constantCoeff_substInv h0) (constantCoeff_substInv h0')
      (coeff_substInv_mem_of_two_le_order hl hS) (coeff_substInv_mem_of_two_le_order hl' hS')
      fun α β _ _ => by simp
  · exact coeff_subst_sumFamily_mem h0 h0' hS hS' hv
end GlobalTheory.FormalInv
