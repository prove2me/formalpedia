-- Prove2me | solution 1 for GlobalTheory.SW.transH_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:01:08.282799+00:00
-- url     : https://prove2.me/submissions/4b4e33ef-7fdc-411a-8b5e-d5e7890fb180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_HAct_mul_blocks
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.HermComp
variable {N : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.SW.HermComp
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem inv_denominator_mul_lower_left_cocycle {N : ℕ}
    {A B C D C' D' Z : Matrix (Fin N) (Fin N) ℂ}
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hdet0 : (C * Z + D).det ≠ 0)
    (hdet1 : (C' * ((A * Z + B) * (C * Z + D)⁻¹) + D').det ≠ 0) :
    ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D') * (C * Z + D))⁻¹ * (C' * A + D' * C) =
      (C * Z + D)⁻¹ * ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D')⁻¹ * C') * (Z * Cᴴ + Dᴴ)⁻¹ +
        (C * Z + D)⁻¹ * C := by
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have hadj : (Z * Cᴴ + Dᴴ) * W = Z * Aᴴ + Bᴴ :=
    _root_.GlobalTheory.SW.HAct.den'_act h1 h2 h3 h4 hdet0
  have hinv : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hadj]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3]
    abel
  have hunit : IsUnit (C' * W + D').det := isUnit_iff_ne_zero.mpr hdet1
  have hC : (C * Z + D)⁻¹ * C = (C * Z + D)⁻¹ * (C' * W + D')⁻¹ * ((C' * W + D') * C) := by
    rw [Matrix.mul_assoc ((C * Z + D)⁻¹), ← Matrix.mul_assoc ((C' * W + D')⁻¹),
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rw [hinv, Matrix.mul_inv_rev, hC]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem matrix_of_apply_row {m r : Type} {α : Type} (f : m → r → α) (k : m) :
    Matrix.of f k = f k := rfl
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (γ γ' : _root_.GlobalTheory.SW.M2 E N), γ ∈ _root_.GlobalTheory.SW.UU E N → γ' ∈ _root_.GlobalTheory.SW.UU E N → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' = _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) * _root_.GlobalTheory.SW.hFac Ψ γ Z z z') ∧ ∀ φ ψ χ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.TransH Ψ γ φ ψ → _root_.GlobalTheory.SW.TransH Ψ γ' ψ χ → _root_.GlobalTheory.SW.TransH Ψ (γ' * γ) φ χ := by
  intro E _ _ _ Ψ n N γ γ' hγ hγ'
  have key : ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N,
      _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' =
        _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z)
          (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
          (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) *
        _root_.GlobalTheory.SW.hFac Ψ γ Z z z' := by
    intro Z hZ z z'
    obtain ⟨hτ, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    obtain ⟨-, hden, -⟩ := hcomp γ' hγ'
    have hτ' := ((_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ' hγ').2 _ hmem).1
    unfold _root_.GlobalTheory.SW.hFac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hlow := (_root_.GlobalTheory.SW.HAct.mul_blocks (E := E) (τ : E →+* ℂ) γ γ').2.2.1
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks (by
      rw [← _root_.GlobalTheory.SW.HAct.map_blocks (E := E) (τ : E →+* ℂ) γ]
      exact _root_.GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) hγ)
    have hM := inv_denominator_mul_lower_left_cocycle (C' := (toBlocks₂₁ γ').map (τ : E →+* ℂ))
      (D' := (toBlocks₂₂ γ').map (τ : E →+* ℂ)) (Z := Z τ) h1 h2 h3 h4 (hτ τ).1 (hτ' τ).1
    rw [hden τ, Matrix.det_mul, mul_pow, hlow]
    simp only [_root_.GlobalTheory.SW.hDen, _root_.GlobalTheory.SW.hDen',
      _root_.GlobalTheory.SW.hAct] at hM ⊢
    rw [hM]
    simp only [matrix_of_apply_row, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_add,
      Complex.exp_add]
    ring
  refine ⟨key, fun φ ψ χ hφ hψ Z hZ z z' => ?_⟩
  obtain ⟨-, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hact, hden, hadj⟩ := hcomp γ' hγ'
  have hvar : (fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ (γ' * γ) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ *ᵥ
          (Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) k := by
    funext τ
    congr 1
    funext k
    rw [hadj τ, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rfl
  have hvar' : (fun τ => Matrix.of fun k =>
        z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ (γ' * γ) Z τ)⁻¹) =
      fun τ => Matrix.of fun k =>
        (Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) k ᵥ*
          (_root_.GlobalTheory.SW.hDen Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ := by
    funext τ
    congr 1
    funext k
    rw [hden τ, Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul]
    rfl
  rw [hact, hvar, hvar', hψ _ hmem, hφ Z hZ z z', key Z hZ z z', mul_assoc]
end _root_.GlobalTheory.SW
