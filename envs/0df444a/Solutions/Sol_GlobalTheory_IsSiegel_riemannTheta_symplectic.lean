-- Prove2me | solution 1 for GlobalTheory.IsSiegel.riemannTheta_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:16.311285+00:00
-- url     : https://prove2.me/submissions/9c471bf6-213f-444e-880f-b3f2297b71bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_tsum_eq_sum_tsum_add_mulVec
import Theorems.Thm_GlobalTheory_intCast_mulVec_complex
import Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_inv_relations
import Theorems.Thm_GlobalTheory_isUnit_det_map_intCast
import Theorems.Thm_GlobalTheory_sum_exp_pair_mul_exp
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv_add_inv_mul
import Theorems.Thm_GlobalTheory_symplectic_action_eq
import Theorems.Thm_GlobalTheory_IsSiegel_add_map_ofReal
import Theorems.Thm_GlobalTheory_IsSiegel_hasSum_riemannTheta
import Theorems.Thm_GlobalTheory_IsSiegel_isUnit_det
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_eq_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_siegelGaussIntegral_ne_zero
import Theorems.Thm_GlobalTheory_IsSiegel_transpose_mul_mul
import Theorems.Thm_GlobalTheory_inv_map_ofReal
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_ofReal_mulVec_eq
import Theorems.Thm_GlobalTheory_ratCircleChar_pairQuadraticForm_mk
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_GlobalTheory_riemannThetaTerm_zero_zero
import Theorems.Thm_GlobalTheory_symm_coprime_of_mem_symplecticGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.mem_siegelUpperCoords
attribute [local simp] GlobalTheory.riemannThetaJointForm_apply



set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {τ : Matrix ι ι ℂ} (hτ : IsSiegel τ)
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ))
    {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin)) (z : ι → ℂ) :
    riemannTheta 0 0 ((a.map (↑) * τ + b.map (↑)) * (c.map (↑) * τ + d.map (↑))⁻¹)
        ((c.map (↑) * τ + d.map (↑))⁻¹ᵀ *ᵥ z) *
      cexp (-(π * I) * (z ⬝ᵥ ((c.map (↑) * τ + d.map (↑))⁻¹ * c.map (↑)) *ᵥ z)) =
    (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
      siegelGaussIntegral (τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ))⁻¹ /
      siegelGaussIntegral τ * riemannTheta 0 0 τ z := by
  have hs := (symm_coprime_of_mem_symplecticGroup h).1
  have hu := isUnit_det_map_intCast ℂ hd
  have huR := isUnit_det_map_intCast ℝ hd
  have hN := hτ.neg_inv_add_inv_mul h hd
  have hG := sum_exp_pair_mul_exp h hd hb hc r hr
  have hφ := ratCircleChar_pairQuadraticForm_mk hd hs hb
  have eR (M : Matrix ι ι ℤ) : M.map ((↑) : ℤ → ℂ) = (M.map ((↑) : ℤ → ℝ)).map ofReal := by
    ext
    simp
  have eD : (d.map ((↑) : ℤ → ℂ))⁻¹ = (d.map ((↑) : ℤ → ℝ))⁻¹.map ofReal := by
    rw [eR d, inv_map_ofReal huR.ne_zero]
  have hBR := (symplectic_fromBlocks_inv_relations
    (fromBlocks_map_intCast_mem_symplecticGroup ℝ h) huR).1
  have eB : b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹ =
      (b.map ((↑) : ℤ → ℝ) * (d.map ((↑) : ℤ → ℝ))⁻¹).map ofReal := by
    rw [eD]
    ext i j
    simp [mul_apply]
  have hcast := intCast_mulVec_complex d
  have hC := fromBlocks_map_intCast_mem_symplecticGroup ℂ h
  set A := a.map ((↑) : ℤ → ℂ)
  set B := b.map ((↑) : ℤ → ℂ)
  set C := c.map ((↑) : ℤ → ℂ)
  set D := d.map ((↑) : ℤ → ℂ)
  set N := τ⁻¹ + D⁻¹ * C with hNdef
  have hNu : IsUnit N.det := by
    have := hN.isUnit_det
    rw [det_neg] at this
    exact isUnit_of_mul_isUnit_right this
  have hNs : N.IsSymm := by simpa using hN.isSymm.neg
  have hσ : IsSiegel N⁻¹ := by
    have e : (-N)⁻¹ = -N⁻¹ := inv_eq_right_inv (by rw [neg_mul_neg, mul_nonsing_inv _ hNu])
    simpa [e] using hN.neg_inv
  have hτs : τ⁻¹.IsSymm := by simpa using hτ.neg_inv.isSymm.neg
  obtain ⟨e1, e2⟩ := symplectic_action_eq hC hu hτ.isUnit_det hNu
  rw [← hNdef] at e1 e2
  have e3 : (C * τ + D)⁻¹ = τ⁻¹ * N⁻¹ * D⁻¹ := by
    rw [e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have hγ : IsSiegel (D⁻¹ᵀ * N⁻¹ * D⁻¹ + B * D⁻¹) := by
    rw [eB, eD]
    exact (hσ.transpose_mul_mul (isUnit_nonsing_inv_det _ huR).ne_zero).add_map_ofReal hBR
  have e4 : (C * τ + D)⁻¹ᵀ *ᵥ z = D⁻¹ᵀ *ᵥ N⁻¹ *ᵥ τ⁻¹ *ᵥ z := by
    rw [e3, transpose_mul, transpose_mul, hσ.isSymm.eq, hτs.eq, mulVec_mulVec, mulVec_mulVec,
      Matrix.mul_assoc]
  have e5 : z ⬝ᵥ ((C * τ + D)⁻¹ * C) *ᵥ z =
      z ⬝ᵥ τ⁻¹ *ᵥ z - (N⁻¹ *ᵥ τ⁻¹ *ᵥ z) ⬝ᵥ τ⁻¹ *ᵥ z := by
    rw [e3, Matrix.mul_assoc, show D⁻¹ * C = N - τ⁻¹ by rw [hNdef]; abel, Matrix.mul_sub,
      nonsing_inv_mul_cancel_right _ _ hNu, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec_comm_of_isSymm hτs z (N⁻¹ *ᵥ _)]
  set x : κ → ι → ℝ := fun k => (d.map ((↑) : ℤ → ℝ))⁻¹ *ᵥ fun i => (r k i : ℝ) with hx
  have hx' (k : κ) : (fun i => (x k i : ℂ)) = D⁻¹ *ᵥ fun i => (r k i : ℂ) := by
    rw [eD]
    exact ofReal_mulVec_eq _ _

  have t1 (k : κ) (m : ι → ℤ) :
      riemannThetaTerm 0 0 (D⁻¹ᵀ * N⁻¹ * D⁻¹ + B * D⁻¹) (D⁻¹ᵀ *ᵥ N⁻¹ *ᵥ τ⁻¹ *ᵥ z) (r k + d *ᵥ m) =
        cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ (B * D⁻¹) *ᵥ fun i => (r k i : ℂ))) *
          riemannThetaTerm (x k) 0 N⁻¹ (N⁻¹ *ᵥ τ⁻¹ *ᵥ z) m := by
    have q1 : (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin) =
        Submodule.Quotient.mk (r k + d *ᵥ m) :=
      (Submodule.Quotient.eq _).2 ⟨-m, by simp [mulVec_neg]⟩
    have q2 : (fun i => (m i : ℂ) + x k i) = D⁻¹ *ᵥ fun i => ((r k + d *ᵥ m) i : ℂ) := by
      have : (fun i => ((r k + d *ᵥ m) i : ℂ)) =
          (fun i => (r k i : ℂ)) + fun i => ((d *ᵥ m) i : ℂ) := by
        ext
        simp
      rw [this, hcast, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, ← hx',
        add_comm]
      rfl
    rw [← hφ, q1, hφ, riemannThetaTerm_zero_zero, riemannThetaTerm, q2, ← Complex.exp_add]
    generalize (fun i => ((r k + d *ᵥ m) i : ℂ)) = n
    congr 1
    simp only [Pi.zero_apply, ofReal_zero, add_zero]
    rw [add_mulVec, dotProduct_add, ← mulVec_mulVec n (D⁻¹ᵀ * N⁻¹), ← mulVec_mulVec _ D⁻¹ᵀ,
      dotProduct_mulVec n D⁻¹ᵀ, dotProduct_mulVec n D⁻¹ᵀ, vecMul_transpose]
    ring

  have t2 : ∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ (B * D⁻¹) *ᵥ fun i => (r k i : ℂ))) *
      riemannTheta 0 (x k) (-N) (τ⁻¹ *ᵥ z) =
      (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ (B * D⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
        riemannTheta 0 0 (-τ⁻¹) (τ⁻¹ *ᵥ z) := by
    refine (hasSum_sum fun k _ =>
      (hN.hasSum_riemannTheta 0 (x k) (τ⁻¹ *ᵥ z)).mul_left _).unique ?_
    convert (hτ.neg_inv.hasSum_riemannTheta 0 0 (τ⁻¹ *ᵥ z)).mul_left _ using 2 with m
    have q (k : κ) : riemannThetaTerm 0 (x k) (-N) (τ⁻¹ *ᵥ z) m =
        cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ D⁻¹ *ᵥ fun i => (r k i : ℂ))) *
          riemannThetaTerm 0 0 (-N) (τ⁻¹ *ᵥ z) m := by
      have := riemannThetaTerm_add_ofReal 0 0 (x k) (-N) (τ⁻¹ *ᵥ z) m
      rw [zero_add] at this
      rw [← this, riemannThetaTerm_add, hx', mul_comm]
      simp
    simp only [q, ← mul_assoc _ _ (riemannThetaTerm ..), ← Finset.sum_mul]
    rw [hG, mul_assoc, riemannThetaTerm_zero_zero, riemannThetaTerm_zero_zero, ← Complex.exp_add,
      hNdef, neg_mulVec, neg_mulVec, add_mulVec, dotProduct_neg, dotProduct_neg, dotProduct_add]
    congr 2
    ring
  rw [e2, e4, e5, riemannTheta,
    tsum_eq_sum_tsum_add_mulVec hd r hr (hγ.summable_riemannThetaTerm 0 0 _)]
  simp only [t1, tsum_mul_left]
  have t3 (k : κ) := hσ.riemannTheta_eq_neg_inv (x k) (N⁻¹ *ᵥ τ⁻¹ *ᵥ z)
  simp only [nonsing_inv_nonsing_inv _ hNu, mulVec_mulVec _ N N⁻¹, mul_nonsing_inv _ hNu,
    one_mulVec] at t3
  simp only [← riemannTheta_def, t3, mul_left_comm _ (siegelGaussIntegral N⁻¹ * _),
    ← Finset.mul_sum]
  rw [t2, hτ.riemannTheta_eq_neg_inv, mul_sub, Complex.exp_sub]
  field_simp [hτ.siegelGaussIntegral_ne_zero]
end IsSiegel
end GlobalTheory
