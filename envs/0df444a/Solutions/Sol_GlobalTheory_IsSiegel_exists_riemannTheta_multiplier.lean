-- Prove2me | solution 1 for GlobalTheory.IsSiegel.exists_riemannTheta_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:20.461634+00:00
-- url     : https://prove2.me/submissions/0e85fd58-7cc0-4534-97d2-30138271fca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_fromBlocks_map_intCast_mem_symplecticGroup
import Theorems.Thm_GlobalTheory_isUnit_det_map_intCast
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv_add_inv_mul
import Theorems.Thm_GlobalTheory_symplectic_action_eq
import Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_symplectic
import Theorems.Thm_GlobalTheory_IsSiegel_isUnit_det
import Theorems.Thm_GlobalTheory_IsSiegel_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_siegelGaussIntegral_ne_zero
import Theorems.Thm_GlobalTheory_IsSiegel_siegelGaussIntegral_sq_mul_det
import Theorems.Thm_GlobalTheory_exists_representatives_quotient_range_mulVecLin
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_GlobalTheory_sq_sum_exp_pair
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
    (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hodd : Odd d.det)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ)) :
    ∃ l : ℂ, l ^ 2 = (ZMod.χ₄ (d.det : ZMod 4) : ℤ) *
      (c.map ((↑) : ℤ → ℂ) * τ + d.map ((↑) : ℤ → ℂ)).det ∧
      ∀ z : ι → ℂ, riemannTheta 0 0 ((a.map (↑) * τ + b.map (↑)) * (c.map (↑) * τ + d.map (↑))⁻¹)
          ((c.map (↑) * τ + d.map (↑))⁻¹ᵀ *ᵥ z) *
        cexp (-(π * I) * (z ⬝ᵥ ((c.map (↑) * τ + d.map (↑))⁻¹ * c.map (↑)) *ᵥ z)) =
        l * riemannTheta 0 0 τ z := by
  have hd : d.det ≠ 0 := by
    rintro h0
    simp [h0] at hodd
  obtain ⟨r, hr⟩ := exists_representatives_quotient_range_mulVecLin hd
  refine ⟨_, ?_, hτ.riemannTheta_symplectic h hd hb hc r hr⟩
  obtain ⟨hs, hco⟩ := symm_coprime_of_mem_symplecticGroup h
  have hN := hτ.neg_inv_add_inv_mul h hd
  have hNu : IsUnit (τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ)).det := by
    have := hN.isUnit_det
    rw [det_neg] at this
    exact isUnit_of_mul_isUnit_right this
  have e1 := (symplectic_action_eq (fromBlocks_map_intCast_mem_symplecticGroup ℂ h)
    (isUnit_det_map_intCast ℂ hd) hτ.isUnit_det hNu).1
  rw [div_pow, mul_pow, sq_sum_exp_pair hodd hs hb hco r hr, e1, det_mul, det_mul, ← Int.cast_det]
  generalize τ⁻¹ + (d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ) = N at hN hNu
  have hσ : IsSiegel N⁻¹ := by
    have e : (-N)⁻¹ = -N⁻¹ := inv_eq_right_inv (by rw [neg_mul_neg, mul_nonsing_inv _ hNu])
    simpa [e] using hN.neg_inv
  have h1 := hσ.siegelGaussIntegral_sq_mul_det
  have h2 := hτ.siegelGaussIntegral_sq_mul_det
  have h3 := det_nonsing_inv_mul_det _ hNu
  rw [det_smul] at h1 h2
  have h4 : (-I) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by simp)
  rw [div_eq_iff (pow_ne_zero _ hτ.siegelGaussIntegral_ne_zero)]
  apply mul_left_cancel₀ h4
  linear_combination ((ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ)) * (N.det * h1 - N.det * h2 -
    (-I) ^ Fintype.card ι * siegelGaussIntegral N⁻¹ ^ 2 * h3)
end IsSiegel
end GlobalTheory
