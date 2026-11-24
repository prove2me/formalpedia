-- Prove2me | solution 1 for GlobalTheory.WeilM.splitOm_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:45.716464+00:00
-- url     : https://prove2.me/submissions/12109b44-7dc9-419f-b659-c7deffc5e082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Theorems.Thm_GlobalTheory_WeilM_splitDarboux_e
import Theorems.Thm_GlobalTheory_WeilM_ugFst_val
import Theorems.Thm_GlobalTheory_WeilM_ug_rel
import Theorems.Thm_GlobalTheory_WeilM_splitOm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution [Invertible (2 : R)] (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) {JA : Matrix α α (R × R)}
    {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA) (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (ψ : AddChar R ℂ)
    (h : UG (swapA R) JB) (w : Matrix α β (R × R)) (φ : (κ → R) → ℂ) :
    splitOm m χ JB σ h ((splitDarboux hA hB σ).rho ψ w φ) =
      (splitDarboux hA hB σ).rho ψ (actB (swapA R) h w) (splitOm m χ JB σ h φ) := by
  funext u
  have rel := ug_rel h
  have hv := ugFst_val h
  have hmul : (ugFst JB h).val * ((ugFst JB h)⁻¹).val = 1 := by simp
  have hinv : ((ugFst JB h)⁻¹).val * (ugFst JB h).val = 1 := by simp
  have c1 : cmp₁ (actB (swapA R) h w) = cmp₁ w * (ugFst JB h).valᵀ := by
    rw [hv]; simp [actB, Matrix.map_mul, Matrix.transpose_map]; rfl
  have c2 : cmp₂ (actB (swapA R) h w) = cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ := by
    simp [actB, Matrix.map_mul, Matrix.transpose_map]; rfl
  simp only [splitOm_apply, Darboux.rho, schr, splitDarboux_e, c1, c2]

  have key1 : cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) = ((ugFst JB h)⁻¹).valᵀ * cmp₁ JB := by
    calc cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R))
        = ((ugFst JB h).val * ((ugFst JB h)⁻¹).val)ᵀ * cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) := by
          rw [hmul, Matrix.transpose_one, Matrix.one_mul]
      _ = ((ugFst JB h)⁻¹).valᵀ * ((ugFst JB h).valᵀ * cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R))) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [rel]
  have rel' : ∀ X : Matrix β α R, (ugFst JB h).valᵀ * (cmp₁ JB * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) * X)) = cmp₁ JB * X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rel]
  have m1 : (flat σ).symm u * (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ)ᵀ =
      (flat σ).symm u * ((ugFst JB h)⁻¹).valᵀ * (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cmp₁ JB) (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R))), key1, Matrix.mul_assoc]
  have m2 : cmp₁ w * (ugFst JB h).valᵀ * (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ)ᵀ =
      cmp₁ w * (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [rel']
  have eX : flat σ ((flat σ).symm (u + flat σ (cmp₁ w * (ugFst JB h).valᵀ)) * ((ugFst JB h)⁻¹).valᵀ) =
      flat σ ((flat σ).symm u * ((ugFst JB h)⁻¹).valᵀ) + flat σ (cmp₁ w) := by
    rw [map_add, LinearEquiv.symm_apply_apply, Matrix.add_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hinv,
      Matrix.transpose_one, Matrix.mul_one, map_add]
  have eP : u ⬝ᵥ flat σ (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ) +
        ⅟2 * flat σ (cmp₁ w * (ugFst JB h).valᵀ) ⬝ᵥ flat σ (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ) =
      flat σ ((flat σ).symm u * ((ugFst JB h)⁻¹).valᵀ) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ) +
        ⅟2 * flat σ (cmp₁ w) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (flat σ) u]
    rw [flat_dot, flat_dot, flat_dot, flat_dot, m1, m2]
  rw [eX, eP]
  ring
end GlobalTheory.WeilM
