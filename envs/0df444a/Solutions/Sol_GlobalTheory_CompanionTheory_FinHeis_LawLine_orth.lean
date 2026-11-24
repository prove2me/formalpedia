-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.LawLine.orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:34.05114+00:00
-- url     : https://prove2.me/submissions/749bce8d-2f70-4f05-8236-6ce167f5f85e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_RationalFiniteIdeleFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_LawLine_rho_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.LawLine
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.CompanionTheory.FinHeis.LawLine
theorem _root_.solution (S : Sys X M) (al : X → ℂ) (Γ : AddSubgroup X) (φ φ' : M) (x : X)
    (hΓ : SelfDual S Γ) (hal : IsSemi S al Γ) (hφ : Law S al Γ φ) (hφ' : Law S al Γ φ')
    (hx : x ∉ Γ) : S.B φ' (S.rho x φ) = 0 := by
  have hΓ₀ : ∀ y, y ∈ Γ ↔ ∀ γ ∈ Γ, S.c γ y ^ 2 = 1 := hΓ
  obtain ⟨hal₁, -⟩ : (∀ y ∈ Γ, al y = 1 ∨ al y = -1) ∧
      ∀ y ∈ Γ, ∀ z ∈ Γ, al (y + z) = al y * al z * S.c y z := hal
  have hφ₀ : ∀ γ ∈ Γ, S.rho γ φ = (al γ)⁻¹ • φ := hφ
  have hφ₀' : ∀ γ ∈ Γ, S.rho γ φ' = (al γ)⁻¹ • φ' := hφ'
  have hnot : ¬ ∀ γ ∈ Γ, S.c γ x ^ 2 = 1 := fun h => hx ((hΓ₀ x).2 h)
  push_neg at hnot
  obtain ⟨γ, hγ, hcx⟩ := hnot
  have hinv := S.12 γ φ' (S.rho x φ)
  rw [hφ₀' γ hγ, GlobalTheory.CompanionTheory.FinHeis.LawLine.rho_comm S γ x φ, hφ₀ γ hγ] at hinv
  simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul] at hinv
  have hunit : (starRingEnd ℂ) (al γ)⁻¹ * (al γ)⁻¹ = 1 := by
    rcases hal₁ γ hγ with h1 | h1 <;> simp [h1]
  have hzero : (S.c γ x ^ 2 - 1) * S.B φ' (S.rho x φ) = 0 := by
    linear_combination hinv - (S.c γ x ^ 2 * S.B φ' (S.rho x φ)) * hunit
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd (sub_eq_zero.1 h) hcx
  · exact h
end GlobalTheory.CompanionTheory.FinHeis.LawLine
