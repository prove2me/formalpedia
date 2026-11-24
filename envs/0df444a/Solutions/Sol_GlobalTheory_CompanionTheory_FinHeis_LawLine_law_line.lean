-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.LawLine.law_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:22:32.748878+00:00
-- url     : https://prove2.me/submissions/8eeee0f3-eb40-421b-8d7f-941343729daf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_RationalFiniteIdeleFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_LawLine_orth

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
theorem _root_.solution {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
    (al : X → ℂ) (Γ : AddSubgroup X) (φ φ' : M) (hΓ : SelfDual S Γ) (hal : IsSemi S al Γ)
    (hφ : Law S al Γ φ) (hc : Cyclic S φ) (hφ' : Law S al Γ φ') : ∃ a : ℂ, φ' = a • φ := by
  have hφ₀ : ∀ γ ∈ Γ, S.rho γ φ = (al γ)⁻¹ • φ := hφ
  have hφ₀' : ∀ γ ∈ Γ, S.rho γ φ' = (al γ)⁻¹ • φ' := hφ'
  have hc₀ : Submodule.span ℂ (Set.range fun x => S.rho x φ) = ⊤ := hc
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = S.B φ φ' / S.B φ φ := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : M, ψ = φ' - a • φ := ⟨_, rfl⟩
  have hψeig : ∀ γ ∈ Γ, S.rho γ ψ = (al γ)⁻¹ • ψ := by
    intro γ hγ
    rw [hψ, map_sub, map_smul, hφ₀' γ hγ, hφ₀ γ hγ, smul_sub, smul_comm (al γ)⁻¹ a φ]
  have hBφψ : S.B φ ψ = 0 := by
    by_cases h0 : φ = 0
    · rw [h0, map_zero, LinearMap.zero_apply]
    · have hpos := S.11 φ h0
      have hne : S.B φ φ ≠ 0 := fun h => by
        rw [h, Complex.zero_re] at hpos
        exact lt_irrefl _ hpos
      rw [hψ, map_sub, map_smul, smul_eq_mul, ha, div_mul_cancel₀ _ hne, sub_self]
  have hall : ∀ x, S.B ψ (S.rho x φ) = 0 := by
    intro x
    by_cases hx : x ∈ Γ
    · rw [hφ₀ x hx, map_smul, smul_eq_mul, ← S.10 φ ψ, hBφψ, map_zero, mul_zero]
    · exact GlobalTheory.CompanionTheory.FinHeis.LawLine.orth S al Γ φ ψ x hΓ hal hφ hψeig hx
  have hker : Submodule.span ℂ (Set.range fun x => S.rho x φ) ≤ LinearMap.ker (S.B ψ) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hall x
  have hmem : ψ ∈ Submodule.span ℂ (Set.range fun x => S.rho x φ) := by
    rw [hc₀]
    exact Submodule.mem_top
  have hψψ : S.B ψ ψ = 0 := LinearMap.mem_ker.1 (hker hmem)
  have hψ0 : ψ = 0 := by
    by_contra hne
    have hpos := S.11 ψ hne
    rw [hψψ, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  refine ⟨a, ?_⟩
  rw [hψ] at hψ0
  exact sub_eq_zero.1 hψ0
end GlobalTheory.CompanionTheory.FinHeis.LawLine
