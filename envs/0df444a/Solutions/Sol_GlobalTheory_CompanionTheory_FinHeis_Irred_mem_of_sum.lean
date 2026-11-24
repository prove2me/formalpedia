-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Irred.mem_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:18:58.384681+00:00
-- url     : https://prove2.me/submissions/3d0391b6-b8b8-4f76-9e04-865fbf3f2f6d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_c_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_eigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.Irred
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
namespace GlobalTheory.CompanionTheory.FinHeis.Irred
theorem _root_.solution {al : X → ℂ} {Γ : AddSubgroup X} {φ : M} (hd : SelfDual S Γ)
    (hs : IsSemi S al Γ) (hl : Law S al Γ φ) (N : Submodule ℂ M)
    (hN : ∀ x, ∀ v ∈ N, S.rho x v ∈ N) (s : Finset X) :
    ∀ a : X → ℂ, (∑ x ∈ s, a x • S.rho x φ) ∈ N → (∑ x ∈ s, a x • S.rho x φ) ≠ 0 → φ ∈ N := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro a hm hne
    have key : ∀ γ ∈ Γ, ∀ x₀ ∈ s,
        al γ • S.rho γ (∑ x ∈ s, a x • S.rho x φ) - S.c γ x₀ ^ 2 • (∑ x ∈ s, a x • S.rho x φ)
          = ∑ x ∈ s.erase x₀, (a x * (S.c γ x ^ 2 - S.c γ x₀ ^ 2)) • S.rho x φ := by
      intro γ hγ x₀ _
      rw [Finset.sum_erase _ (by simp), map_sum, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, smul_comm (al γ), eigen S hs hl hγ, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    by_cases h : ∃ γ ∈ Γ, ∃ x₀ ∈ s,
        (∑ x ∈ s.erase x₀, (a x * (S.c γ x ^ 2 - S.c γ x₀ ^ 2)) • S.rho x φ) ≠ 0
    · obtain ⟨γ, hγ, x₀, hx₀, h⟩ := h
      refine ih (s.erase x₀) (Finset.erase_ssubset hx₀) _ ?_ h
      rw [← key γ hγ x₀ hx₀]
      exact N.sub_mem (N.smul_mem _ (hN _ _ hm)) (N.smul_mem _ hm)
    · push Not at h
      obtain ⟨x₀, hx₀⟩ : s.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hne (by simp)
      have hΓ : ∀ x ∈ s, x - x₀ ∈ Γ := by
        intro x hx
        refine (hd _).2 fun γ hγ => ?_
        have h1 := key γ hγ x hx
        have h2 := key γ hγ x₀ hx₀
        rw [h γ hγ x hx, sub_eq_zero] at h1
        rw [h γ hγ x₀ hx₀, sub_eq_zero, h1] at h2
        have h3 : S.c γ x ^ 2 = S.c γ x₀ ^ 2 := smul_left_injective ℂ hne h2
        have h4 := S.c_add_right γ (x - x₀) x₀
        rw [sub_add_cancel] at h4
        rw [h4, mul_pow] at h3
        exact mul_right_cancel₀ (pow_ne_zero 2 (c_ne S γ x₀)) (by rw [h3, one_mul])
      have hx : ∀ x ∈ s, S.rho x φ = ((S.c x₀ (x - x₀))⁻¹ * (al (x - x₀))⁻¹) • S.rho x₀ φ := by
        intro x hx
        have h1 := S.rho_rho x₀ (x - x₀) φ
        rw [hl _ (hΓ x hx), map_smul, add_sub_cancel] at h1
        rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ (c_ne S _ _), one_smul]
      have hv : (∑ x ∈ s, a x • S.rho x φ)
          = (∑ x ∈ s, a x * ((S.c x₀ (x - x₀))⁻¹ * (al (x - x₀))⁻¹)) • S.rho x₀ φ := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun x hxs => ?_
        rw [hx x hxs, smul_smul]
      rw [hv] at hm hne
      have h0 := (N.smul_mem_iff (left_ne_zero_of_smul hne)).1 hm
      have h1 := hN (-x₀) _ h0
      rw [S.rho_rho, neg_add_cancel, S.rho_zero] at h1
      exact (N.smul_mem_iff (c_ne S _ _)).1 h1
end GlobalTheory.CompanionTheory.FinHeis.Irred
