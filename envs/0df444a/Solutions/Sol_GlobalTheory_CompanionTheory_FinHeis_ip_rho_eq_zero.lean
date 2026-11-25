-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.ip_rho_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:29.549257+00:00
-- url     : https://prove2.me/submissions/0402043a-0775-44e9-8d7a-68f73209ca03

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_ip_rho
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Sys_rho_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_IsSemi_conj_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
variable {S}
namespace GlobalTheory.CompanionTheory.FinHeis
theorem _root_.solution {al : X → ℂ} {Γ : AddSubgroup X} (hΓ : SelfDual S Γ) (h : IsSemi S al Γ) {φ : M}
    (hφ : Law S al Γ φ) {x : X} (hx : x ∉ Γ) : ip S (S.rho x φ) φ = 0 := by
  have : ¬ ∀ γ ∈ Γ, S.c γ x ^ 2 = 1 := fun hh => hx ((hΓ x).2 hh)
  push Not at this
  obtain ⟨γ, hγ, hne⟩ := this
  have e1 := ip_rho S γ (S.rho x φ) φ
  rw [S.rho_comm γ x, hφ γ hγ, h.inv_eq hγ, map_smul (S.rho x), ip_smul_left, ip_smul_left, ip_smul_right,
    h.conj_eq hγ] at e1
  have : (S.c γ x ^ 2 - 1) * ip S (S.rho x φ) φ = 0 := by
    linear_combination e1 - S.c γ x ^ 2 * ip S (S.rho x φ) φ * h.mul_self hγ
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
end GlobalTheory.CompanionTheory.FinHeis
