-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.Irred.eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:01:39.54058+00:00
-- url     : https://prove2.me/submissions/def7823e-2630-483d-ad95-707ceca0d51e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_rho_comm
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis GlobalTheory.CompanionTheory.FinHeis.Irred
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
namespace GlobalTheory.CompanionTheory.FinHeis.Irred
theorem _root_.solution {al : X → ℂ} {Γ : AddSubgroup X} {φ : M} (hs : IsSemi S al Γ) (hl : Law S al Γ φ)
    {γ : X} (hγ : γ ∈ Γ) (x : X) :
    al γ • S.rho γ (S.rho x φ) = S.c γ x ^ 2 • S.rho x φ := by
  have ha : al γ ≠ 0 := by
    rcases hs.1 γ hγ with h | h <;> rw [h] <;> norm_num
  rw [rho_comm, hl γ hγ, map_smul, smul_smul, smul_smul]
  congr 1
  field_simp
end GlobalTheory.CompanionTheory.FinHeis.Irred
