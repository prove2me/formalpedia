-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.la_eq_sqrt_smul_Lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:31.966458+00:00
-- url     : https://prove2.me/submissions/e7748f08-8fb7-4f91-acfb-673d2e044c83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam

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
theorem _root_.solution (al : X → ℂ) {Γ Γ' : AddSubgroup X} (hN : Γ.relIndex Γ' ≠ 0) (φ : M) :
    la S al Γ' Γ φ = ((Real.sqrt (Γ.relIndex Γ' : ℝ) : ℝ) : ℂ) • abelian₂ S al Γ' Γ φ := by
  have : ((Real.sqrt (Γ.relIndex Γ' : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (Γ.relIndex Γ' : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  rw [abelian₂, smul_smul, mul_inv_cancel₀ this, one_smul]
end GlobalTheory.CompanionTheory.FinHeis
