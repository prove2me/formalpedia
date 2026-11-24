-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PRep.JacExact.avg_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:08.705743+00:00
-- url     : https://prove2.me/submissions/5da86288-afdf-4a21-9517-239e2ec058f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_JacExact_avg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PRep GlobalTheory.CompanionTheory.PRep.JacExact
variable {L V W : Type} [Group L] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.PRep.JacExact
theorem _root_.solution (τ : Representation ℂ L V) (χ : L →* ℂˣ) (M : Subgroup L) [M.Normal]
    [Fintype (L ⧸ M)] (hχ : M ≤ χ.ker) (x : V) (hx : ∀ m ∈ M, τ m x = x) (n : L) :
    avg τ χ M (τ n x) = ((χ n : ℂˣ) : ℂ) • avg τ χ M x := by
  set F : L → V := fun t => (((χ t)⁻¹ : ℂˣ) : ℂ) • τ t x with hFdef
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ M) = QuotientGroup.mk b → F a = F b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ M := QuotientGroup.eq.1 hab
    have hb : b = a * (a⁻¹ * b) := by group
    have hc : χ (a⁻¹ * b) = 1 := hχ hm
    have ht : τ b x = τ a x := by
      rw [hb, map_mul, Module.End.mul_apply, hx _ hm]
    have hcb : χ b = χ a := by
      rw [hb, map_mul, hc, mul_one]
    simp only [hFdef, ht, hcb]
  have h1 : ∀ q : L ⧸ M, (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) • τ (Quotient.out q) (τ n x)
      = ((χ n : ℂˣ) : ℂ) • F (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
    intro q
    have hq : (QuotientGroup.mk (Quotient.out q * n) : L ⧸ M)
        = QuotientGroup.mk (Quotient.out (q * (QuotientGroup.mk n : L ⧸ M))) := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [← hF _ _ hq]
    simp only [hFdef, map_mul, mul_inv, Units.val_mul, smul_smul, Module.End.mul_apply]
    congr 1
    have : ((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)
        = (((χ n : ℂˣ) : ℂ) * (((χ n)⁻¹ : ℂˣ) : ℂ)) * (((χ (Quotient.out q))⁻¹ : ℂˣ) : ℂ) := by
          rw [this, one_mul]
      _ = _ := by ring
  rw [avg_apply, avg_apply, Finset.sum_congr rfl (fun q _ => h1 q), ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk n : L ⧸ M))
    (fun q => F (Quotient.out q))
end GlobalTheory.CompanionTheory.PRep.JacExact
