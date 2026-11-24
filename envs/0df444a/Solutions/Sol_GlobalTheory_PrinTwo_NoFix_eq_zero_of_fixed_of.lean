-- Prove2me | solution 1 for GlobalTheory.PrinTwo.NoFix.eq_zero_of_fixed_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:24.43055+00:00
-- url     : https://prove2.me/submissions/2cab0f0a-0f68-4b89-ba0e-5e2dc972a62d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramifiedPrincipalSeriesNoInvariant
import Theorems.Thm_GlobalTheory_PrinTwo_NoFix_exists_unif
import Theorems.Thm_GlobalTheory_PrinTwo_NoFix_isUnram_mul
import Theorems.Thm_GlobalTheory_PrinTwo_NoFix_bchar_shift
import Theorems.Thm_GlobalTheory_PrinTwo_NoFix_val_lt_val_mul_inv
import Theorems.Thm_GlobalTheory_PrinTwo_bchar_ne_zero
import Theorems.Thm_GlobalTheory_PrinTwo_ev_act
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_eq_unrChar
import Theorems.Thm_GlobalTheory_SmGL_isUnram_absPow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo
open GlobalTheory GlobalTheory.PrinTwo GlobalTheory.PrinTwo.NoFix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo.NoFix
theorem _root_.solution
    (hinj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0)
    (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1)
    {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) (hne : μ₂ ≠ μ₁ * absPow k 1)
    (f : PSp μ₁ μ₂) (hf : ∀ x : k, psRep μ₁ μ₂ (nU x) f = f) : f = 0 := by
  have hc : ∀ x : k, coord f x = ev f wE := fun x => by
    rw [coord, ← ev_act, hf x]
  obtain ⟨R, hR⟩ := hasy k μ₁ μ₂ f
  obtain ⟨ϖ, hϖ⟩ := exists_unif k
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x = R * ϖ⁻¹ := ⟨_, rfl⟩
  have hxR : valuation k (R : k) < valuation k (x : k) := hx ▸ val_lt_val_mul_inv hϖ R
  have hx'R : valuation k (R : k) < valuation k ((x * ϖ⁻¹ : kˣ) : k) :=
    hxR.trans (val_lt_val_mul_inv hϖ x)
  have h1 : ev f 1 = 0 := by
    by_contra h0
    apply hne
    have e := (hR x hxR).symm.trans ((hc x).trans ((hc _).symm.trans (hR _ hx'R)))
    have e2 : bchar μ₁ μ₂ (-(x * ϖ⁻¹)⁻¹) (x * ϖ⁻¹) =
        bchar μ₁ μ₂ (-x⁻¹) x * ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) := by
      rw [← bchar_shift]
      congr 1
      rw [mul_inv_rev, inv_inv, neg_mul, mul_comm]
    rw [e2, mul_assoc] at e
    have e3 := mul_left_cancel₀ (bchar_ne_zero μ₁ μ₂ _ _) e
    have e4 : ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e3.symm.trans (one_mul _).symm)
      exact this
    have e5 : μ₂ ϖ = (μ₁ * absPow k 1) ϖ := by
      rw [MonoidHom.mul_apply]
      exact (div_eq_one.1 (Units.ext e4)).symm
    rw [eq_unrChar h₂ hϖ, eq_unrChar (isUnram_mul h₁ (isUnram_absPow k 1)) hϖ, e5]
  refine hinj k μ₁ μ₂ f h1 fun y => ?_
  rw [hc y, ← hc x, hR x hxR, h1, mul_zero]
end GlobalTheory.PrinTwo.NoFix
