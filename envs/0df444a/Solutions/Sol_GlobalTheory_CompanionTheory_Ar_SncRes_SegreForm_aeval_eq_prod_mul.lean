-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.aeval_eq_prod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:24.949092+00:00
-- url     : https://prove2.me/submissions/19b5d812-7aca-446c-a7d6-392ad8a5e5e4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_aeval_blockScale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
theorem _root_.solution (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b) :
    aeval y β = (∏ k, y ⟨k, E c₀ k⟩ ^ b k) *
      aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := by
  have h := GlobalTheory.CompanionTheory.Ar.aeval_blockScale hb (fun k => y ⟨k, E c₀ k⟩) (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩)
  have e : (fun p : Σ k, ι k => y ⟨p.1, E c₀ p.1⟩ * (y p / y ⟨p.1, E c₀ p.1⟩)) = y :=
    funext fun p => mul_div_cancel₀ _ (hc p.1)
  rwa [e] at h
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
