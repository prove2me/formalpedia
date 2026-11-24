-- Prove2me | solution 1 for GlobalTheory.CovolumeOneSelfDual.unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:48.795862+00:00
-- url     : https://prove2.me/submissions/70dcb8f8-ae46-4af2-82fb-bb3683d754d4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.CovolumeOneSelfDual
namespace GlobalTheory.CovolumeOneSelfDual
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (hF : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : Γ => ‖c (γ + y)‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' γ : Γ, c (γ + y) ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun y => c (γ + y)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_left μ (γ : G)).quasiMeasurePreserving
    exact this.restrict
  have hl : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    rfl
  have hfin : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne
  refine ⟨?_, ?_⟩
  · have h1 : ∫⁻ y in 𝓕, ∑' γ : Γ, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : Γ, ‖c (γ + y)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : Γ, (‖c (γ + y)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  · rw [integral_tsum hm hfin, hF.integral_eq_tsum'' c hc]
    rfl
end GlobalTheory.CovolumeOneSelfDual
