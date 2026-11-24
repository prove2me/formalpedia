-- Prove2me | solution 1 for GlobalTheory.ClassIntegral.measure_dcoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:51.025427+00:00
-- url     : https://prove2.me/submissions/b32bef9d-1980-42bc-bb85-e6eabe525d92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum
import Theorems.Thm_GlobalTheory_ClassIntegral_measurableSet_dcoset
import Theorems.Thm_GlobalTheory_ClassIntegral_tsum_indicator_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace GlobalTheory.ClassIntegral
theorem _root_.solution (Γ K : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) (g : G) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (∑' _ : {γ : Γ // g⁻¹ * (γ : G) * g ∈ K}, (1 : ENNReal)) * μ.restrict 𝓕 (dcoset Γ K g) = 1 := by
  have i1 : MeasurableConstSMul Γ G :=
    ⟨fun γ => by simpa [Subgroup.smul_def, smul_eq_mul] using measurable_const_mul (γ : G)⟩
  have i2 : SMulInvariantMeasure Γ G μ :=
    ⟨fun γ s _ => by
      have : ((fun x => γ • x) ⁻¹' s) = ((fun x => (γ : G) * x) ⁻¹' s) := by
        ext x; simp [Subgroup.smul_def, smul_eq_mul]
      rw [this, measure_preimage_mul]⟩
  have hT : MeasurableSet ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)) := (measurable_const_mul _) hK
  have hf : Measurable (((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)) :=
    measurable_one.indicator hT
  have hC := measurableSet_dcoset Γ K hK g
  rw [← lintegral_indicator_one hC, ← lintegral_const_mul _ (measurable_one.indicator hC)]
  simp only [← tsum_indicator_eq]
  have hmeas : ∀ γ : Γ, Measurable fun x : G =>
      ((fun y => g⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x) :=
    fun γ => hf.comp (measurable_const_smul γ)
  rw [lintegral_tsum fun γ => (hmeas γ).aemeasurable,
    ← h𝓕.lintegral_eq_tsum'', lintegral_indicator_one hT, measure_preimage_mul, hK1]
end GlobalTheory.ClassIntegral
