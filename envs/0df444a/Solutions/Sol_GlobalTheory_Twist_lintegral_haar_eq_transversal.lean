-- Prove2me | solution 1 for GlobalTheory.Twist.lintegral_haar_eq_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:06.25636+00:00
-- url     : https://prove2.me/submissions/2874f8ff-aeb1-45eb-b4af-6d89fafb6c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LintegralHaarEqCompactSubgroupTransversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.Twist
namespace GlobalTheory.Twist
theorem _root_.solution (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G)
    (he : Measurable e) (hK : mK Kᶜ = 0)
    (hinv : ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) (hlam : lam ≠ 0)
    (hfin : ∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤)
    (hact : ∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧
      ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
  have hm : Measurable (fun z : E × G => z.2 * e z.1) :=
    measurable_snd.mul (he.comp measurable_fst)
  set ν : Measure G := Measure.map (fun z : E × G => z.2 * e z.1) (lam.prod mK) with hν
  have hint : ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂ν = ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by
    intro f hf
    rw [hν, lintegral_map hf hm]
    exact lintegral_prod (fun z : E × G => f (z.2 * e z.1)) (hf.comp hm).aemeasurable
  have hH : ∀ f : G → ENNReal, Measurable f →
      Measurable (fun B => ∫⁻ k, f (k * e B) ∂mK) := by
    intro f hf
    exact Measurable.lintegral_prod_right' (f := fun z : E × G => f (z.2 * e z.1)) (hf.comp hm)
  have hR : ν.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨ψ, hψ, hψl, hψe⟩ := hact g
    refine Measure.ext_of_lintegral _ (fun f hf => ?_)
    have hg : Measurable (fun x : G => x * g) := measurable_mul_const g
    rw [lintegral_map hf hg, hint (fun x => f (x * g)) (hf.comp hg), hint f hf]
    have h1 : ∀ B, ∫⁻ k, f (k * e B * g) ∂mK = ∫⁻ k, f (k * e (ψ B)) ∂mK := by
      intro B
      obtain ⟨κ, hκ, hk⟩ := hψe B
      have h2 := lintegral_map (μ := mK) (f := fun x => f (x * e (ψ B))) (g := fun x => x * κ)
        (hf.comp (measurable_mul_const _)) (measurable_mul_const κ)
      rw [hinv κ hκ] at h2
      rw [h2]
      simp only [mul_assoc, hk]
    simp only [h1]
    have h3 := lintegral_map (μ := lam) (hH f hf) hψ
    rw [hψl] at h3
    exact h3.symm
  have hF : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun C hC => ?_⟩
    have hCm : MeasurableSet C := hC.measurableSet
    have h1 := hint (C.indicator 1) (measurable_one.indicator hCm)
    rw [lintegral_indicator_one hCm] at h1
    rw [h1]
    set S := {B | ∃ k ∈ K, k * e B ∈ C} with hS
    refine lt_of_le_of_lt ?_ (hfin C hC)
    rw [← measure_toMeasurable, ← lintegral_indicator_one (measurableSet_toMeasurable _ _)]
    refine lintegral_mono (fun B => ?_)
    by_cases hB : B ∈ toMeasurable lam S
    · rw [Set.indicator_of_mem hB]
      calc ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK ≤ ∫⁻ _k, 1 ∂mK :=
            lintegral_mono (fun k => Set.indicator_le_self' (fun _ _ => zero_le_one) _)
        _ = 1 := by simp
    · rw [Set.indicator_of_notMem hB]
      have hB' : B ∉ S := fun h => hB (subset_toMeasurable _ _ h)
      have hae : ∀ᵐ k ∂mK, k ∈ K := hK
      have : ∫⁻ k, C.indicator (1 : G → ENNReal) (k * e B) ∂mK = ∫⁻ _k, 0 ∂mK := by
        refine lintegral_congr_ae (hae.mono fun k hk => ?_)
        exact Set.indicator_of_notMem (fun h => hB' ⟨k, hk, h⟩) _
      simp [this]
  have hν0 : ν ≠ 0 := by
    intro h
    have h1 := hint (fun _ => 1) measurable_const
    rw [h] at h1
    simp at h1
    exact hlam (Measure.measure_univ_eq_zero.mp h1.symm)
  have hmul := Measure.isMulLeftInvariant_eq_smul ν.inv μ
  set c := Measure.haarScalarFactor ν.inv μ with hc
  have hνc : ν = c • μ := by
    have : ν.inv.inv = (c • μ).inv := by rw [← hmul]
    rw [Measure.inv_inv] at this
    rw [this]
    change Measure.map _ (c • μ) = _
    rw [Measure.map_smul, Measure.map_inv_eq_self]
  have hc0 : c ≠ 0 := by
    intro h
    apply hν0
    rw [hνc, h, zero_smul]
  refine ⟨((c⁻¹ : NNReal) : ℝ), by exact_mod_cast inv_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf => ?_⟩
  rw [← hint f hf, hνc, lintegral_smul_measure, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul,
    ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0]
  simp
end GlobalTheory.Twist
