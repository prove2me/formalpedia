-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.lintegral_fibFam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:51.993812+00:00
-- url     : https://prove2.me/submissions/2ee6518f-522d-4006-9ee3-fa9e769bc0b9

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_theta_isOpenEmbedding
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_orbit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_off
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_continuous_smul_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution [T2Space V] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) (μ : Measure V) (ν : Measure X)
    (χ χ' : Q →* ℝ≥0) (hχ : Continuous χ) (hχ' : Continuous χ')
    (m : Measure (g ⁻¹' {b₀})) [SFinite m]
    [SFinite ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞)))]
    (hm : (μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞)) =
        ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))).prod m)
    {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
      ∫⁻ b, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν := by
  obtain ⟨hΘ, hr⟩ := theta_isOpenEmbedding (Q := Q) hg heq ho
  have hΘm := hΘ.measurableEmbedding
  have hom := ho.measurableEmbedding
  have hχm : Measurable (fun q : Q => (χ q : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hχ.measurable
  have hχim : Measurable (fun q : Q => (χ q⁻¹ : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (hχ.comp continuous_inv).measurable
  have hχ'm : Measurable (fun q : Q => (χ' q : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp hχ'.measurable
  have hF : Measurable (fun p : Q × (g ⁻¹' {b₀}) => (χ p.1⁻¹ : ℝ≥0∞) * φ (theta g b₀ p)) :=
    (hχim.comp measurable_fst).mul (hφ.comp hΘm.measurable)

  have hleft : ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
      ∫⁻ q, (χ' q : ℝ≥0∞) * ∫⁻ z : (g ⁻¹' {b₀}), (χ q⁻¹ : ℝ≥0∞) * φ (q • (z : V)) ∂m
        ∂(ν.comap (fun q : Q => q • b₀)) := by
    have h1 : ∫⁻ v in g ⁻¹' Set.range (fun q : Q => q • b₀), φ v ∂μ =
        ∫⁻ p, φ (theta g b₀ p) ∂(μ.comap (theta (Q := Q) g b₀)) := by
      rw [← hr, ← hΘm.map_comap μ, lintegral_map hφ hΘm.measurable]
    have h2 : ∫⁻ p, φ (theta g b₀ p) ∂(μ.comap (theta (Q := Q) g b₀)) =
        ∫⁻ p, (χ p.1⁻¹ : ℝ≥0∞) * φ (theta g b₀ p)
          ∂((μ.comap (theta (Q := Q) g b₀)).withDensity (fun p => (χ p.1 : ℝ≥0∞))) := by
      have hd : Measurable (fun p : Q × (g ⁻¹' {b₀}) => (χ p.1 : ℝ≥0∞)) :=
        hχm.comp measurable_fst
      rw [lintegral_withDensity_eq_lintegral_mul _ hd hF]
      refine lintegral_congr fun p => ?_
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one,
        one_mul]
    rw [h1, h2, hm, lintegral_prod _ hF.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hχ'm hF.lintegral_prod_right']
    rfl

  have hright : ∫⁻ b, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν =
      ∫⁻ q, ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m (q • b₀))
        ∂(ν.comap (fun q : Q => q • b₀)) := by
    have hB : MeasurableSet (Set.range (fun q : Q => q • b₀)) := ho.isOpen_range.measurableSet
    have hoff : ∫⁻ b in (Set.range (fun q : Q => q • b₀))ᶜ,
        ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b) ∂ν = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => 0) hB.compl]
      · simp
      · intro b hb
        simp only
        rw [fibFam_off _ m hb]
        simp
    have hmap := hom.lintegral_map (μ := ν.comap (fun q : Q => q • b₀))
      (fun b => ∫⁻ v, φ v ∂(fibFam g b₀ (fun q => χ' q * χ q⁻¹) m b))
    rw [hom.map_comap] at hmap
    rw [← lintegral_add_compl _ hB, hoff, add_zero]
    exact hmap
  rw [hleft, hright]
  refine lintegral_congr fun q => ?_
  have hc : ∫⁻ z : (g ⁻¹' {b₀}), (χ q⁻¹ : ℝ≥0∞) * φ (q • (z : V)) ∂m =
      (χ q⁻¹ : ℝ≥0∞) * ∫⁻ z : (g ⁻¹' {b₀}), φ (q • (z : V)) ∂m :=
    lintegral_const_mul _ (hφ.comp (continuous_smul_fib g b₀ q).measurable)
  rw [fibFam_orbit _ m ho.injective, lintegral_smul_measure,
    lintegral_map hφ (continuous_smul_fib g b₀ q).measurable, hc, smul_eq_mul,
    ENNReal.coe_mul, mul_assoc]
end GlobalTheory.CompanionTheory.SW.Slice
