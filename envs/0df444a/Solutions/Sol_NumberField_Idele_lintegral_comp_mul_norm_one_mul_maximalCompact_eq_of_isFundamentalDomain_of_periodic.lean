-- Prove2me | solution 1 for NumberField.Idele.lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5bbaa274-6b3e-5f37-bd2c-8eeabdb14178

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

open scoped Pointwise in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
    (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (f : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℝ≥0∞) (_hf : Measurable f)
    (_hper : ∀ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F →
      ∀ (t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)), f (γ * t, k) = f (t, k))
    (c : (AdeleRing (𝓞 F) F)ˣ) (_hc : NumberField.TateGlobal.ideleNorm F c = 1)
    (b : ↥(adelicMaximalCompact F)) :
    ∫⁻ p, f (p.1 * c, b * p.2)
        ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) =
      ∫⁻ p, f p
        ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) := by
  classical
  haveI hIH := NumberField.Idele.isHaarMeasure_idelicHaar F

  haveI : Countable F := by
    obtain ⟨n, b⟩ : Σ n, Module.Basis (Fin n) ℚ F := ⟨_, Module.finBasis ℚ F⟩
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable Fˣ := Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  haveI : Countable ↥(M4aHerbrand.principalIdeles (𝓞 F) F) :=
    (Set.countable_range (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) :
      Fˣ → (AdeleRing (𝓞 F) F)ˣ)).to_subtype

  haveI : SMulCommClass (AdeleRing (𝓞 F) F)ˣ ↥(M4aHerbrand.principalIdeles (𝓞 F) F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun a g x => mul_left_comm a (g : (AdeleRing (𝓞 F) F)ˣ) x⟩
  haveI : MeasurableConstSMul ↥(M4aHerbrand.principalIdeles (𝓞 F) F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun g => (continuous_mul_left (g : (AdeleRing (𝓞 F) F)ˣ)).measurable⟩

  set ν := maximalCompactHaar F with hν
  set w : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun t => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) with hw
  have hwm : Measurable w :=
    ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm F).measurable.inv)
  have hwc : ∀ t, w (c * t) = w t := fun t => by
    simp only [hw, NumberField.TateGlobal.ideleNorm_mul, _hc, one_mul]
  have hnormγ : ∀ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F → NumberField.TateGlobal.ideleNorm F γ = 1 := by
    rintro γ ⟨a, rfl⟩
    simp only [NumberField.TateGlobal.ideleNorm]
    rw [show (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) a =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a from rfl,
      NumberField.AdeleRing.distribHaarChar_algebraMap F a, NNReal.coe_one]
  have hwγ : ∀ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F → ∀ t, w (γ * t) = w t := fun γ hγ t => by
    simp only [hw, NumberField.TateGlobal.ideleNorm_mul, hnormγ γ hγ, one_mul]
  set h : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun t => ∫⁻ k, f (t, k) ∂ν with hh
  have hhm : Measurable h := _hf.lintegral_prod_right'
  have hhγ : ∀ γ : (AdeleRing (𝓞 F) F)ˣ, γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F → ∀ t, h (γ * t) = h t := fun γ hγ t => by
    simp only [hh, _hper γ hγ]
  set H : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞ := fun t => w t * h t with hH
  have hHm : Measurable H := hwm.mul hhm
  have hHγ : ∀ (γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) (t : (AdeleRing (𝓞 F) F)ˣ), H (γ • t) = H t := fun γ t => by
    show w ((γ : (AdeleRing (𝓞 F) F)ˣ) * t) * h ((γ : (AdeleRing (𝓞 F) F)ˣ) * t) = w t * h t
    rw [hwγ _ γ.2, hhγ _ γ.2]

  have hinner : ∀ t : (AdeleRing (𝓞 F) F)ˣ, ∫⁻ k, f (t, b * k) ∂ν = h t := by
    intro t
    have hm : Measurable fun k : ↥(adelicMaximalCompact F) => f (t, k) := _hf.comp measurable_prodMk_left
    calc ∫⁻ k, f (t, b * k) ∂ν = ∫⁻ k, (fun k => f (t, k)) k ∂(Measure.map (fun k => b * k) ν) :=
          (lintegral_map hm (continuous_mul_left b).measurable).symm
      _ = h t := by rw [map_mul_left_eq_self]

  have hmeasL : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => f (p.1 * c, b * p.2) :=
    _hf.comp (Measurable.prodMk ((continuous_mul_right c).measurable.comp measurable_fst)
      ((continuous_mul_left b).measurable.comp measurable_snd))
  have hL : ∫⁻ p, f (p.1 * c, b * p.2)
        ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity w).prod ν) =
      ∫⁻ t in D, H (c * t) ∂(NumberField.Idele.idelicHaar F) := by
    rw [lintegral_prod _ hmeasL.aemeasurable]
    simp_rw [hinner]
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm
      (show Measurable (fun t : (AdeleRing (𝓞 F) F)ˣ => h (t * c)) from hhm.comp (continuous_mul_right c).measurable)]
    refine lintegral_congr fun t => ?_
    show w t * h (t * c) = w (c * t) * h (c * t)
    rw [hwc, mul_comm t c]
  have hR : ∫⁻ p, f p ∂((((NumberField.Idele.idelicHaar F).restrict D).withDensity w).prod ν) =
      ∫⁻ t in D, H t ∂(NumberField.Idele.idelicHaar F) := by
    rw [lintegral_prod _ _hf.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hwm hhm]
    rfl
  rw [hL, hR]

  have hcD : ∫⁻ t in D, H (c * t) ∂(NumberField.Idele.idelicHaar F) =
      ∫⁻ t in c • D, H t ∂(NumberField.Idele.idelicHaar F) := by
    have hcDm : MeasurableSet (c • D) := _hDm.const_smul c
    rw [← lintegral_indicator _hDm, ← lintegral_indicator hcDm]
    have hind : ∀ t, D.indicator (fun t => H (c * t)) t = (c • D).indicator H (c * t) := by
      intro t
      by_cases ht : t ∈ D
      · rw [Set.indicator_of_mem ht]
        exact (Set.indicator_of_mem (show c * t ∈ c • D from Set.smul_mem_smul_set_iff.mpr ht) H).symm
      · rw [Set.indicator_of_notMem ht]
        exact (Set.indicator_of_notMem (show c * t ∉ c • D from fun h' => ht (Set.smul_mem_smul_set_iff.mp h')) H).symm
    simp_rw [hind]
    calc ∫⁻ t, (c • D).indicator H (c * t) ∂(NumberField.Idele.idelicHaar F)
        = ∫⁻ t, (c • D).indicator H t ∂(Measure.map (fun t => c * t) (NumberField.Idele.idelicHaar F)) :=
          (lintegral_map ((hHm.indicator hcDm)) (continuous_mul_left c).measurable).symm
      _ = ∫⁻ t, (c • D).indicator H t ∂(NumberField.Idele.idelicHaar F) := by rw [map_mul_left_eq_self]
  rw [hcD]
  exact (_hDF.setLIntegral_eq (_hDF.smul_of_comm c) H hHγ).symm

end

end S_NumberField_Idele_lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic
end P2MW
export P2MW.S_NumberField_Idele_lintegral_comp_mul_norm_one_mul_maximalCompact_eq_of_isFundamentalDomain_of_periodic (solution)
