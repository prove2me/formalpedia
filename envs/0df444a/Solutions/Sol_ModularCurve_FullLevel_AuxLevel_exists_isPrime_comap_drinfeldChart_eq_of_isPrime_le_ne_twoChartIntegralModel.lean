-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1fb5aa0f-ec6c-5592-9653-9b8777cbf71e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

namespace IGREG

theorem mem_span_X_of_constantCoeff_eq_zero {R : Type} [CommRing R] (h : MvPowerSeries (Fin 2) R)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    h ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1} := by
  classical
  let h₁ : MvPowerSeries (Fin 2) R := fun m => if m 0 = 0 then h m else 0
  have hc : ∀ (m : Fin 2 →₀ ℕ) (g : MvPowerSeries (Fin 2) R), MvPowerSeries.coeff m g = g m := fun _ _ => rfl
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ∣ h₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    rw [hc]
    show (if m 0 = 0 then h m else 0) = 0
    split_ifs with hm0
    · have hm : m = 0 := by
        ext i; fin_cases i
        · simpa using hm0
        · simpa using hm1
      subst hm
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
      exact h0
    · rfl
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ∣ (h - h₁) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm0
    rw [map_sub, hc, hc, sub_eq_zero]
    show h m = (if m 0 = 0 then h m else 0)
    rw [if_pos hm0]
  obtain ⟨a, ha⟩ := hX0
  obtain ⟨b, hb⟩ := hX1
  have heq : h = MvPowerSeries.X 0 * a + MvPowerSeries.X 1 * b := by rw [← ha, ← hb, sub_add_cancel]
  rw [heq]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end IGREG

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
      (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
      (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
    (hconst :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))))
    (𝔭 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (h𝔭 : 𝔭.IsPrime)
    (hϖ𝔭 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ 𝔭) (h𝔭y : 𝔭 ≤ y.asIdeal) (h𝔭ne : 𝔭 ≠ y.asIdeal) :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      ∃ P' : Ideal S, P'.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P' ∨ mkS (MvPowerSeries.X 1) ∉ P') ∧
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P' ∧
        Ideal.comap ((e : CMP →+* S).comp (toC.comp germY)) P' = 𝔭 := by
  intro STK CMP toC S mkS germY
  classical

  let φA : A →+* STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom.comp
      ((((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
  have hφAϖ : φA ϖ = ϖz := by rw [hϖz]; rfl
  let ψ : STK →+* S := (e : CMP →+* S).comp toC
  have hψϖ : ψ ϖz = mkS (MvPowerSeries.C (σ ϖ)) := by
    rw [← hφAϖ]; exact hconst ϖ

  letI algASTK : Algebra A STK := φA.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ L := by
    haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite {q * ℓ} ℚ L
    infer_instance
  obtain ⟨htj, hFD, hsep⟩ :=
    ModularCurve.FullLevel.AuxLevel.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq
      q M' ℓ L K hK A j hj
  obtain ⟨hFT, hFT'⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  obtain ⟨hNoeth, -, hDom, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
      A (↥K) hinjAK j hFT hFT' z (fun r => rfl)
  haveI : IsNoetherianRing STK := hNoeth

  have hmaxC : IsLocalRing.maximalIdeal CMP = (IsLocalRing.maximalIdeal STK).map toC :=
    AdicCompletion.maximalIdeal_eq_map
  have hcomap_max : (IsLocalRing.maximalIdeal CMP).comap toC = IsLocalRing.maximalIdeal STK :=
    ((IsLocalRing.maximalIdeal.isMaximal STK).eq_of_le
      (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal CMP).ne_top)
      (by rw [hmaxC]; exact Ideal.le_comap_map)).symm
  obtain ⟨_, hNoethC, -, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing STK (IsLocalRing.maximalIdeal STK)
  haveI : IsNoetherianRing CMP := hNoethC
  haveI : IsNoetherianRing S := isNoetherianRing_of_ringEquiv CMP e
  haveI : Module.FaithfullyFlat STK CMP := by
    refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal STK CMP).mpr ⟨inferInstance, fun I hI htop => ?_⟩
    have hle : I • (⊤ : Submodule STK CMP) ≤ (IsLocalRing.maximalIdeal STK) • ⊤ :=
      Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hI)
    rw [htop, top_le_iff, Ideal.smul_top_eq_map, ← hmaxC] at hle
    have h1 : (1 : CMP) ∈ (IsLocalRing.maximalIdeal CMP).restrictScalars STK := by rw [hle]; trivial
    exact (IsLocalRing.maximalIdeal.isMaximal CMP).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hSmax : ∀ P : Ideal S, P.IsPrime → mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
      mkS (MvPowerSeries.X 0) ∈ P → mkS (MvPowerSeries.X 1) ∈ P → (P.comap ψ).IsMaximal := by
    intro P hP hPπ hP0 hP1
    haveI := hP
    haveI : IsLocalRing S := e.isLocalRing
    have hmS : IsLocalRing.maximalIdeal S ≤ P := by
      intro s hs
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective s
      have hg : ¬ IsUnit g := fun hu' => (IsLocalRing.mem_maximalIdeal _).mp hs (hu'.map mkS)
      rw [MvPowerSeries.isUnit_iff_constantCoeff] at hg
      have hcc : MvPowerSeries.constantCoeff g ∈ Ideal.span {σ ϖ} := by
        rw [← hσϖ]; exact (IsLocalRing.mem_maximalIdeal _).mpr hg
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hcc
      have hdec : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} :=
        IGREG.mem_span_X_of_constantCoeff_eq_zero _ (by simp)
      have h1 : mkS (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ P := by
        have hle : (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}).map mkS ≤ P := by
          rw [Ideal.map_span, Ideal.span_le]
          rintro _ ⟨x, hx, rfl⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          exacts [hP0, hP1]
        exact hle (Ideal.mem_map_of_mem _ hdec)
      have h2 : mkS (MvPowerSeries.C (MvPowerSeries.constantCoeff g)) ∈ P := by
        rw [← hw, map_mul, map_mul]; exact Ideal.mul_mem_left _ _ hPπ
      have h12 := P.add_mem h1 h2
      rwa [map_sub, sub_add_cancel] at h12
    have hle : IsLocalRing.maximalIdeal STK ≤ P.comap ψ := by
      intro s hs
      rw [Ideal.mem_comap]
      apply hmS
      show e (toC s) ∈ IsLocalRing.maximalIdeal S
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
      apply Ideal.mem_map_of_mem
      rw [hmaxC]; exact Ideal.mem_map_of_mem _ hs
    have hne : P.comap ψ ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    rw [← (IsLocalRing.maximalIdeal.isMaximal STK).eq_of_le hne hle]
    exact IsLocalRing.maximalIdeal.isMaximal STK
  have hSURJ : ∀ Q : Ideal STK, Q.IsPrime → ϖz ∈ Q → ¬ Q.IsMaximal →
      ∃ P : Ideal S, P.IsPrime ∧ (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) ∧
        mkS (MvPowerSeries.C (σ ϖ)) ∈ P ∧ P.comap ψ = Q := by
    intro Q hQ hϖQ hQmax
    haveI := hQ
    obtain ⟨P', hP'prime, hP'over⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := STK) (B := CMP) Q
    haveI := hP'prime
    let P : Ideal S := P'.comap (e.symm : S →+* CMP)
    haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ P'
    have hPψ : P.comap ψ = Q := by
      have h1 : P.comap (e : CMP →+* S) = P' := by
        ext x; simp [P]
      show (P.comap (e : CMP →+* S)).comap toC = Q
      rw [h1]; exact hP'over.over.symm
    have hPπ : mkS (MvPowerSeries.C (σ ϖ)) ∈ P := by
      have : ψ ϖz ∈ P := by rw [← Ideal.mem_comap, hPψ]; exact hϖQ
      rwa [hψϖ] at this
    have hPX : mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P := by
      by_contra h
      push Not at h
      exact hQmax (hPψ ▸ hSmax P hPprime hPπ h.1 h.2)
    exact ⟨P, hPprime, hPX, hPπ, hPψ⟩

  obtain ⟨eL, heL1, heL2⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A (↥K) j z y hy
  let eR := eL.commRingCatIsoToRingEquiv
  have heR : ∀ r : A, eR (φA r) = algebraMap A (Localization.AtPrime y.asIdeal) r := fun r => heL1 r
  have hgermY : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      eR (germY a) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) a :=
    fun a => heL2 a
  have hdisj : Disjoint (y.asIdeal.primeCompl : Set ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
      (𝔭 : Set ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) :=
    Set.disjoint_left.mpr fun c hc hc𝔭 => hc (h𝔭y hc𝔭)
  have h𝔭L : (𝔭.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal) 𝔭 h𝔭 hdisj
  let Q : Ideal STK := (𝔭.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (Localization.AtPrime y.asIdeal))).comap (eR : STK →+* Localization.AtPrime y.asIdeal)
  haveI hQprime : Q.IsPrime := Ideal.comap_isPrime _ _
  have hback : (Q.map (eR : STK →+* Localization.AtPrime y.asIdeal)) =
      𝔭.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)) :=
    Ideal.map_comap_of_surjective _ eR.surjective _
  have hQgermY : Q.comap germY = 𝔭 := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap]
    show eR (germY a) ∈ _ ↔ _
    rw [hgermY]
    have h := IsLocalization.under_map_of_isPrime_disjoint y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal) h𝔭 hdisj
    constructor
    · intro ha
      have : a ∈ (𝔭.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
        (Localization.AtPrime y.asIdeal))).under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ha
      rwa [h] at this
    · intro ha; exact Ideal.mem_map_of_mem _ ha
  have hϖQ : ϖz ∈ Q := by
    rw [Ideal.mem_comap, ← hφAϖ]
    show eR (φA ϖ) ∈ _
    rw [heR, IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)]
    exact Ideal.mem_map_of_mem _ hϖ𝔭
  have hQmax : ¬ Q.IsMaximal := by
    intro hmax
    apply h𝔭ne
    have h2 : (𝔭.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal))).IsMaximal := by
      rw [← hback, Ideal.map_comap_of_equiv]
      exact Ideal.comap_isMaximal_of_surjective _ eR.symm.surjective
    have h3 : 𝔭.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)) =
        y.asIdeal.map (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)) := by
      rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.eq_maximalIdeal h2
    have h4 := IsLocalization.under_map_of_isPrime_disjoint y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal) h𝔭 hdisj
    rw [h3] at h4
    rw [← h4]
    exact (IsLocalization.under_map_of_isPrime_disjoint y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
      (inferInstance : y.asIdeal.IsPrime) (Set.disjoint_left.mpr fun c hc hcy => hc hcy))

  obtain ⟨P, hPprime, hPX, hPπ, hPψ⟩ := hSURJ Q hQprime hϖQ hQmax
  refine ⟨P, hPprime, hPX, hPπ, ?_⟩
  show P.comap (ψ.comp germY) = 𝔭
  rw [← Ideal.comap_comap, hPψ, hQgermY]

end S_ModularCurve_FullLevel_AuxLevel_exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isPrime_comap_drinfeldChart_eq_of_isPrime_le_ne_twoChartIntegralModel (solution)
