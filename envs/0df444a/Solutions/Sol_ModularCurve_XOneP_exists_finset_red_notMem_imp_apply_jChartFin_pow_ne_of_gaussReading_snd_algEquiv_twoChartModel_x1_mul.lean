-- Prove2me | solution 1 for ModularCurve.XOneP.exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f6a750c4-50d4-53b2-8b54-6789668048a6

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false

p2m_attr_erase "instance" "IsScalarTower.of_algHom"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace VexAsm

theorem Spec_map_ofHom_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem ofHom_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end VexAsm

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)

    (w : ModularCurve.IntegralWeightOneForm k M)

    [NeZero p]
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσfin : ∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
        σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hσW : ∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
          (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom))

    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    [hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₂ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((σ (a : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₂.ffEquiv.symm
        (Mdl₂.C.germToFunctionField ((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
          (((e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
            (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
        : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
      HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (O : Subring (AlgebraicClosure ℚ)) (hO : O ≤ Pl.toSubring)
    (ρO : A →+* ↥O) (hρO : O.subtype.comp ρO = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective ⇑πk)

    (red₂ : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) →
      AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hred₂ : ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j))
        (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Spec.map (CommRingCat.ofHom O.subtype) ≫ ξ.1 =
        (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 →
      red₂ P = Mdl₂.pointEquivPlace ⟨c.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c.2⟩) :
    ∃ S₀ : Finset (AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
      ∀ (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥O) (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),

        Spec.map (CommRingCat.ofHom O.subtype) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j =
          (Mη.pointEquivPlace.symm P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →

        c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
          Spec.map (CommRingCat.ofHom ((πk.comp (Subring.inclusion hO)).comp ψ)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →

        red₂ P ∉ S₀ →
        ((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) ^ (p ^ 2) ≠ ((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) := by
  classical
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩

  obtain ⟨t, ht, htr, hfd, hsep⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C p M hM hpM k w
  haveI : AlgebraicCurve.HasPrincipalDivisors k ↥(ModularCurve.igusaFunctionFieldX1C k M w) :=
    AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable htr hfd hsep
  have hrat : ∀ v : AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w), v.IsRational := by
    intro v
    rw [← Mdl₂.pointEquivPlace.apply_symm_apply v]
    exact AlgebraicCurve.CurveModel.isRational_pointEquivPlace Mdl₂ _

  let g₂ := e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  let x : ↥(ModularCurve.igusaFunctionFieldX1C k M w) := Mdl₂.ffEquiv.symm
    (Mdl₂.C.germToFunctionField (g₂ ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
      ((g₂.app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv (ModularCurve.TwoChart.jChartFin A (↥K) j)))))
  have hx_nonconst : x ∉ Set.range (algebraMap k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := by

    obtain ⟨-, x₀, y₀, hy₀, hpres₀, hred₀⟩ :=
      ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
    have hker : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
      have hprime : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
      have hp : (p : A) ∈ RingHom.ker (algebraMap A k) := by
        rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
      have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hp
        have : (p : L) = 0 := by
          have := congrArg (algebraMap A L) hp
          simpa using this
        exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
      exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal hprime hne)
    let ι : IsLocalRing.ResidueField A →+* k :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A k) (fun a ha => by
        rw [← RingHom.mem_ker, hker]; exact ha)
    have hι : ∀ a : A, ι (IsLocalRing.residue A a) = algebraMap A k a := fun a => Ideal.Quotient.lift_mk _ _ _
    have hyk : y₀.map (algebraMap A k) ≠ 0 := by
      intro h
      apply hy₀
      ext n
      rw [PowerSeries.coeff_map, map_zero, ← RingHom.mem_ker, IsLocalRing.ker_residue, ← hker, RingHom.mem_ker]
      have := congrArg (PowerSeries.coeff n) h
      rwa [PowerSeries.coeff_map, map_zero] at this
    have hpres : ((σ ((ModularCurve.TwoChart.jChartFin A (↥K) j) : ↥K) : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y₀.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x₀.map (algebraMap A L)) := by
      rw [ModularCurve.TwoChart.coe_jChartFin, hσj]; exact hpres₀
    have hread := hgauss₂ (ModularCurve.TwoChart.jChartFin A (↥K) j) x₀ y₀ hyk hpres
    have hmapPS : ∀ P : PowerSeries A, HahnSeries.ofPowerSeries ℤ k (P.map (algebraMap A k)) =
        ModularCurve.coeffMap ι (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (P.map (IsLocalRing.residue A))) := by
      intro P
      ext n
      rw [ModularCurve.coeffMap_coeff]
      show ((P.map (algebraMap A k) : PowerSeries k) : LaurentSeries k).coeff n =
        ι (((P.map (IsLocalRing.residue A) : PowerSeries (IsLocalRing.ResidueField A)) :
          LaurentSeries (IsLocalRing.ResidueField A)).coeff n)
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
      split_ifs with hn
      · rw [map_zero]
      · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, hι]
    have hjt : ((x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) = ((t ^ p : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) := by
      rw [hread, hmapPS, hmapPS, ← map_div₀, hred₀, map_pow]
      show (ModularCurve.jqModC (IsLocalRing.ResidueField A)).map ι ^ p = _
      rw [ModularCurve.map_jqModC, ← ht]
      rfl
    have hxt : x = t ^ p := Subtype.ext hjt

    rintro ⟨c, hc⟩
    apply htr
    have halg : IsAlgebraic k (t ^ p) := by
      rw [← hxt, ← hc]; exact isAlgebraic_algebraMap c
    exact (halg.of_pow (Fact.out : p.Prime).pos)

  let T : Finset k := ((Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial k).roots).toFinset
  have hT : ∀ a : k, a ∈ T ↔ a ^ (p ^ 2) = a := by
    intro a
    have hne : (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial k) ≠ 0 := by
      exact FiniteField.X_pow_card_sub_X_ne_zero k (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
  refine ⟨(AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem hrat x hx_nonconst T).toFinset, ?_⟩
  intro P ψ c h1 hcχ hS
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hS
  obtain ⟨hxmem, hxT⟩ := hS
  rw [not_not] at hxmem

  have hψ : ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = ρO := by
    have e := congrArg (· ≫ ModularCurve.TwoChart.modelTo A (↥K) j) h1
    simp only [Category.assoc, ModularCurve.TwoChart.ιFin_modelTo] at e
    rw [pullback.condition, reassoc_of% heη, reassoc_of% (Mη.pointEquivPlace.symm P).2] at e
    rw [← VexAsm.Spec_map_ofHom_comp, ← VexAsm.Spec_map_ofHom_comp] at e
    have e' := VexAsm.ofHom_inj e

    apply RingHom.ext; intro a; apply Subtype.ext
    have := congrArg (fun f : A →+* AlgebraicClosure ℚ => f a) e'
    have h2 := congrArg (fun f : A →+* AlgebraicClosure ℚ => f a) hρO
    simp only [RingHom.coe_comp, Function.comp_apply] at this h2 ⊢
    exact this.trans h2.symm
  let ξ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρO)) (ModularCurve.TwoChart.modelTo A (↥K) j) :=
    ⟨Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j, by rw [Category.assoc, ModularCurve.TwoChart.ιFin_modelTo, ← VexAsm.Spec_map_ofHom_comp, hψ]⟩
  have hcξ : c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom (πk.comp (Subring.inclusion hO))) ≫ ξ.1 := by
    rw [hcχ]; show _ = Spec.map _ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j
    rw [← Category.assoc (Spec.map _), ← VexAsm.Spec_map_ofHom_comp]
  have hred := hred₂ P ξ c h1 hcξ

  have hz : (⟨c.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c.2⟩ :
      {q : Spec (CommRingCat.of k) ⟶ Mdl₂.C // q ≫ Mdl₂.toBase = 𝟙 _}).1 ≫ g₂ =
      Spec.map (CommRingCat.ofHom ((πk.comp (Subring.inclusion hO)).comp ψ)) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
    show (c.1 ≫ e₂.inv) ≫ e₂.hom ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = _
    rw [Category.assoc, e₂.inv_hom_id_assoc]; exact hcχ
  have hcen := AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_sub_algebraMap_mem_nonunits_pointEquivPlace_of_comp_eq_specMap_comp Mdl₂ g₂ (ModularCurve.TwoChart.ιFin A (↥K) j)
    ⟨c.1 ≫ e₂.inv, by rw [← he₂, Category.assoc, e₂.inv_hom_id_assoc]; exact c.2⟩ ((πk.comp (Subring.inclusion hO)).comp ψ) hz (ModularCurve.TwoChart.jChartFin A (↥K) j)
  rw [← hred] at hcen

  have hamem : algebraMap k ↥(ModularCurve.igusaFunctionFieldX1C k M w) (((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j)) ∈
      (red₂ P).toValuationSubring := (red₂ P).algebraMap_mem' _
  have hval : (red₂ P).evalAt x = ((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j) := by
    rw [(red₂ P).evalAt_of_mem hxmem]
    have hres : IsLocalRing.residue ↥(red₂ P).toValuationSubring (⟨x, hxmem⟩ : (red₂ P).toValuationSubring) =
        algebraMap k (red₂ P).ResidueField (((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j)) := by
      rw [IsScalarTower.algebraMap_apply k ↥(red₂ P).toValuationSubring (red₂ P).ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
        ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      obtain ⟨hm, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hcen
      have e : (⟨x, hxmem⟩ : ↥(red₂ P).toValuationSubring) - algebraMap k ↥(red₂ P).toValuationSubring
          (((πk.comp (Subring.inclusion hO)).comp ψ) (ModularCurve.TwoChart.jChartFin A (↥K) j)) = ⟨_, hm⟩ := Subtype.ext rfl
      rw [e]; exact hmax
    rw [hres, (red₂ P).residueInv_algebraMap]

  intro hpow
  apply hxT
  show (red₂ P).evalAt x ∈ (T : Set k)
  rw [Finset.mem_coe, hT, hval]
  exact hpow

end S_ModularCurve_XOneP_exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_finset_red_notMem_imp_apply_jChartFin_pow_ne_of_gaussReading_snd_algEquiv_twoChartModel_x1_mul (solution)
