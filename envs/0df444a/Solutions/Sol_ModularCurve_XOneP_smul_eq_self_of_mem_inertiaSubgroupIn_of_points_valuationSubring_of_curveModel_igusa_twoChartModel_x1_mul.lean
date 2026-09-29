-- Prove2me | solution 1 for ModularCurve.XOneP.smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0f91e61a-8028-504f-9ed6-7878dbba4080

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace FinFixed

end FinFixed

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

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

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ Pl.inertiaSubgroupIn ℚ →
      (∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (m : ℕ), 0 < m → ¬ p ∣ m →
        ∀ (x : ModularCurve.JOne (M * p)), m • x = 0 →
          ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
            (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 →
              σ • x = x := by
  intro σ hσI hσL m hm0 hpm x hx z hz
  classical

  let G : GoodReductionJacobian.RelativeGroupLaw A D.toBase :=
    RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some
  have hGc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative _

  obtain ⟨g, hgI, hgσ⟩ := Subgroup.mem_map.1 hσI
  let σPl : ↥Pl →+* ↥Pl := MulSemiringAction.toRingHom (↥(Pl.decompositionSubgroup ℚ)) (↥Pl) g
  have hσPl : ∀ a : ↥Pl, ((σPl a : ↥Pl) : AlgebraicClosure ℚ) = σ a := fun a => by
    rw [← hgσ]; rfl

  have hσA : ∀ a : A, σ (algebraMap A (AlgebraicClosure ℚ) a) = algebraMap A (AlgebraicClosure ℚ) a := fun a => by
    rw [IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ), hσL]
  have hρa : ∀ a : A, ((ρ a : ↥Pl) : AlgebraicClosure ℚ) = algebraMap A (AlgebraicClosure ℚ) a :=
    fun a => RingHom.congr_fun hρ a
  have hσρ : σPl.comp ρ = ρ := by
    refine RingHom.ext fun a => Subtype.ext ?_
    change ((σPl (ρ a) : ↥Pl) : AlgebraicClosure ℚ) = (ρ a : AlgebraicClosure ℚ)
    rw [hσPl, hρa, hσA]

  let z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase :=
    ⟨Spec.map (CommRingCat.ofHom σPl) ≫ z.1, by
      rw [Category.assoc, z.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσρ]⟩

  have hσspecA : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ specMap A (AlgebraicClosure ℚ) = specMap A (AlgebraicClosure ℚ) := by
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ))) = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun a => hσA a)
  have hσspecL : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ) = specMap L (AlgebraicClosure ℚ) := by
    change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ))) = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure ℚ)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext fun l => hσL l)
  letI grpη := G.pointGroup (specMap A (AlgebraicClosure ℚ))
  have hg0 : gpts 0 = (1 : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase) := by
    have h := hgadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have htrans : (gpts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (gpts x).1 := by

    have hφ : ∀ P : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ P.1 ≫ eη ≫
            pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ≫
          ModularCurve.TwoChart.modelTo A (↥K) j = 𝟙 _ ≫ specMap A (AlgebraicClosure ℚ) := by
      intro P
      rw [Category.id_comp]
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% heη, reassoc_of% P.2, hσspecA]
    let twist : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} →
        {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} := fun P =>
      ⟨pullback.lift (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ P.1 ≫ eη ≫
            pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) (𝟙 _) (hφ P) ≫ inv eη, by
        have hinv : inv eη ≫ Mη.toBase = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) := by
          rw [← heη, IsIso.inv_hom_id_assoc]
        rw [Category.assoc, hinv, pullback.lift_snd]⟩
    have htw : ∀ P : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        (twist P).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ P.1 ≫ eη ≫
            pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) := by
      intro P
      change (pullback.lift _ _ _ ≫ inv eη) ≫ eη ≫ _ = _
      rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

    have htwaj : ∀ P : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        (twist P).1 ≫ ajbar = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ P.1 ≫ ajbar := by
      intro P
      have hk : ((twist P).1 ≫ eη) ≫ kL = (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ P.1 ≫ eη) ≫ kL := by
        apply pullback.hom_ext
        · simp only [Category.assoc, hkL₁]
          exact htw P
        · simp only [Category.assoc, hkL₂, reassoc_of% heη, reassoc_of% (twist P).2, reassoc_of% P.2, hσspecL]
      rw [hajbar]
      calc (twist P).1 ≫ eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L)
          = (((twist P).1 ≫ eη) ≫ kL) ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L) := by
            simp only [Category.assoc]
        _ = ((Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ P.1 ≫ eη) ≫ kL) ≫ ajL.1 ≫
              pullback.fst D.toBase (specMap A L) := by rw [hk]
        _ = _ := by simp only [Category.assoc]

    have hpl : ∀ P : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        Mη.pointEquivPlace (twist P) =
          ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) σ • Mη.pointEquivPlace P :=
      fun P => hgal σ hσL P (twist P) (htw P)
    have hεtw : (twist εbar).1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        specMap A (AlgebraicClosure ℚ) ≫ ε.1 := by
      rw [htw, hεbar, ← Category.assoc, hσspecA]

    have hgen : ∀ P : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
          (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
            Finsupp.single (Mη.pointEquivPlace P) 1 - Finsupp.single (Mη.pointEquivPlace εbar) 1 ∧
          gpts (σ • Pic0.mk Dv) =
            GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) hσspecA
              (gpts (Pic0.mk Dv)) := by
      intro P
      obtain ⟨Dv, hDv, hgDv⟩ := hpts_aj P εbar hεbar
      obtain ⟨Dv', hDv', hgDv'⟩ := hpts_aj (twist P) (twist εbar) hεtw
      refine ⟨Dv, hDv, Subtype.ext ?_⟩
      have hσDv : σ • Pic0.mk Dv = Pic0.mk Dv' := by
        rw [ModularCurve.galois_smul_pic0_def, AlgebraicCurve.SemilinearAut.pic0_smul_mk]
        congr 1
        apply Subtype.ext
        rw [AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom, hDv, hDv', hpl P, hpl εbar, smul_sub,
          AlgebraicCurve.SemilinearAut.smul_single, AlgebraicCurve.SemilinearAut.smul_single]
      rw [hσDv, hgDv']
      change (twist P).1 ≫ ajbar = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (gpts (Pic0.mk Dv)).1
      rw [hgDv, htwaj]

    let Ψ : ModularCurve.JOne (M * p) → SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase := fun y =>
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) hσspecA (gpts y)
    have hΨmul : ∀ y y' : ModularCurve.JOne (M * p), Ψ (y + y') = Ψ y * Ψ y' := fun y y' => by
      change GoodReductionJacobian.schemeHomOverComp _ hσspecA (gpts (y + y')) = G.mul _ (Ψ y) (Ψ y')
      rw [hgadd]
      exact G.mul_natural _ _ _ hσspecA _ _
    have hΨ0 : Ψ 0 = 1 := by
      change GoodReductionJacobian.schemeHomOverComp _ hσspecA (gpts 0) = G.one _
      rw [hg0]
      exact GoodReductionJacobian.RelativeGroupLaw.one_natural G _ _ _ hσspecA
    have hΦmul : ∀ y y' : ModularCurve.JOne (M * p), gpts (σ • (y + y')) = gpts (σ • y) * gpts (σ • y') :=
      fun y y' => by rw [smul_add, hgadd]; rfl
    let S : AddSubgroup (ModularCurve.JOne (M * p)) :=
      { carrier := {y | gpts (σ • y) = Ψ y}
        add_mem' := fun {a b} ha hb => by
          change gpts (σ • (a + b)) = Ψ (a + b)
          rw [hΦmul, hΨmul, show gpts (σ • a) = Ψ a from ha, show gpts (σ • b) = Ψ b from hb]
        zero_mem' := by
          change gpts (σ • 0) = Ψ 0
          rw [show σ • (0 : ModularCurve.JOne (M * p)) = 0 from (DistribSMul.toAddMonoidHom (ModularCurve.JOne (M * p)) σ).map_zero, hg0, hΨ0]
        neg_mem' := fun {a} ha => by
          change gpts (σ • -a) = Ψ (-a)
          have h1 : gpts (σ • a) * gpts (σ • -a) = 1 := by
            rw [← hΦmul, add_neg_cancel, show σ • (0 : ModularCurve.JOne (M * p)) = 0 from
              (DistribSMul.toAddMonoidHom (ModularCurve.JOne (M * p)) σ).map_zero, hg0]
          have h2 : Ψ a * Ψ (-a) = 1 := by rw [← hΨmul, add_neg_cancel, hΨ0]
          rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2, show gpts (σ • a) = Ψ a from ha] }

    haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.Prime.ne_zero Fact.out)⟩
    have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
      rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.coe_T]
    have hdeg1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)), v.deg = 1 := fun v =>
      ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 (M * p)) hT
        (ModularCurve.x1FunctionField (M * p)) rfl v
    have hSall : x ∈ S := by
      obtain ⟨E, rfl⟩ := AlgebraicCurve.Pic0.mk_surjective x
      have hgenmem : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
              Finsupp.single v 1 - Finsupp.single (Mη.pointEquivPlace εbar) 1 ∧ Pic0.mk Dv ∈ S := by
        intro v
        obtain ⟨Dv, hDv, hS⟩ := hgen (Mη.pointEquivPlace.symm v)
        rw [Equiv.apply_symm_apply] at hDv
        exact ⟨Dv, hDv, hS⟩
      choose gen hgen1 hgen2 using hgenmem

      have hsum : ∑ v ∈ (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
          (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) v = 0 := by
        have hE0 : Divisor.degree (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) = 0 := E.2
        rw [← Finsupp.sum_single (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))), Finsupp.sum,
          map_sum] at hE0
        simpa only [Divisor.degree_single, hdeg1, Nat.cast_one, mul_one] using hE0
      have hE : E = ∑ v ∈ (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
          (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) v • gen v := by
        apply Subtype.ext
        rw [AddSubgroup.val_finsetSum]
        simp only [AddSubgroupClass.coe_zsmul, hgen1, smul_sub, Finset.sum_sub_distrib, Finsupp.smul_single,
          smul_eq_mul, mul_one]
        rw [← Finsupp.single_finsetSum, hsum, Finsupp.single_zero, sub_zero]
        exact (Finsupp.sum_single _).symm
      rw [hE]
      have hmk : Pic0.mk (∑ v ∈ (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
            (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) v • gen v) =
          ∑ v ∈ (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))).support,
            (E : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) v • Pic0.mk (gen v) := by
        change QuotientAddGroup.mk' _ (∑ v ∈ _, _) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [map_zsmul]
        rfl
      rw [hmk]
      exact S.sum_mem fun v _ => S.zsmul_mem (hgen2 v) _
    exact congrArg Subtype.val hSall
  have hσsub : Pl.subtype.comp σPl = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp Pl.subtype :=
    RingHom.ext fun a => hσPl a
  have hz' : (gpts (σ • x)).1 =
      Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 := by
    change (gpts (σ • x)).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ Spec.map (CommRingCat.ofHom σPl) ≫ z.1
    rw [htrans, hz, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hσsub]

  have hred : (IsLocalRing.residue ↥Pl).comp σPl = IsLocalRing.residue ↥Pl := by
    refine RingHom.ext fun a => ?_
    change IsLocalRing.residue ↥Pl (g • a) = IsLocalRing.residue ↥Pl a
    rw [IsLocalRing.ResidueField.residue_smul]
    have hk := (MonoidHom.mem_ker).1 hgI
    change (MulSemiringAction.toRingAut (↥(Pl.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥Pl) g)
      (IsLocalRing.residue ↥Pl a) = IsLocalRing.residue ↥Pl a
    rw [hk]
    rfl

  letI := G.pointGroup (Spec.map (CommRingCat.ofHom ρ))
  have htor : ∀ (w : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : ModularCurve.JOne (M * p)),
      m • y = 0 → (gpts y).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ w.1 → w ^ m = 1 := by
    intro w y hy hw
    have hι : Spec.map (CommRingCat.ofHom Pl.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) =
        specMap A (AlgebraicClosure ℚ) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
    letI := G.pointGroup (specMap A (AlgebraicClosure ℚ))
    have hcomp : GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι w = gpts y :=
      Subtype.ext hw.symm

    have hg0 : gpts 0 = (1 : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase) := by
      have h := hgadd 0 0
      rw [add_zero] at h
      exact (mul_eq_left.1 h.symm)
    have hgpow : ∀ k : ℕ, gpts (k • y) = gpts y ^ k := by
      intro k
      induction k with
      | zero => rw [zero_nsmul, pow_zero, hg0]
      | succ k ih => rw [succ_nsmul, hgadd, pow_succ, ← ih]; rfl
    have hgen : (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι w) ^ m = 1 := by
      rw [hcomp, ← hgpow, hy, hg0]

    have hcpow : ∀ k : ℕ, GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι (w ^ k) =
        (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι w) ^ k := by
      intro k
      induction k with
      | zero => exact GoodReductionJacobian.RelativeGroupLaw.one_natural G _ _ _ hι
      | succ k ih => rw [pow_succ, pow_succ, ← ih]; exact G.mul_natural _ _ _ hι _ _

    haveI : IsSeparated D.toBase := hsep
    haveI : IsDominant (Spec.map (CommRingCat.ofHom Pl.subtype)) :=
      ⟨((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
          rw [(RingHom.injective_iff_ker_eq_bot _).1 (fun a b h => Subtype.ext h)]
          exact bot_le) : DenseRange (PrimeSpectrum.comap Pl.subtype))⟩
    apply Subtype.ext
    refine ext_of_isDominant_of_isSeparated D.toBase ?_ (Spec.map (CommRingCat.ofHom Pl.subtype)) ?_
    · rw [(w ^ m).2, (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase).2]
    · calc Spec.map (CommRingCat.ofHom Pl.subtype) ≫ (w ^ m).1
          = (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι (w ^ m)).1 := rfl
        _ = ((GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι w) ^ m).1 := by
          rw [hcpow]
        _ = (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom Pl.subtype)) hι (G.one _)).1 := by
          rw [hgen, GoodReductionJacobian.RelativeGroupLaw.one_natural]; rfl
        _ = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase).1 := rfl
  have hzm : z ^ m = 1 := htor z x hx hz
  have hσmx : m • (σ • x) = 0 := by
    rw [show σ • x = DistribSMul.toAddMonoidHom (ModularCurve.JOne (M * p)) σ x from rfl, ← map_nsmul, hx,
      map_zero]
  have hz'm : z' ^ m = 1 := htor z' (σ • x) hσmx hz'

  have hzz : z' = z := by
    haveI : IsSeparated D.toBase := hsep
    haveI : Smooth D.toBase := hsm
    haveI : HenselianLocalRing ↥Pl := ValuationSubring.henselianLocalRing_of_isAlgClosed Pl
    haveI : IsAlgClosed (IsLocalRing.ResidueField ↥Pl) :=
      ValuationSubring.isAlgClosed_residueField_of_isAlgClosed Pl

    have hmu : IsUnit (m : A) := by
      by_contra hmu
      have hmm : (m : A) ∈ IsLocalRing.maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hmu)
      obtain ⟨a, c, hac⟩ : IsCoprime (m : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm))
      apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (a : A) * (m : A) + (c : A) * (p : A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hac
      rw [← h1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmm) (Ideal.mul_mem_left _ _ hAp)
    have hπu : ∀ y : ↥Pl, IsUnit y ↔ IsLocalRing.residue ↥Pl y ≠ 0 := fun y => by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    obtain ⟨hinj, -⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
        G hGc m hmu (↥Pl) ρ (IsLocalRing.ResidueField ↥Pl) (IsLocalRing.residue ↥Pl)
        IsLocalRing.residue_surjective hπu

    have hψ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ Spec.map (CommRingCat.ofHom ρ) =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcz : GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) hψ z' =
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) hψ z := by
      apply Subtype.ext
      change Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ Spec.map (CommRingCat.ofHom σPl) ≫ z.1 =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ z.1
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hred]
    have hu : z' * z⁻¹ = 1 := by
      refine hinj (z' * z⁻¹) ?_ ?_
      · rw [Commute.mul_pow (hGc _ z' z⁻¹ : Commute z' z⁻¹), hz'm, inv_pow, hzm, inv_one, mul_one]
      · letI := G.pointGroup (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ)))
        change (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) hψ
          (G.mul _ z' z⁻¹)).1 = (G.one _).1
        rw [G.mul_natural, hcz, ← G.mul_natural]
        change (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) hψ
          (z * z⁻¹)).1 = (G.one _).1
        rw [mul_inv_cancel]
        exact congrArg Subtype.val (GoodReductionJacobian.RelativeGroupLaw.one_natural G _ _ _ hψ)
    calc z' = z' * z⁻¹ * z := by rw [inv_mul_cancel_right]
      _ = z := by rw [hu, one_mul]

  apply gpts.injective
  apply Subtype.ext
  rw [hz', hzz, ← hz]

end S_ModularCurve_XOneP_smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_smul_eq_self_of_mem_inertiaSubgroupIn_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul (solution)
