-- Prove2me | solution 1 for ModularCurve.serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1b552b70-a21f-510b-9d2c-996e9ff699a8

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_HomOver_serrePairingInt_map
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isDeformationClassMap
import Theorems.Thm_TwoChartCech_Cover_serrePairingInt_eq_serrePairing
import Theorems.Thm_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange_residuesVanishOnCoboundaries
import Theorems.Thm_ModularCurve_exists_functionField_degeneracyRoof_kaehlerToFunctionField_eq_correspondence_of_res_eq_heckeDiffBar
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicGeometry.RelPicard.RigKerDualNumber.baseTransport_mk AlgebraicGeometry.RelPicard.BaseTransport.idOver_coe AlgebraicGeometry.RelPicard.RigKerDualNumber.baseTransport_symm_mk AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing CuspForm AlgebraicGeometry.Scheme.TwoAffineOpenCover KaehlerDifferential"

namespace HADJGlue

theorem cechH1ToH1_swap_mk {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S₀ S₁ : Set (AlgebraicCurve.Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hS' : S₁ ∪ S₀ = Set.univ)
    (D : AlgebraicCurve.Divisor K F) (f : F)
    (h : f ∈ AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) D) (h' : f ∈ AlgebraicCurve.lSpaceOn (S₁ ∩ S₀) D) :
    AlgebraicCurve.cechH1ToH1 hS' D (Submodule.Quotient.mk ⟨f, h'⟩) =
      - AlgebraicCurve.cechH1ToH1 hS D (Submodule.Quotient.mk ⟨f, h⟩) := by
  rw [AlgebraicCurve.cechH1ToH1_mk, AlgebraicCurve.cechH1ToH1_mk, ← Submodule.Quotient.mk_neg, Submodule.Quotient.eq]
  have hcov' : (S₀ ∩ S₁)ᶜ ∪ (S₀ ∩ S₁) = Set.univ := Set.compl_union_self _
  have key : AlgebraicCurve.extendOffChart K S₁ f - -AlgebraicCurve.extendOffChart K S₀ f =
      algebraMap F (↥(AlgebraicCurve.repartitions K F)) f - AlgebraicCurve.extendOffChart K (S₀ ∩ S₁)ᶜ f := by
    apply Subtype.ext
    funext v
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, NegMemClass.coe_neg, Pi.sub_apply, Pi.sub_apply,
      Pi.neg_apply, Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AlgebraicCurve.coe_extendOffChart_apply, AlgebraicCurve.coe_extendOffChart_apply,
      AlgebraicCurve.coe_extendOffChart_apply]
    have hv := Set.eq_univ_iff_forall.mp hS v
    by_cases h0 : v ∈ S₀ <;> by_cases h1 : v ∈ S₁ <;>
      simp [h0, h1, Set.mem_compl_iff, Set.mem_inter_iff] at hv ⊢
  rw [key]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right (AlgebraicCurve.algebraMap_mem_principalRepartitions f))
    (Submodule.mem_sup_left (AlgebraicCurve.extendOffChart_mem_repartitionsOf hcov' h))

end HADJGlue

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))

    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (M' : CurveModel ℚ ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (φα φβ : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (πα πβ : M'.C ⟶ X)
    (Hα : πα ≫ c = M'.toBase ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) (Hβ : πβ ≫ c = M'.toBase ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    (πα₀ πβ₀ : M'.C ⟶ M₀.C) (d : ℕ)
    (hdeg :
      πα = πα₀ ≫ e₀ ≫ pullback.fst c _ ∧ πβ = πβ₀ ≫ e₀ ≫ pullback.fst c _ ∧
      πα₀ ≫ M₀.toBase = M'.toBase ∧ πβ₀ ≫ M₀.toBase = M'.toBase ∧
      IsFinite πα₀ ∧ Flat πα₀ ∧ LocallyOfFinitePresentation πα₀ ∧
      IsFinite πβ₀ ∧ Flat πβ₀ ∧ LocallyOfFinitePresentation πβ₀ ∧
      (∀ x, πα₀.finrank x = d) ∧

      M'.C.fromSpecStalk (genericPoint M'.C) ≫ πα₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φα.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ πβ₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φβ.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      (∀ f : ↥(modularFunctionFieldFull p),
        heckeAlphaBar (AlgebraicClosure ℚ) p q (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
          baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φα f)) ∧
      (∀ f : ↥(modularFunctionFieldFull p),
        heckeBetaBar (AlgebraicClosure ℚ) p q (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
          baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φβ f)))

    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hφ₁ :
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) φ₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s (NeronModelInfra.schemeHomOverComp x φ₁)
            (NeronModelInfra.schemeHomOverComp y φ₁)))
    (hmoduli :
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of ℚ))
          (M : RigidifiedLineBundle c ε (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
          (hM : (algEquivZeroCut c ε).P (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) ε) (pullback.snd c (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))
            (Scheme.Modules.normModule (curveChange πα Hα (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)) d
              ((Scheme.Modules.pullback (curveChange πβ Hβ (t' ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))).obj M.L)))))

    (𝒱 : X.TwoAffineOpenCover) {ιT : Type} [Fintype ιT] (Λ : ιT → (𝒱.cover c).LaurentChart)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)

    (σ : ιT → (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (hΛ : ∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)))
    (hΛt : ∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0)

    {δ : RigKerDualNumber c ε ↥(GaloisRep.ratLocalizedAt ℓ) → H1StructureSheaf c ↥(GaloisRep.ratLocalizedAt ℓ) 𝒱}
    (hδ : IsDeformationClassMap c ε ↥(GaloisRep.ratLocalizedAt ℓ) 𝒱 δ)
    (j : H1StructureSheaf c ↥(GaloisRep.ratLocalizedAt ℓ) 𝒱 ≃ₗ[↥(GaloisRep.ratLocalizedAt ℓ)] (𝒱.structureSheafSections c).H1)
    (hj : ∀ y, j.symm y = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c ↥(GaloisRep.ratLocalizedAt ℓ) y)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar p))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar p⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) ι hιR ω.val.1) :
    ∀ (ω ω' : ↥((𝒱.kaehlerSections c).H0)), res ω' = heckeDiffBar p q (res ω) →
      ∀ (x x' : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (DualNumber ↥(GaloisRep.ratLocalizedAt ℓ))))) D.toBase //
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ↥(GaloisRep.ratLocalizedAt ℓ) ↥(GaloisRep.ratLocalizedAt ℓ) ↥(GaloisRep.ratLocalizedAt ℓ)).toRingHom) ≫ x.1 =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(GaloisRep.ratLocalizedAt ℓ))))).1}),
        x'.1.1 = x.1.1 ≫ φ₁.1 →
          (𝒱.cover c).serrePairingInt Λ hv ω (j (δ (h.kerPointsToRigKer ↥(GaloisRep.ratLocalizedAt ℓ) x'))) =
            (𝒱.cover c).serrePairingInt Λ hv ω' (j (δ (h.kerPointsToRigKer ↥(GaloisRep.ratLocalizedAt ℓ) x))) := by
  intro ω ω' hωω' x xr hxr
  letI := (AlgebraicCurve.baseToFunctionField (pullback.snd c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra

  let Rℓ := ↥(GaloisRep.ratLocalizedAt ℓ)
  let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
  let fq := HomOver.baseChange 𝒱 c ℚ
  let SPI := (𝒱.cover c).serrePairingInt Λ hv

  have hinj : Function.Injective (algebraMap Rℓ ℚ) := by
    exact fun a b hab => Subtype.ext hab
  apply hinj

  haveI : IsFractionRing Rℓ ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  haveI : Mono (specMap Rℓ ℚ) := by
    haveI : Epi (CommRingCat.ofHom (algebraMap Rℓ ℚ)) := IsLocalization.epi (nonZeroDivisors Rℓ) ℚ
    change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Rℓ ℚ)).op)
    infer_instance

  obtain ⟨Λq, hvq, hΛq⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange_residuesVanishOnCoboundaries 𝒱 c ℚ Λ hv
  obtain ⟨σq, hσq, -, hcomplq, hparq⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq 𝒱 c ℚ σ hσ Λ Λq hΛq
  let SPIq := ((𝒱.pullback c ℚ).cover (pullback.snd c (specMap Rℓ ℚ))).serrePairingInt Λq hvq

  have hspec : ∀ (η : ↥((𝒱.kaehlerSections c).H0)) (z : (𝒱.structureSheafSections c).H1),
      algebraMap Rℓ ℚ (SPI η z) = SPIq (fq.kaehlerH0map η) (fq.H1map z) := fun η z =>
    (HomOver.serrePairingInt_map fq Λ Λq hΛq hv hvq η z).symm
  rw [hspec, hspec]

  obtain ⟨δq, hδq⟩ := AlgebraicGeometry.RelPicard.exists_isDeformationClassMap c ε ℚ 𝒱
  let g : Rℓ →ₐ[Rℓ] ℚ := Algebra.ofId Rℓ ℚ
  obtain ⟨-, -, -, hunit4, hnat5⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.deformationClass_kerPoints_bijective_additive_natural h Rℓ hδ

  let σ' := RelPicard.LFP.stageHom Rℓ (DualNumber.lift
    ⟨((IsScalarTower.toAlgHom Rℓ ℚ (DualNumber ℚ)).comp g, DualNumber.eps),
      DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)

  have hxq := hunit4 ℚ g x.1 x.2
  have hxrq := hunit4 ℚ g xr.1 xr.2
  let xq : {x : SchemeHomOver (specMap Rℓ (DualNumber ℚ)) D.toBase //
      dualNumberReduction Rℓ ℚ ≫ x.1 = (L.one (specMap Rℓ ℚ)).1} :=
    ⟨GoodReductionJacobian.schemeHomOverComp σ'.1 σ'.2 x.1, hxq⟩
  let xrq : {x : SchemeHomOver (specMap Rℓ (DualNumber ℚ)) D.toBase //
      dualNumberReduction Rℓ ℚ ≫ x.1 = (L.one (specMap Rℓ ℚ)).1} :=
    ⟨GoodReductionJacobian.schemeHomOverComp σ'.1 σ'.2 xr.1, hxrq⟩
  have hxrq_comp : xrq.1.1 = xq.1.1 ≫ φ₁.1 := by
    change σ'.1 ≫ xr.1.1 = (σ'.1 ≫ x.1.1) ≫ φ₁.1
    rw [hxr, Category.assoc]

  have hδq_x : δq (h.kerPointsToRigKer ℚ xq) = 𝒱.H1stageMap c g (δ (h.kerPointsToRigKer Rℓ x)) :=
    hnat5 ℚ hδq g x hxq
  have hδq_xr : δq (h.kerPointsToRigKer ℚ xrq) = 𝒱.H1stageMap c g (δ (h.kerPointsToRigKer Rℓ xr)) :=
    hnat5 ℚ hδq g xr hxrq

  have hjq : ∀ w : H1StructureSheaf c Rℓ 𝒱, fq.H1map (j w) = 𝒱.H1stageMap c g w := by
    intro w
    have h1 : 𝒱.H1stageMap c g (𝒱.H1baseChangeMap c Rℓ (j w)) = 𝒱.H1baseChangeMap c ℚ (j w) :=
      H1stageMap_H1baseChangeMap 𝒱 c g (j w)
    rw [← hj, LinearEquiv.symm_apply_apply] at h1
    exact h1.symm
  rw [hjq, hjq, ← hδq_x, ← hδq_xr]

  obtain ⟨iI, iS, iSm, hC, iCOq, iDCq, iNTq, iCDq, hRT, iIM, iF, iFl, iL, iA, hd', φα', φβ', hφπα, hφπβ, jCO, jDC, jNT, jCD,
    jPD, hRT', hφα, hφβ, htrα, hsepβ, hfibα, hfibβ, jNE0, hroof⟩ :=
    ModularCurve.exists_functionField_degeneracyRoof_kaehlerToFunctionField_eq_correspondence_of_res_eq_heckeDiffBar p ℓ hℓp c ε D h hsm hpr hgc M₀ e₀ he₀ q M' φα φβ πα πβ Hα Hβ πα₀ πβ₀ d hdeg 𝒱 ι hιR hgen0 hιdef res hres
  obtain ⟨hregα, hΩ⟩ := hroof ω ω' hωω'

  obtain ⟨iNE, hW, hgerm, e1, he1, eΩ, iNE0, heΩ, hfib⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_serrePairingInt_eq_serrePairing_of_isCompletionAlong (𝒱.pullback c ℚ) (pullback.snd c (specMap Rℓ ℚ)) σq hσq Λq hvq
      (fun i => hcomplq i (hΛ i)) (fun i => hparq i (hΛt i)) hRT
  rw [hfib, hfib]

  have hW' : AlgebraicCurve.placesOf (pullback.snd c (specMap Rℓ ℚ)) (𝒱.pullback c ℚ).U0 ∪
      AlgebraicCurve.placesOf (pullback.snd c (specMap Rℓ ℚ)) (𝒱.pullback c ℚ).U1 = Set.univ := by
    rw [Set.union_comm]; exact hW
  have hgerm' : ∀ s : ((𝒱.pullback c ℚ).cover (pullback.snd c (specMap Rℓ ℚ))).A01,
      ((Limits.pullback c (specMap Rℓ ℚ)).germToFunctionField ((𝒱.pullback c ℚ).U0 ⊓ (𝒱.pullback c ℚ).U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf (pullback.snd c (specMap Rℓ ℚ)) (𝒱.pullback c ℚ).U0 ∩
            AlgebraicCurve.placesOf (pullback.snd c (specMap Rℓ ℚ)) (𝒱.pullback c ℚ).U1)
          (0 : AlgebraicCurve.Divisor ℚ (Limits.pullback c (specMap Rℓ ℚ)).functionField) := by
    intro s; rw [Set.inter_comm]; exact hgerm s

  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (δq (h.kerPointsToRigKer ℚ xq))
  obtain ⟨sr, hsrr, x', hδr, hx', htr⟩ :=
    AlgebraicGeometry.RelPicard.IsDeformationClassMap.exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono c ε ℚ hC D h M'.toBase πα πβ Hα Hβ d hd' φ₁ hmoduli 𝒱 hδq xq xrq hxrq_comp s hs.symm
      φα' φβ' hφπα hφπβ hφα hφβ htrα hW' (hgerm' s)

  have hL1 : e1 (δq (h.kerPointsToRigKer ℚ xrq)) =
      Submodule.Quotient.mk ⟨((Limits.pullback c (specMap Rℓ ℚ)).germToFunctionField _).hom sr, hgerm sr⟩ := by
    rw [hδr, he1]
  have hreg_eq : ((eΩ (fq.kaehlerH0map ω) : ↥(AlgebraicCurve.regularDifferentials ℚ _)) : Ω[_⁄ℚ]) =
      AlgebraicCurve.kaehlerToFunctionField (pullback.snd c (specMap Rℓ ℚ)) (𝒱.pullback c ℚ).U0
        (fq.kaehlerH0map ω).val.1 := heΩ _
  have hωα : AlgebraicCurve.Differential.pullbackAlong φα'
      ((eΩ (fq.kaehlerH0map ω) : ↥(AlgebraicCurve.regularDifferentials ℚ _)) : Ω[_⁄ℚ]) ∈
        AlgebraicCurve.regularDifferentials ℚ M'.C.functionField := by
    rw [hreg_eq]; exact hregα
  have hωβα : AlgebraicCurve.Differential.traceAlong φβ' (AlgebraicCurve.Differential.pullbackAlong φα'
      ((eΩ (fq.kaehlerH0map ω) : ↥(AlgebraicCurve.regularDifferentials ℚ _)) : Ω[_⁄ℚ])) ∈
        AlgebraicCurve.regularDifferentials ℚ (Limits.pullback c (specMap Rℓ ℚ)).functionField := by
    rw [hreg_eq, ← AlgebraicCurve.Differential.correspondence_apply, ← hΩ, ← heΩ]
    exact (eΩ (fq.kaehlerH0map ω')).2
  have hω'eq : eΩ (fq.kaehlerH0map ω') =
      ⟨AlgebraicCurve.Differential.traceAlong φβ' (AlgebraicCurve.Differential.pullbackAlong φα'
        ((eΩ (fq.kaehlerH0map ω) : ↥(AlgebraicCurve.regularDifferentials ℚ _)) : Ω[_⁄ℚ])), hωβα⟩ := by
    apply Subtype.ext
    show ((eΩ (fq.kaehlerH0map ω') : ↥(AlgebraicCurve.regularDifferentials ℚ _)) : Ω[_⁄ℚ]) =
      AlgebraicCurve.Differential.traceAlong φβ' (AlgebraicCurve.Differential.pullbackAlong φα'
        ((eΩ (fq.kaehlerH0map ω) : ↥(AlgebraicCurve.regularDifferentials ℚ _)) : Ω[_⁄ℚ]))
    rw [heΩ, hΩ, AlgebraicCurve.Differential.correspondence_apply, hreg_eq]
  have hR1 : e1 (δq (h.kerPointsToRigKer ℚ xq)) =
      Submodule.Quotient.mk ⟨((Limits.pullback c (specMap Rℓ ℚ)).germToFunctionField _).hom s, hgerm s⟩ := by
    rw [← hs, he1]

  have hsw_sr := HADJGlue.cechH1ToH1_swap_mk hW' hW 0 _ (hgerm' sr) (hgerm sr)
  have hsw_s := HADJGlue.cechH1ToH1_swap_mk hW' hW 0 _ (hgerm' s) (hgerm s)
  have hL2 : AlgebraicCurve.serrePairing hRT hW (eΩ (fq.kaehlerH0map ω))
        (Submodule.Quotient.mk ⟨((Limits.pullback c (specMap Rℓ ℚ)).germToFunctionField _).hom sr, hgerm sr⟩) =
      - AlgebraicCurve.serrePairing hRT hW' (eΩ (fq.kaehlerH0map ω))
        (AlgebraicCurve.cechH1.traceAlong φα' hφα htrα _ _ x') := by
    rw [← LinearMap.map_neg]
    exact AlgebraicCurve.serrePairing_eq_of_cechH1ToH1_eq hRT hW hW' _ _ _ (by rw [hsw_sr, htr, LinearMap.map_neg])
  have hR2 : AlgebraicCurve.serrePairing hRT hW (eΩ (fq.kaehlerH0map ω'))
        (Submodule.Quotient.mk ⟨((Limits.pullback c (specMap Rℓ ℚ)).germToFunctionField _).hom s, hgerm s⟩) =
      - AlgebraicCurve.serrePairing hRT hW' (eΩ (fq.kaehlerH0map ω'))
        (Submodule.Quotient.mk ⟨((Limits.pullback c (specMap Rℓ ℚ)).germToFunctionField _).hom s, hgerm' s⟩) := by
    rw [← LinearMap.map_neg]
    exact AlgebraicCurve.serrePairing_eq_of_cechH1ToH1_eq hRT hW hW' _ _ _ (by rw [hsw_s, LinearMap.map_neg])
  rw [hL1, hR1, hL2, hR2, neg_inj, hω'eq]
  exact AlgebraicCurve.serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
    hRT hRT' φα' φβ' hφα hφβ htrα hsepβ hfibα hfibβ hW' hW'
    (eΩ (fq.kaehlerH0map ω)) hωα hωβα _ x' hx'

#print axioms solution

end S_ModularCurve_serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar
end P2MW
export P2MW.S_ModularCurve_serrePairingInt_deformationClass_heckeGen_eq_of_isCompletionAlong_of_res_eq_heckeDiffBar (solution)
