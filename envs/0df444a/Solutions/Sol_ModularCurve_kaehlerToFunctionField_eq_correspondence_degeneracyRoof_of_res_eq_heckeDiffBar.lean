-- Prove2me | solution 1 for ModularCurve.kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/aa0b2cb0-b687-598d-916a-0098923888d1

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
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Theorems.Thm_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
import Theorems.Thm_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_isIntegral
import Theorems.Thm_AlgebraicCurve_kaehlerDifferential_map_injective_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
import Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_comp
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve~mem_restrictAlong_iff AlgebraicCurve IsLocalRing CuspForm AlgebraicGeometry.Scheme.TwoAffineOpenCover KaehlerDifferential"

namespace T3Kit

section IsoPackage

variable {K : Type u} [Field K] {X X₁ : Scheme.{u}} [IsIntegral X] [IsIntegral X₁] (p : X₁ ⟶ X) [IsIso p]

theorem app_genericPoint : p (genericPoint X₁) = genericPoint X := genericPoint_eq_of_isOpenImmersion p

theorem insep : Inseparable (genericPoint X) (p (genericPoint X₁)) := Inseparable.of_eq (app_genericPoint p).symm

noncomputable def θiso : X.functionField ≅ X₁.functionField :=
  X.presheaf.stalkCongr (insep p) ≪≫ asIso (p.stalkMap (genericPoint X₁))

theorem θiso_hom_apply (z : X.functionField) :
    (θiso p).hom z = p.stalkMap (genericPoint X₁) (X.presheaf.stalkSpecializes (insep p).ge z) := rfl

theorem θiso_germ (U : X.Opens) (hU : genericPoint X ∈ U) (hU₁ : genericPoint X₁ ∈ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (θiso p).hom (X.presheaf.germ U (genericPoint X) hU a) =
      X₁.presheaf.germ (p ⁻¹ᵁ U) (genericPoint X₁) hU₁ (p.app U a) := by
  rw [θiso_hom_apply, TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem θiso_algebraMap (x₁ : X₁) (z : X.presheaf.stalk (p x₁)) :
    algebraMap (X₁.presheaf.stalk x₁) X₁.functionField (p.stalkMap x₁ z) =
      (θiso p).hom (algebraMap (X.presheaf.stalk (p x₁)) X.functionField z) := by
  rw [θiso_hom_apply, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
    TopCat.Presheaf.stalkSpecializes_comp_apply]
  exact (Scheme.Hom.stalkSpecializes_stalkMap_apply p (genericPoint X₁) x₁
    ((genericPoint_spec X₁).specializes (Set.mem_univ x₁)) z).symm

theorem range_algebraMap_eq (x₁ : X₁) :
    Set.range (algebraMap (X₁.presheaf.stalk x₁) X₁.functionField) =
      (θiso p).hom '' Set.range (algebraMap (X.presheaf.stalk (p x₁)) X.functionField) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (p.stalkMap x₁)).2 w
    exact ⟨_, ⟨z, rfl⟩, (θiso_algebraMap p x₁ z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨p.stalkMap x₁ z, θiso_algebraMap p x₁ z⟩

variable (cX : X ⟶ Spec (.of K))

noncomputable def θalg :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField (p ≫ cX)).toAlgebra
    X.functionField ≃ₐ[K] X₁.functionField :=
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField (p ≫ cX)).toAlgebra
  { (θiso p).commRingCatIsoToRingEquiv with
    commutes' := fun k => by
      change (θiso p).hom (baseToFunctionField cX k) = baseToFunctionField (p ≫ cX) k
      simp only [baseToFunctionField, RingHom.comp_apply]
      rw [θiso_germ p ⊤ trivial trivial]
      rfl }

theorem θalg_apply (z : X.functionField) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField (p ≫ cX)).toAlgebra
    θalg p cX z = (θiso p).hom z := rfl

theorem θalg_toRingHom :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField (p ≫ cX)).toAlgebra
    CommRingCat.ofHom (θalg p cX).toAlgHom.toRingHom = (θiso p).hom := rfl

end IsoPackage

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (Place.restrictAlong φ hφ w).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem exists_algEquiv_functionField_of_isIso
    {K : Type u} [Field K] {X X₁ : Scheme.{u}} [IsIntegral X] [IsIntegral X₁]
    (cX : X ⟶ Spec (.of K)) (c₁ : X₁ ⟶ Spec (.of K)) (p : X₁ ⟶ X) [IsIso p] (hp : p ≫ cX = c₁) :
    letI := (baseToFunctionField cX).toAlgebra
    letI := (baseToFunctionField c₁).toAlgebra
    ∃ (θ : X.functionField ≃ₐ[K] X₁.functionField) (hθ : θ.toAlgHom.toRingHom.IsIntegral),
      X₁.fromSpecStalk (genericPoint X₁) ≫ p =
          Spec.map (CommRingCat.ofHom θ.toAlgHom.toRingHom) ≫ X.fromSpecStalk (genericPoint X) ∧
      (∀ U : X.Opens, placesOf c₁ (p ⁻¹ᵁ U) = (Place.restrictAlong θ.toAlgHom hθ) ⁻¹' placesOf cX U) ∧
      (∀ (U : X.Opens) [Nonempty (U : X.Opens)] [Nonempty (p ⁻¹ᵁ U : X₁.Opens)] (a : Γ(X, U)),
          (X₁.germToFunctionField (p ⁻¹ᵁ U)).hom (p.app U a) = θ ((X.germToFunctionField U).hom a)) := by
  subst hp
  letI := (baseToFunctionField cX).toAlgebra
  letI := (baseToFunctionField (p ≫ cX)).toAlgebra
  have hθ : (θalg p cX).toAlgHom.toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ (θalg p cX).surjective
  refine ⟨θalg p cX, hθ, ?_, ?_, ?_⟩
  ·
    rw [θalg_toRingHom]
    change _ = Spec.map (X.presheaf.stalkSpecializes (insep p).ge ≫ p.stalkMap (genericPoint X₁)) ≫ _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  ·
    intro U
    have hO : ∀ v : Place K X₁.functionField,
        ((Place.restrictAlong (θalg p cX).toAlgHom hθ v).toValuationSubring : Set X.functionField) =
          (θiso p).hom ⁻¹' (v.toValuationSubring : Set X₁.functionField) := fun v => by
      ext f; exact mem_restrictAlong_iff _ hθ v f
    ext v
    simp only [Set.mem_preimage, mem_placesOf_iff]
    constructor
    · rintro ⟨x₁, hx₁U, hcl, hrg⟩
      refine ⟨p x₁, hx₁U, ?_, ?_⟩
      · have : ({p x₁} : Set X) = p.homeomorph '' {x₁} := by rw [Set.image_singleton]; rfl
        rw [this]; exact p.homeomorph.isClosedMap _ hcl
      · apply SetLike.coe_injective
        change Set.range _ = ((Place.restrictAlong (θalg p cX).toAlgHom hθ v).toValuationSubring : Set X.functionField)
        rw [hO, ← Set.preimage_image_eq (Set.range _) (θiso p).commRingCatIsoToRingEquiv.injective]
        change (θiso p).hom ⁻¹' ((θiso p).hom '' _) = _
        rw [← range_algebraMap_eq p x₁]
        exact congrArg _ (congrArg SetLike.coe hrg)
    · rintro ⟨x, hxU, hcl, hrg⟩
      obtain ⟨x₁, hx₁⟩ : ∃ x₁ : X₁, p x₁ = x := ⟨p.homeomorph.symm x, p.homeomorph.apply_symm_apply x⟩
      subst hx₁
      have hinj : Function.Injective p := p.homeomorph.injective
      refine ⟨x₁, hxU, ?_, ?_⟩
      · have : ({x₁} : Set X₁) = p ⁻¹' {p x₁} := by
          rw [← Set.image_singleton, hinj.preimage_image]
        rw [this]; exact hcl.preimage p.continuous
      · apply SetLike.coe_injective
        change Set.range _ = (v.toValuationSubring : Set X₁.functionField)
        rw [range_algebraMap_eq p x₁]
        rw [show Set.range (algebraMap (X.presheaf.stalk (p x₁)) X.functionField) =
            ((Place.restrictAlong (θalg p cX).toAlgHom hθ v).toValuationSubring : Set X.functionField) from
          congrArg SetLike.coe hrg, hO]
        exact Set.image_preimage_eq _ (θiso p).commRingCatIsoToRingEquiv.surjective
  ·
    intro U _ _ a
    rw [θalg_apply]
    exact (θiso_germ p U ((genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
      (let ⟨⟨x, hx⟩⟩ := ‹Nonempty (U : X.Opens)›; ⟨x, Set.mem_univ _, hx⟩)) _ a).symm

end T3Kit

namespace RiiiIso

theorem app_genericPoint_of_fromSpecStalk_comp_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (φ : X.functionField →+* Y.functionField)
    (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) :
    π (genericPoint Y) = genericPoint X := by
  have h1 := congrArg (fun q => q (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y)))) hφπ
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at h1
  rw [h1]
  have h2 : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (Y.presheaf.stalk (genericPoint Y))) =
      IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) := Subsingleton.elim _ _
  rw [h2, Scheme.fromSpecStalk_closedPoint]

theorem ringHom_ext_of_fromSpecStalk_comp_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (g₁ g₂ : X.functionField →+* Y.functionField)
    (h₁ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom g₁) ≫ X.fromSpecStalk (genericPoint X))
    (h₂ : Y.fromSpecStalk (genericPoint Y) ≫ π = Spec.map (CommRingCat.ofHom g₂) ≫ X.fromSpecStalk (genericPoint X)) :
    g₁ = g₂ := by

  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  haveI : Nonempty (U : X.Opens) := ⟨⟨_, hηU⟩⟩
  have hgen := app_genericPoint_of_fromSpecStalk_comp_eq π g₁ h₁
  haveI : Nonempty (π ⁻¹ᵁ U : Y.Opens) := ⟨⟨genericPoint Y, show π (genericPoint Y) ∈ U by rw [hgen]; exact hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, U))
  ext s
  change g₁ ((X.germToFunctionField U).hom s) = g₂ ((X.germToFunctionField U).hom s)
  rw [← AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π g₁ h₁ U s,
    ← AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq π g₂ h₂ U s]

theorem germ_app_appLE {X Y Z : Scheme.{u}} [IsIntegral Z] (p : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (hV : V = f ⁻¹ᵁ U) (h : V ≤ f ⁻¹ᵁ U) (hη : genericPoint Z ∈ p ⁻¹ᵁ V) (hη' : genericPoint Z ∈ (p ≫ f) ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    Z.presheaf.germ (p ⁻¹ᵁ V) (genericPoint Z) hη (p.app V (f.appLE U V h a)) =
      Z.presheaf.germ ((p ≫ f) ⁻¹ᵁ U) (genericPoint Z) hη' ((p ≫ f).app U a) := by
  subst hV
  rw [← Scheme.Hom.app_eq_appLE, Scheme.Hom.comp_app]
  rfl

section Theta

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {X : Scheme.{0}} (c : X ⟶ Spec (.of R)) [IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R ℚ))]
  {L₀ L' : Type} [Field L₀] [Field L'] [Algebra ℚ L₀] [Algebra ℚ L']
  (M₀ : CurveModel ℚ L₀)
  (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) [IsIso e₀]
  (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
  (M' : CurveModel ℚ L')
  (φα φβ : L₀ →+* L')
  (πα πβ : M'.C ⟶ X)
  (Hα : πα ≫ c = M'.toBase ≫ Scheme.TwoAffineOpenCover.specMap R ℚ)
  (Hβ : πβ ≫ c = M'.toBase ≫ Scheme.TwoAffineOpenCover.specMap R ℚ)
  (πα₀ πβ₀ : M'.C ⟶ M₀.C)
  (hdeg1 : πα = πα₀ ≫ e₀ ≫ pullback.fst c _) (hdeg2 : πβ = πβ₀ ≫ e₀ ≫ pullback.fst c _)
  (hdeg3 : πα₀ ≫ M₀.toBase = M'.toBase) (hdeg4 : πβ₀ ≫ M₀.toBase = M'.toBase)
  (hgenα : M'.C.fromSpecStalk (genericPoint M'.C) ≫ πα₀ =
    Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φα.comp M₀.ffEquiv.symm.toRingHom))) ≫
      M₀.C.fromSpecStalk (genericPoint M₀.C))
  (hgenβ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ πβ₀ =
    Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φβ.comp M₀.ffEquiv.symm.toRingHom))) ≫
      M₀.C.fromSpecStalk (genericPoint M₀.C))
  (𝒱 : X.TwoAffineOpenCover)
  (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)

include he₀ hdeg1 hdeg2 hdeg3 hdeg4 hgenα hgenβ in

theorem exists_theta :
    letI Xq := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R ℚ)
    letI cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R ℚ)
    letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField M₀.toBase).toAlgebra
    letI Vq := 𝒱.pullback c ℚ
    letI fq := Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c ℚ
    ∀ [Nonempty (Vq.U0 : Xq.Opens)]
      (φα' φβ' : Xq.functionField →ₐ[ℚ] M'.C.functionField)
      (hφπα : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πα M'.toBase Hα =
        Spec.map (CommRingCat.ofHom φα'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (hφπβ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πβ M'.toBase Hβ =
        Spec.map (CommRingCat.ofHom φβ'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq)),
    ∃ θX : Xq.functionField ≃ₐ[ℚ] L₀,
      (∀ a : (𝒱.cover c).A0,
        θX ((Xq.germToFunctionField Vq.U0).hom (fq.map0 a)) =
          M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom
            (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) ∧
      (∀ x : Xq.functionField, M'.ffAlgEquiv.symm (φα' x) = φα.toRatAlgHom (θX x)) ∧
      (∀ x : Xq.functionField, M'.ffAlgEquiv.symm (φβ' x) = φβ.toRatAlgHom (θX x)) := by
  intro _ φα' φβ' hφπα hφπβ
  let Xq := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R ℚ)
  let cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R ℚ)
  letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField M₀.toBase).toAlgebra
  let Vq := 𝒱.pullback c ℚ
  let fq := Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c ℚ

  obtain ⟨ψ, hψ, hsq, -, hgerm⟩ := T3Kit.exists_algEquiv_functionField_of_isIso cq M₀.toBase e₀ he₀
  let θX : Xq.functionField ≃ₐ[ℚ] L₀ := ψ.trans M₀.ffAlgEquiv.symm
  have hθX : ∀ z, θX z = M₀.ffEquiv.symm (ψ z) := fun z => rfl

  have hliftα : pullback.lift πα M'.toBase Hα = πα₀ ≫ e₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hdeg1, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, he₀, hdeg3]
  have hliftβ : pullback.lift πβ M'.toBase Hβ = πβ₀ ≫ e₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hdeg2, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, he₀, hdeg4]

  have hleg : ∀ (φ' : Xq.functionField →ₐ[ℚ] M'.C.functionField) (φ : L₀ →+* L') (π₀ : M'.C ⟶ M₀.C)
      (hgen : M'.C.fromSpecStalk (genericPoint M'.C) ≫ π₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φ.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C))
      (hφπ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ (π₀ ≫ e₀) =
        Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq)),
      ∀ x, M'.ffAlgEquiv.symm (φ' x) = φ.toRatAlgHom (θX x) := by
    intro φ' φ π₀ hgen hφπ
    have hsq' : M'.C.fromSpecStalk (genericPoint M'.C) ≫ (π₀ ≫ e₀) =
        Spec.map (CommRingCat.ofHom ((M'.ffEquiv.toRingHom.comp (φ.comp M₀.ffEquiv.symm.toRingHom)).comp
          ψ.toAlgHom.toRingHom)) ≫ Xq.fromSpecStalk (genericPoint Xq) := by
      rw [← Category.assoc, hgen, Category.assoc, hsq, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have heq := ringHom_ext_of_fromSpecStalk_comp_eq (π₀ ≫ e₀) _ _ hφπ hsq'
    intro x
    have hx := RingHom.congr_fun heq x
    change φ' x = M'.ffEquiv (φ (M₀.ffEquiv.symm (ψ x))) at hx
    change M'.ffEquiv.symm (φ' x) = φ (M₀.ffEquiv.symm (ψ x))
    rw [hx, RingEquiv.symm_apply_apply]
  refine ⟨θX, ?_, ?_, ?_⟩
  ·
    intro a
    have hηV : genericPoint M₀.C ∈ e₀ ⁻¹ᵁ Vq.U0 := hgen0
    rw [hθX]
    congr 1
    haveI : Nonempty (e₀ ⁻¹ᵁ Vq.U0 : M₀.C.Opens) := ⟨⟨_, hηV⟩⟩
    rw [← hgerm Vq.U0 (fq.map0 a), Scheme.TwoAffineOpenCover.HomOver.map0_apply]
    change M₀.C.presheaf.germ (e₀ ⁻¹ᵁ Vq.U0) (genericPoint M₀.C) _
        (e₀.app Vq.U0 ((pullback.fst c _).appLE 𝒱.U0 Vq.U0 fq.U0_le a)) = _
    exact germ_app_appLE e₀ (pullback.fst c _) 𝒱.U0 Vq.U0 (Scheme.TwoAffineOpenCover.pullback_U0 𝒱 c ℚ)
      fq.U0_le _ hgen0 a
  · exact hleg φα' φα πα₀ hgenα (by rw [← hliftα]; exact hφπα)
  · exact hleg φβ' φβ πβ₀ hgenβ (by rw [← hliftβ]; exact hφπβ)

end Theta

end RiiiIso

theorem RiiiAux.pullbackAlong_id {K F : Type*} [Field K] [Field F] [Algebra K F] (ω : Ω[F⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (AlgHom.id K F) ω = ω := by
  have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; rw [AlgebraicCurve.Differential.pullbackAlong_D]; rfl
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [AlgebraicCurve.Differential.pullbackAlong_smul, hx]; rfl

theorem RiiiAux.pullbackAlong_injective_of_algEquiv {K F F₀ : Type*} [Field K] [Field F] [Field F₀] [Algebra K F]
    [Algebra K F₀] (θ : F ≃ₐ[K] F₀) :
    Function.Injective (AlgebraicCurve.Differential.pullbackAlong (θ : F →ₐ[K] F₀)) := by
  intro ω₁ ω₂ h
  have h' := congrArg (AlgebraicCurve.Differential.pullbackAlong (θ.symm : F₀ →ₐ[K] F)) h
  rwa [← AlgebraicCurve.Differential.pullbackAlong_comp, ← AlgebraicCurve.Differential.pullbackAlong_comp,
    AlgEquiv.symm_comp, RiiiAux.pullbackAlong_id, RiiiAux.pullbackAlong_id] at h'

set_option maxHeartbeats 24000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

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

    (𝒱 : X.TwoAffineOpenCover)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar p))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar p⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) ι hιR ω.val.1) :
    letI Rℓ := ↥(GaloisRep.ratLocalizedAt ℓ)
    letI Xq := Limits.pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    letI cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
    letI Vq := 𝒱.pullback c ℚ
    letI fq := HomOver.baseChange 𝒱 c ℚ
    ∀ [IsIntegral Xq] [SmoothOfRelativeDimension 1 cq]
      [AlgebraicCurve.IsCurveOver ℚ Xq.functionField] [∀ v : AlgebraicCurve.Place ℚ Xq.functionField, v.DCoordGenerates]
      [AlgebraicCurve.IsCurveOver ℚ M'.C.functionField] [∀ w : AlgebraicCurve.Place ℚ M'.C.functionField, w.DCoordGenerates]
      [Nonempty (Vq.U0 : Xq.Opens)]
      (φα' φβ' : Xq.functionField →ₐ[ℚ] M'.C.functionField)
      (hφπα : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πα M'.toBase Hα =
        Spec.map (CommRingCat.ofHom φα'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (hφπβ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πβ M'.toBase Hβ =
        Spec.map (CommRingCat.ofHom φβ'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (hfinα : AlgebraicCurve.FiniteAlong ℚ φα') (hfinβ : AlgebraicCurve.FiniteAlong ℚ φβ')
      (hsepβ : AlgebraicCurve.SeparableAlong ℚ φβ'),
    ∀ (ω ω' : ↥((𝒱.kaehlerSections c).H0)), res ω' = heckeDiffBar p q (res ω) →
      AlgebraicCurve.Differential.pullbackAlong φα'
          (AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω).val.1) ∈
        AlgebraicCurve.regularDifferentials ℚ M'.C.functionField ∧
      AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω').val.1 =
        AlgebraicCurve.Differential.correspondence φβ' φα'
          (AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω).val.1) := by
  intro iI iSm iCO iDC jCO jDC iNE φα' φβ' hφπα hφπβ hfinα hfinβ hsepβ ω ω' hωω'

  let Rℓ := ↥(GaloisRep.ratLocalizedAt ℓ)
  let Xq := Limits.pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
  let cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
  letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField M₀.toBase).toAlgebra
  let Vq := 𝒱.pullback c ℚ
  let fq := HomOver.baseChange 𝒱 c ℚ
  obtain ⟨hdeg1, hdeg2, hdeg3, hdeg4, hfinα₀, hflatα₀, hlfpα₀, hfinβ₀, hflatβ₀, hlfpβ₀, hrank, hgenα, hgenβ, hextα, hextβ⟩ := hdeg

  let germ : ↥((𝒱.kaehlerSections c).H0) → Ω[Xq.functionField⁄ℚ] := fun ω =>
    AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerH0map ω).val.1

  let κ : Ω[↥(modularFunctionFieldFull p)⁄ℚ] → Ω[↥(modularFunctionFieldBar p)⁄AlgebraicClosure ℚ] := fun η =>
    ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
      (AlgebraicCurve.Differential.pullbackAlong
        (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p)))) η)

  let θ' : M'.C.functionField ≃ₐ[ℚ] ↥(modularFunctionFieldFull (p * (q : ℕ))) := M'.ffAlgEquiv.symm

  let j : ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(modularFunctionFieldBar p) :=
    ((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p)))
  have hj : ∀ f : ↥(modularFunctionFieldFull p), j f = ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ := fun f =>
    ModularCurve.baseChangeEquiv_one_tmul (AlgebraicClosure ℚ) (modularFunctionFieldFull p) f
  have hκ_smul_D : ∀ u v : ↥(modularFunctionFieldFull p),
      KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)
        (AlgebraicCurve.Differential.pullbackAlong j (u • KaehlerDifferential.D ℚ ↥(modularFunctionFieldFull p) v)) =
      j u • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) (j v) := by
    intro u v
    rw [AlgebraicCurve.Differential.pullbackAlong_smul, AlgebraicCurve.Differential.pullbackAlong_D,
      LinearMap.map_smul, KaehlerDifferential.map_D]
    rfl

  obtain ⟨θX, hK, hLEGα, hLEGβ⟩ := RiiiIso.exists_theta c M₀ e₀ he₀ M' φα φβ πα πβ Hα Hβ πα₀ πβ₀ hdeg1 hdeg2 hdeg3 hdeg4
    hgenα hgenβ 𝒱 hgen0 φα' φβ' hφπα hφπβ

  have hRES : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      κ (AlgebraicCurve.Differential.pullbackAlong (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p)) (germ ω)) = res ω := by

    have hkey : ∀ a : (𝒱.cover c).A0,
        j ((θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p)) ((Xq.germToFunctionField Vq.U0).hom (fq.map0 a))) = ι a := by
      intro a
      apply Subtype.ext
      rw [hj, AlgEquiv.coe_algHom, hK, hιdef a]

    have hgenEq : ∀ η : Ω[(𝒱.cover c).A0⁄Rℓ],
        KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)
          (AlgebraicCurve.Differential.pullbackAlong j (AlgebraicCurve.Differential.pullbackAlong
            (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p))
            (AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (fq.kaehlerMap0 η)))) =
          KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) ι hιR η := by

      have hG : ∀ b b' : ((𝒱.pullback c ℚ).cover cq).A0,
          AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (b • KaehlerDifferential.D ℚ (((𝒱.pullback c ℚ).cover cq).A0) b') =
            (Xq.germToFunctionField Vq.U0).hom b • KaehlerDifferential.D ℚ Xq.functionField ((Xq.germToFunctionField Vq.U0).hom b') :=
        fun b b' => AlgebraicCurve.kaehlerToFunctionField_smul_D cq Vq.U0 b b'
      have hGs : ∀ (b : ((𝒱.pullback c ℚ).cover cq).A0) (η' : Ω[((𝒱.pullback c ℚ).cover cq).A0⁄ℚ]),
          AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (b • η') =
            (Xq.germToFunctionField Vq.U0).hom b • AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 η' :=
        fun b η' => AlgebraicCurve.kaehlerToFunctionField_smul cq Vq.U0 b η'
      have hG0 : AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (0 : Ω[((𝒱.pullback c ℚ).cover cq).A0⁄ℚ]) = 0 := map_zero _
      have hGa : ∀ η₁ η₂ : Ω[((𝒱.pullback c ℚ).cover cq).A0⁄ℚ],
          AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 (η₁ + η₂) =
            AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 η₁ + AlgebraicCurve.kaehlerToFunctionField cq Vq.U0 η₂ :=
        fun η₁ η₂ => map_add _ η₁ η₂
      intro η
      have hmem : η ∈ Submodule.span ((𝒱.cover c).A0) (Set.range (KaehlerDifferential.D Rℓ ((𝒱.cover c).A0))) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hmem using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        rw [← one_smul ((𝒱.cover c).A0) (KaehlerDifferential.D Rℓ ((𝒱.cover c).A0) s), HomOver.kaehlerMap0_smul_D, hG,
          AlgebraicCurve.Differential.pullbackAlong_smul, AlgebraicCurve.Differential.pullbackAlong_D, hκ_smul_D,
          KaehlerDifferential.mapOfRingHom_smul_D, hkey, hkey]
      | zero => rw [map_zero, hG0, map_zero, map_zero, map_zero, map_zero]
      | add x y _ _ hx hy => rw [map_add, hGa, map_add, map_add, map_add, hx, hy, map_add]
      | smul a x _ hx =>
        rw [show fq.kaehlerMap0 (a • x) = fq.map0 a • fq.kaehlerMap0 x from
            KaehlerDifferential.mapOfRingHom_smul _ _ fq.ringHom0_comp_algebraMap a x,
          hGs, AlgebraicCurve.Differential.pullbackAlong_smul, AlgebraicCurve.Differential.pullbackAlong_smul,
          LinearMap.map_smul, hx, KaehlerDifferential.mapOfRingHom_smul, hkey]
    intro ω
    have h1 : (fq.kaehlerH0map ω).val.1 = fq.kaehlerMap0 ω.val.1 := congrArg Prod.fst (HomOver.kaehlerH0map_apply_coe fq ω)
    rw [hres ω, ← hgenEq ω.val.1, ← h1]
    rfl

  have hκinj : Function.Injective κ := by

    let j : ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(modularFunctionFieldBar p) :=
      ((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p)))
    have hj : ∀ f : ↥(modularFunctionFieldFull p), j f = ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ := fun f =>
      ModularCurve.baseChangeEquiv_one_tmul (AlgebraicClosure ℚ) (modularFunctionFieldFull p) f
    letI algj : Algebra ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldBar p) := j.toRingHom.toAlgebra
    haveI : IsScalarTower ℚ ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldBar p) :=
      IsScalarTower.of_algebraMap_eq fun r => (j.commutes r).symm

    have hκ : ∀ η, κ η = KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldBar p) η := by
      intro η
      have hmem : η ∈ Submodule.span ↥(modularFunctionFieldFull p) (Set.range (KaehlerDifferential.D ℚ ↥(modularFunctionFieldFull p))) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hmem using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        show ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
          (AlgebraicCurve.Differential.pullbackAlong j (KaehlerDifferential.D ℚ ↥(modularFunctionFieldFull p) g)) = _
        rw [AlgebraicCurve.Differential.pullbackAlong_D, LinearMap.restrictScalars_apply, KaehlerDifferential.map_D,
          KaehlerDifferential.map_D]
        rfl
      | zero =>
        show ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
          (AlgebraicCurve.Differential.pullbackAlong j 0) = _
        rw [map_zero, map_zero, map_zero]
      | add x y _ _ hx hy =>
        have hadd : κ (x + y) = κ x + κ y := by
          show ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
            (AlgebraicCurve.Differential.pullbackAlong j (x + y)) = _
          rw [map_add, map_add]
        rw [hadd, hx, hy, map_add]
      | smul a x _ hx =>
        show ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
          (AlgebraicCurve.Differential.pullbackAlong j (a • x)) = _
        rw [AlgebraicCurve.Differential.pullbackAlong_smul, LinearMap.restrictScalars_apply, LinearMap.map_smul,
          LinearMap.map_smul_of_tower]
        show j a • κ x = _
        rw [hx]
        rfl

    have hgen : IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range (algebraMap ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldBar p))) = ⊤ := by
      apply IntermediateField.lift_injective
      erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
      show IntermediateField.adjoin (AlgebraicClosure ℚ) (Subtype.val '' Set.range j) = _
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, hj]
      constructor
      · rintro ⟨f, rfl⟩; exact ⟨f, f.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    haveI : AlgebraicCurve.IsCurveOver ℚ ↥(modularFunctionFieldFull p) := by
      rw [← ModularCurve.modularFunctionFieldFullC_rat]; convert ModularCurve.isCurveOver_modularFunctionFieldFullC ℚ p
      exact Subsingleton.elim _ _
    haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) := ModularCurve.isCurveOver_modularFunctionFieldBar p
    rw [show κ = ⇑(KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(modularFunctionFieldFull p) ↥(modularFunctionFieldBar p)) from funext hκ]
    exact AlgebraicCurve.kaehlerDifferential_map_injective_of_constantFieldExtension hgen
  have hnat : ∀ η : Ω[Xq.functionField⁄ℚ],
      AlgebraicCurve.Differential.pullbackAlong (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p))
          (AlgebraicCurve.Differential.correspondence φβ' φα' η) =
        AlgebraicCurve.Differential.correspondence φβ.toRatAlgHom φα.toRatAlgHom
          (AlgebraicCurve.Differential.pullbackAlong (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p)) η) := by
    intro η
    rw [AlgebraicCurve.Differential.correspondence_apply, AlgebraicCurve.Differential.correspondence_apply,
      AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv φβ' φβ.toRatAlgHom θX θ'
        (fun x => hLEGβ x) hsepβ,
      ← AlgebraicCurve.Differential.pullbackAlong_comp, ← AlgebraicCurve.Differential.pullbackAlong_comp]

    have hcompα : (θ' : M'.C.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull (p * (q : ℕ)))).comp φα' =
        φα.toRatAlgHom.comp (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p)) := AlgHom.ext fun x => hLEGα x
    rw [hcompα]

  have hfinβ₀ : AlgebraicCurve.FiniteAlong ℚ φβ.toRatAlgHom := by
    letI := AlgebraicCurve.algebraAlong φβ'
    letI := AlgebraicCurve.algebraAlong φβ.toRatAlgHom
    haveI : Module.Finite Xq.functionField M'.C.functionField := hfinβ
    exact Module.Finite.of_equiv_equiv θX.toRingEquiv θ'.toRingEquiv (RingHom.ext fun x => (hLEGβ x).symm)

  have hB : germ ω' = AlgebraicCurve.Differential.correspondence φβ' φα' (germ ω) := by

    have hθinj : Function.Injective
        (AlgebraicCurve.Differential.pullbackAlong (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p))) :=
      RiiiAux.pullbackAlong_injective_of_algEquiv θX
    apply hθinj; apply hκinj
    rw [hRES ω', hωω', ← hRES ω, hnat]

    exact (ModularCurve.map_differentialCorrespondence_eq_heckeDiffBar_map p q φα φβ hextα hextβ
      hfinβ₀
      (AlgebraicCurve.Differential.pullbackAlong (θX : Xq.functionField →ₐ[ℚ] ↥(modularFunctionFieldFull p)) (germ ω))).symm

  have hA : AlgebraicCurve.Differential.pullbackAlong φα' (germ ω) ∈
      AlgebraicCurve.regularDifferentials ℚ M'.C.functionField := by
    haveI : Nonempty (Vq.U1 : Xq.Opens) := by

      by_contra hne
      have hU1 : (Vq.U1 : Xq.Opens) = ⊥ := by
        ext x
        simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne ⟨⟨x, hx⟩⟩
      have htop : (Vq.U0 : Xq.Opens) = ⊤ := by
        have h := Vq.sup_eq_top
        rwa [hU1, sup_bot_eq] at h
      have hA : IsAffineOpen (⊤ : Xq.Opens) := htop ▸ Vq.isAffineOpen_U0
      have : IsAffine Xq := @IsAffine.of_isIso _ _ Xq.topIso.inv inferInstance hA
      exact AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one M₀.toBase (IsAffine.of_isIso e₀)
    haveI : IsProper cq := inferInstance
    have hreg := AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials Vq cq
      (fq.kaehlerH0map ω)
    have hint : φα'.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hfinα
    haveI : Algebra.EssFiniteType ℚ M'.C.functionField := AlgebraicCurve.essFiniteType_functionField M'.toBase
    exact AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_isIntegral φα' hint hreg
  exact ⟨hA, hB⟩

end S_ModularCurve_kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar
end P2MW
export P2MW.S_ModularCurve_kaehlerToFunctionField_eq_correspondence_degeneracyRoof_of_res_eq_heckeDiffBar (solution)
