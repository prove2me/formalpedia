-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7cbc5774-e40d-567f-9716-9f4af048d482

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_functionField_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_XHDRModelAtP_isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero SheafOfModules.isIso_ihomModelToIhom GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

universe u

noncomputable section

namespace PPR

section PoincarePow

open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}

theorem nonempty_poincare_pullbackAlong_pow_iso (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : SchemeHomOver t D.toBase) (n : ℕ) :
    letI := h.relativeGroupLaw.pointGroup t
    Nonempty ((h.poincare.pullbackAlong (σ ^ n)).L ≅ ((h.poincare.pullbackAlong σ).L).tensorPow n) := by
  letI := h.relativeGroupLaw.pointGroup t
  letI := h.grpObj
  induction n with
  | zero =>
    have h1 := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := P) h (Over.mk t)
    obtain ⟨e⟩ := h1
    refine ⟨?_⟩
    rw [pow_zero]
    exact e
  | succ n ih =>
    obtain ⟨eₙ⟩ := ih
    have hm := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := P) h (T := Over.mk t)
      (schemeHomOverToOverHom (σ ^ n)) (schemeHomOverToOverHom σ)
    obtain ⟨em⟩ := hm
    refine ⟨?_⟩
    rw [pow_succ]
    exact em ≪≫ (eₙ ⊗ᵢ Iso.refl _)

theorem iterate_mul_one_eq_pow (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : SchemeHomOver t D.toBase) (n : ℕ) :
    letI := h.relativeGroupLaw.pointGroup t
    (fun τ : SchemeHomOver t D.toBase => h.relativeGroupLaw.mul t τ σ)^[n] (h.relativeGroupLaw.one t) = σ ^ n := by
  letI := h.relativeGroupLaw.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    rfl

theorem nonempty_tensorPow_poincare_iso_unit_of_iterate (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : SchemeHomOver t D.toBase) (n : ℕ)
    (hσ : (fun τ : SchemeHomOver t D.toBase => h.relativeGroupLaw.mul t τ σ)^[n] (h.relativeGroupLaw.one t) =
      h.relativeGroupLaw.one t) :
    Nonempty (((h.poincare.pullbackAlong σ).L).tensorPow n ≅ 𝟙_ (pullback c t).Modules) := by
  letI := h.relativeGroupLaw.pointGroup t
  letI := h.grpObj
  have hpow : σ ^ n = 1 := by
    rw [← iterate_mul_one_eq_pow h t σ n]
    exact hσ
  obtain ⟨e⟩ := nonempty_poincare_pullbackAlong_pow_iso h t σ n
  have h1 := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := P) h (Over.mk t)
  obtain ⟨e1⟩ := h1
  refine ⟨e.symm ≪≫ ?_ ≪≫ e1⟩
  rw [hpow]
  exact Iso.refl _

end PoincarePow

section LocalPow

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}}

abbrev rM (M : X.Modules) {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

theorem isUnit_of_isFrameOn_unit {U : X.Opens} {s : Γ(𝟙_ X.Modules, U)} (hs : IsFrameOn s U) :
    IsUnit (show Γ(X, U) from s) := by
  obtain ⟨g, hg⟩ := (hs le_rfl le_rfl).2 (unitSection U)
  have hg' : g * (show Γ(X, U) from s) = 1 := by
    have : (𝟙_ X.Modules).presheaf.map (homOfLE (le_refl U)).op s = s := by
      rw [show (homOfLE (le_refl U)).op = 𝟙 (Opposite.op U) from rfl, CategoryTheory.Functor.map_id]; rfl
    rw [this] at hg
    exact hg
  exact ⟨⟨_, g, by rw [mul_comm]; exact hg', hg'⟩, rfl⟩

variable [IsIntegral X]

theorem nonempty_inf (U W : X.Opens) [hU : Nonempty U] [hW : Nonempty W] : Nonempty (U ⊓ W : X.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

structure IsPres (N : X.Modules) (ψ : ∀ U : X.Opens, Γ(N, U) →+ (X.functionField : Type u)) : Prop where
  nat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(N, U), ψ V (N.presheaf.map (homOfLE h).op m) = ψ U m
  smul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(N, U)),
    ψ U (a • m) = algebraMap Γ(X, U) X.functionField a * ψ U m
  inj : ∀ U : X.Opens, Nonempty U → Function.Injective (ψ U)

theorem germ_res_apply' {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) = X.germToFunctionField U a := by
  show (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField V).hom a = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

open Classical in

def germPres (N : X.Modules) (eN : N ≅ 𝟙_ X.Modules) (U : X.Opens) : Γ(N, U) →+ (X.functionField : Type u) :=
  if h : Nonempty U then
    (haveI := h; ((X.germToFunctionField U).hom : Γ(X, U) →+* X.functionField).toAddMonoidHom.comp
      (show Γ(N, U) →+ Γ(X, U) from (eN.hom.app U).hom))
  else 0

theorem germPres_apply (N : X.Modules) (eN : N ≅ 𝟙_ X.Modules) (U : X.Opens) [h : Nonempty U] (m : Γ(N, U)) :
    germPres N eN U m = X.germToFunctionField U (show Γ(X, U) from eN.hom.app U m) := by
  rw [germPres, dif_pos h]
  rfl

omit [IsIntegral X] in
theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (φ.app U m) = φ.app V (M.presheaf.map (homOfLE h).op m) := by
  have := (φ.mapPresheaf).naturality (homOfLE h).op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) this) m).symm

omit [IsIntegral X] in
theorem app_injective_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) : Function.Injective (e.hom.app U) := by
  intro x y hxy
  have hx : (e.hom.app U ≫ e.inv.app U) x = x := by
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  have hy : (e.hom.app U ≫ e.inv.app U) y = y := by
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  rw [← hx, ← hy]
  show e.inv.app U (e.hom.app U x) = e.inv.app U (e.hom.app U y)
  rw [hxy]

theorem isPres_germPres (N : X.Modules) (eN : N ≅ 𝟙_ X.Modules) : IsPres N (germPres N eN) where
  nat U V h hV m := by
    haveI := hV
    haveI : Nonempty U := by obtain ⟨⟨v, hv⟩⟩ := hV; exact ⟨⟨v, h hv⟩⟩
    rw [germPres_apply, germPres_apply, ← app_naturality]
    exact germ_res_apply' h _
  smul U _ a m := by
    rw [germPres_apply, germPres_apply, Scheme.Modules.Hom.app_smul, RingHom.algebraMap_toAlgebra]
    show X.germToFunctionField U (a * (show Γ(X, U) from eN.hom.app U m)) = _
    rw [map_mul]
  inj U hU := by
    haveI := hU
    intro x y hxy
    rw [germPres_apply, germPres_apply] at hxy
    exact app_injective_of_iso eN U (X.germToFunctionField_injective U hxy)

variable {L L' : X.Modules}

omit [IsIntegral X] in

theorem IsFrameOn.ne_zero_of_nontrivial {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

theorem exists_forall_tensorSections_eq_mul
    (hL : IsInvertible L) (hL' : IsInvertible L')
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hφ : IsPres L φ) (hφ' : IsPres L' φ') (hφ'' : IsPres (L ⊗ L') φ'') :
    ∃ f : X.functionField, f ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (t : Γ(L', U)),
      φ'' U (tensorSections s t) = f * φ U s * φ' U t := by
  classical
  obtain ⟨hnat, hsmul, hinj⟩ := hφ
  obtain ⟨hnat', hsmul', hinj'⟩ := hφ'
  obtain ⟨hnat'', hsmul'', hinj''⟩ := hφ''

  obtain ⟨U₁, s₁, hη₁, hs₁⟩ := hL.exists_isFrameOn (genericPoint X)
  obtain ⟨U₂, t₂, hη₂, ht₂⟩ := hL'.exists_isFrameOn (genericPoint X)
  let V : X.Opens := U₁ ⊓ U₂
  haveI : Nonempty V := ⟨⟨genericPoint X, hη₁, hη₂⟩⟩
  let s₀ : Γ(L, V) := rM L inf_le_left s₁
  let t₀ : Γ(L', V) := rM L' inf_le_right t₂
  have hs₀ : IsFrameOn s₀ V := (hs₁.map (homOfLE (inf_le_left : V ≤ U₁))).mono inf_le_left
  have ht₀ : IsFrameOn t₀ V := (ht₂.map (homOfLE (inf_le_right : V ≤ U₂))).mono inf_le_right
  have hst₀ : IsFrameOn (tensorSections s₀ t₀) V := hs₀.tensorSections ht₀
  have hφs : φ V s₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hs₀ (hinj V inferInstance (by rw [h, map_zero]))
  have hφt : φ' V t₀ ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial ht₀ (hinj' V inferInstance (by rw [h, map_zero]))
  have hφst : φ'' V (tensorSections s₀ t₀) ≠ 0 := fun h =>
    IsFrameOn.ne_zero_of_nontrivial hst₀ (hinj'' V inferInstance (by rw [h, map_zero]))
  refine ⟨φ'' V (tensorSections s₀ t₀) / (φ V s₀ * φ' V t₀), div_ne_zero hφst (mul_ne_zero hφs hφt), ?_⟩
  intro U hU s t
  let W : X.Opens := U ⊓ V
  haveI : Nonempty W := nonempty_inf U V
  obtain ⟨a, ha⟩ := (hs₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L (inf_le_left : W ≤ U) s)
  obtain ⟨b, hb⟩ := (ht₀ (inf_le_right : W ≤ V) inf_le_right).2 (rM L' (inf_le_left : W ≤ U) t)
  simp only at ha hb
  have e1 : φ'' U (tensorSections s t) = algebraMap Γ(X, W) X.functionField (a * b) * φ'' V (tensorSections s₀ t₀) := by
    rw [← hnat'' U W inf_le_left inferInstance (tensorSections s t), map_homOfLE_tensorSections]
    change φ'' W (tensorSections (rM L (inf_le_left : W ≤ U) s) (rM L' (inf_le_left : W ≤ U) t)) = _
    rw [← ha, ← hb, tensorSections_smul_left, tensorSections_smul_right, ← mul_smul,
      ← map_homOfLE_tensorSections, hsmul'', hnat'' V W inf_le_right inferInstance]
  have e2 : φ U s = algebraMap Γ(X, W) X.functionField a * φ V s₀ := by
    rw [← hnat U W inf_le_left inferInstance s]
    change φ W (rM L (inf_le_left : W ≤ U) s) = _
    rw [← ha, hsmul, hnat V W inf_le_right inferInstance]
  have e3 : φ' U t = algebraMap Γ(X, W) X.functionField b * φ' V t₀ := by
    rw [← hnat' U W inf_le_left inferInstance t]
    change φ' W (rM L' (inf_le_left : W ≤ U) t) = _
    rw [← hb, hsmul', hnat' V W inf_le_right inferInstance]
  rw [e1, e2, e3, map_mul]
  field_simp
  try ring

theorem exists_isPres_tensorPow (hL : IsInvertible L) (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hφ : IsPres L φ) (n : ℕ) :
    ∃ (c : X.functionField) (ψ : ∀ U : X.Opens, Γ(L.tensorPow n, U) →+ (X.functionField : Type u)),
      c ≠ 0 ∧ IsPres (L.tensorPow n) ψ ∧
      ∀ (U : X.Opens) [Nonempty U] (s : Γ(L, U)), ψ U (tensorPowSection s n) = c * (φ U s) ^ n := by
  induction n with
  | zero =>
    refine ⟨1, germPres (𝟙_ X.Modules) (Iso.refl _), one_ne_zero, isPres_germPres _ _, ?_⟩
    intro U hU s
    rw [tensorPowSection_zero, pow_zero, mul_one]
    erw [germPres_apply]
    show X.germToFunctionField U (show Γ(X, U) from unitSection U) = 1
    exact map_one _
  | succ n ih =>
    obtain ⟨c, ψ, hc, hψ, hψs⟩ := ih
    obtain ⟨ψ', h1, h2, h3⟩ := IsInvertible.exists_functionField_presentation (L.tensorPow (n + 1)) (hL.tensorPow (n + 1))
    have hψ' : IsPres (L.tensorPow n ⊗ L) ψ' := ⟨h1, fun U _ a m => h2 U a m, h3⟩
    obtain ⟨f, hf, hcal⟩ := exists_forall_tensorSections_eq_mul (hL.tensorPow n) hL ψ φ ψ' hψ hφ hψ'
    refine ⟨f * c, ψ', mul_ne_zero hf hc, ⟨h1, fun U _ a m => h2 U a m, h3⟩, ?_⟩
    intro U hU s
    rw [tensorPowSection_succ]
    erw [hcal U (tensorPowSection s n) s]
    rw [hψs, pow_succ]
    ring

theorem exists_forall_exists_frame_unit_germ_eq_mul_pow
    (L : X.Modules) (hL : IsInvertible L) (n : ℕ)
    (eL : L.tensorPow n ≅ 𝟙_ X.Modules)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) :
    ∃ F : X.functionField, F ≠ 0 ∧ ∀ x : X, ∃ (U : X.Opens) (hx : x ∈ U) (e : Γ(L, U)) (u : Γ(X, U)),
      IsFrameOn e U ∧ IsUnit u ∧
      (letI : Nonempty U := ⟨⟨x, hx⟩⟩; X.germToFunctionField U u) = F * (φ U e) ^ n := by
  classical
  have hφ : IsPres L φ := ⟨hnat, fun U _ a m => hsmul U a m, hinj⟩
  obtain ⟨c, ψ, hc, hψ, hψs⟩ := exists_isPres_tensorPow hL φ hφ n

  have hχ := isPres_germPres (L.tensorPow n) eL
  have hsec : ∃ (U : X.Opens) (m : Γ(L.tensorPow n, U)), m ≠ 0 := by
    obtain ⟨U₁, s₁, hη₁, hs₁⟩ := hL.exists_isFrameOn (genericPoint X)
    haveI : Nonempty U₁ := ⟨⟨_, hη₁⟩⟩
    exact ⟨U₁, tensorPowSection s₁ n, IsFrameOn.ne_zero_of_nontrivial (hs₁.tensorPowSection n)⟩
  obtain ⟨g, hg, hgχ⟩ := Scheme.Modules.exists_forall_eq_mul_of_presentations (L.tensorPow n) ψ (germPres _ eL)
    hψ.nat hχ.nat (fun U _ a m => hψ.smul U a m) (fun U _ a m => hχ.smul U a m) hψ.inj hχ.inj hsec
  refine ⟨g * c, mul_ne_zero hg hc, fun x => ?_⟩
  obtain ⟨U, e, hxU, he⟩ := hL.exists_isFrameOn x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨U, hxU, e, (show Γ(X, U) from eL.hom.app U (tensorPowSection e n)), he, ?_, ?_⟩
  · exact isUnit_of_isFrameOn_unit ((he.tensorPowSection n).map_iso eL)
  · show X.germToFunctionField U (show Γ(X, U) from eL.hom.app U (tensorPowSection e n)) = _
    rw [← germPres_apply, hgχ, hψs, mul_assoc]

end LocalPow

section UnitOrd

theorem ord_pointEquivPlace_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type} [Field L] [Algebra K L]
    (Mdl : CurveModel K L) (U : Mdl.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(Mdl.C, U)) (hs : IsUnit s)
    (z : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    (Mdl.pointEquivPlace z).ord (Mdl.ffEquiv.symm (Mdl.C.germToFunctionField U s)) = 0 := by
  obtain ⟨s', hs'⟩ := hs.exists_right_inv
  have h1 := (Mdl.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace U s z hz).1
  have h2 := (Mdl.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace U s' z hz).1
  have hab : Mdl.ffEquiv.symm (Mdl.C.germToFunctionField U s) * Mdl.ffEquiv.symm (Mdl.C.germToFunctionField U s') = 1 := by
    rw [← map_mul, ← map_mul, hs', map_one, map_one]
  let uu : ((Mdl.pointEquivPlace z).toValuationSubring)ˣ :=
    ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext hab, Subtype.ext (by rw [mul_comm] at hab; exact hab)⟩
  exact AlgebraicCurve.Place.ord_coe_unit _ uu

end UnitOrd

section Gauss

theorem eq_mul_inv_pow {F : Type*} [Field F] {a b f X : F} (n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : X = a ^ n * (f * b ^ n)) : f = X * ((b * a)⁻¹) ^ n := by
  subst h
  rw [inv_pow, mul_pow]
  field_simp

theorem mem_of_pow_mem {F : Type*} [Field F] (O : ValuationSubring F) {b : F} {n : ℕ} (hn : n ≠ 0)
    (h : b ^ n ∈ O) : b ∈ O := by
  rw [← O.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

end Gauss

end PPR

end

set_option maxHeartbeats 3200000 in
open ModularCurve in

theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (σ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : barPt Pl ≫ σ.1 = (O.pts (AlgebraicCurve.Pic0.mk Dv)).1)
    (hpσ : (fun τ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g =>
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ τ σ)^[p] ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).one _)

    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v = v.ord f)
    (y : LaurentSeries ↥Pl)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y)
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y) :
    ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
      (p : ℤ) ∣ v.ord g := by
  classical
  intro v
  haveI : NeZero (M / p) := ModularCurve.neZero_div p M hpM

  obtain ⟨Pbar, rfl⟩ := (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint_bijective.2 v

  have hρbar : barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) = genPt p := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  let gA : 𝔛.Meta.C ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (𝔛.eeta ≫ pullback.fst _ _) (𝔛.Meta.toBase ≫ barPt Pl) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, 𝔛.heeta, Category.assoc, hρbar])
  have hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl := pullback.lift_snd _ _ _
  let bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) (by
      rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) :=
    pullback.lift_snd _ _ _

  obtain ⟨hint, hdense, -⟩ := ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂
  haveI := hint
  obtain ⟨-, Ψ, hΨ⟩ := ModularCurve.XHDRModelAtP.isOpenImmersion_and_exists_functionField_ringEquiv_of_genericFibre p M H hpM hj 𝔛 Pl hPl ρ hρ gA hgA₁ hgA₂

  let Lσ := (hD.poincare.pullbackAlong σ).L
  have hLσ : Scheme.Modules.IsInvertible Lσ := (hD.poincare.pullbackAlong σ).isInvertible
  obtain ⟨θ⟩ := PPR.nonempty_tensorPow_poincare_iso_unit_of_iterate (P := algEquivZeroGroupCut _ _) hD
    (Spec.map (CommRingCat.ofHom ρ)) σ p hpσ

  obtain ⟨φ, hφnat, hφsmul, hφinj⟩ := Scheme.Modules.IsInvertible.exists_functionField_presentation Lσ hLσ
  obtain ⟨F, hF0, hF⟩ := PPR.exists_forall_exists_frame_unit_germ_eq_mul_pow Lσ hLσ p θ φ hφnat hφsmul hφinj

  have key3 : ∃ μ : ↥(ModularCurve.xHFunctionFieldBar M H), f = Ψ F * μ ^ p := by

    have N3 : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H), x ≠ 0 →
        (∀ W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H), W.ord x = 0) →
        ∃ c : AlgebraicClosure ℚ, x = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c := by
      haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
      have hjmem : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.jqModC ℚ) ∈ ModularCurve.xHFunctionFieldBar M H :=
        ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC_mono ℚ le_top hj)
      obtain ⟨htr, hfd⟩ :=
        ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
          (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) ⟨_, hjmem⟩
          (show (ModularCurve.jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = _ from ModularCurve.map_jqModC _)
      haveI := hfd
      intro x _ hx
      obtain ⟨c, hc⟩ := AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed _ htr hx
      exact ⟨c, hc.symm⟩
    obtain ⟨Dφ, g₁, hg₁, hDφ, hgen⟩ := ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 Λ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc
      hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ ρ hρ gA hgA₁ hgA₂ (AlgebraicCurve.Pic0.mk Dv) Dv rfl
      σ hσ φ hφnat hφsmul hφinj Ψ hΨ
    have hΨF0 : Ψ F ≠ 0 := (map_ne_zero Ψ).2 hF0

    have hordF : ∀ W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        W.ord (Ψ F) = W.ord f + (p : ℤ) * W.ord g₁ := by
      intro W
      set q := 𝔛.Meta.pointEquivPlace.symm W with hq
      have hWq : 𝔛.Meta.pointEquivPlace q = W := Equiv.apply_symm_apply _ _
      obtain ⟨U, hxU, e, u, he, hu, hgerm⟩ := hF (gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))
      haveI hUne : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hxU⟩⟩
      have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)) := hdense U hUne
      have he0 : φ U e ≠ 0 := fun h0 =>
        PPR.IsFrameOn.ne_zero_of_nontrivial he (hφinj U hUne (by rw [h0, map_zero]))
      have hΨe0 : Ψ (φ U e) ≠ 0 := (map_ne_zero Ψ).2 he0

      have hgenq : W.ord (Ψ (φ U e)) = -Dφ W := by
        rw [← hWq]
        refine (hgen U q hxU e).2 (fun W' hW' _ m' => ?_)
        obtain ⟨a, ha⟩ := (he hW' hW').2 m'
        exact ⟨a, ha.symm⟩

      have hz : ⊤ ≤ q.1 ⁻¹ᵁ (gA ⁻¹ᵁ U) := by
        intro pt _
        show gA.base (q.1.base pt) ∈ U
        rw [Subsingleton.elim pt (IsLocalRing.closedPoint (AlgebraicClosure ℚ))]
        exact hxU
      have hu0 : W.ord (Ψ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U u)) = 0 := by
        rw [hΨ U hne u, ← hWq]
        haveI := hne
        exact PPR.ord_pointEquivPlace_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit 𝔛.Meta (gA ⁻¹ᵁ U)
          ((gA.app U).hom u) (hu.map _) q hz
      have hcomb := congrArg (fun t => W.ord (Ψ t)) hgerm
      simp only at hcomb
      rw [hu0, map_mul, map_pow, AlgebraicCurve.Place.ord_mul _ hΨF0 (pow_ne_zero _ hΨe0), ← zpow_natCast,
        AlgebraicCurve.Place.ord_zpow, hgenq, hDφ W] at hcomb
      have hdv := hdiv W
      linarith

    have hx0 : Ψ F / (f * g₁ ^ p) ≠ 0 := div_ne_zero hΨF0 (mul_ne_zero hf0 (pow_ne_zero _ hg₁))
    have hx : ∀ W : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        W.ord (Ψ F / (f * g₁ ^ p)) = 0 := by
      intro W
      rw [div_eq_mul_inv, AlgebraicCurve.Place.ord_mul _ hΨF0 (inv_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hg₁))),
        AlgebraicCurve.Place.ord_inv, AlgebraicCurve.Place.ord_mul _ hf0 (pow_ne_zero _ hg₁), ← zpow_natCast,
        AlgebraicCurve.Place.ord_zpow, hordF W]
      ring
    obtain ⟨c, hc⟩ := N3 _ hx0 hx
    have hc0 : c ≠ 0 := by rintro rfl; exact hx0 (by rw [hc, map_zero])
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (NeZero.pos p)
    have hd0 : d ≠ 0 := by rintro rfl; exact hc0 (by rw [← hd, zero_pow (NeZero.ne p)])
    refine ⟨(g₁ * algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) d)⁻¹, ?_⟩
    have had0 : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) d ≠ 0 := (map_ne_zero _).2 hd0
    rw [← hd, map_pow, div_eq_iff (mul_ne_zero hf0 (pow_ne_zero _ hg₁))] at hc
    exact PPR.eq_mul_inv_pow p had0 hg₁ hc

  have key : ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
      (hzU : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1) ∈ U)
      (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)))
      (s : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U))
      (b : ↥(ModularCurve.xHFunctionFieldBar M H)),
      IsUnit s ∧ f = b ^ p * 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) := by
    obtain ⟨μ, hμ⟩ := key3
    obtain ⟨U, hzU, e, u, he, hu, hgerm⟩ := hF (bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base Pbar.1))
    haveI hUne : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hzU⟩⟩
    have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)) := hdense U hUne
    refine ⟨U, hzU, hne, u, μ * (Ψ (φ U e))⁻¹, hu, ?_⟩

    have he0 : φ U e ≠ 0 := fun h0 =>
      PPR.IsFrameOn.ne_zero_of_nontrivial he (hφinj U hUne (by rw [h0, map_zero]))
    have hΨe0 : Ψ (φ U e) ≠ 0 := (map_ne_zero Ψ).2 he0
    have hfs : 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom u)) =
        Ψ F * Ψ (φ U e) ^ p := by
      rw [← hΨ U hne u, ← map_pow, ← map_mul, ← hgerm]
    rw [hfs, hμ, mul_pow, inv_pow]
    field_simp
  obtain ⟨U, hzU, hne, s, b, hsU, hfb⟩ := key

  obtain ⟨hneV, xs, ys, hys, hW, hR, hU⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ Pbar U hzU hne s
  have hord0 := hU hsU

  set fs : ↥(ModularCurve.xHFunctionFieldBar M H) :=
    𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) with hfs_def
  set rs : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
    (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField
      ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s)) with hrs_def

  have hrs0 : rs ≠ 0 := (((hsU.map _).map _).map _).ne_zero

  obtain ⟨Rg, hRi, -, hRiii⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (ΓM M H) (ModularCurve.translation_mem_GammaH M H)
  have h1 : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) (1 : LaurentSeries ↥Pl) ≠ 0 := by
    rw [map_one]; exact one_ne_zero
  have hfy' : ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
      ModularCurve.coeffMap Pl.subtype 1 = ModularCurve.coeffMap Pl.subtype y := by
    rw [map_one, mul_one]; exact hfy
  have hfO : (f : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ Rg.integers := (hRi f).2 ⟨y, 1, h1, hfy'⟩
  have hres_f : ((Rg.residue ⟨f, hfO⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓM M H))) :
      LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y := by
    have := hRiii f hfO y 1 h1 hfy'
    rwa [map_one, mul_one] at this
  have hfsO : fs ∈ Rg.integers := (hRi fs).2 ⟨xs, ys, hys, hW⟩
  have hres_fs : ((Rg.residue ⟨fs, hfsO⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓM M H))) :
      LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = (rs : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
    have := hRiii fs hfsO xs ys hys hW
    rw [← hR] at this
    exact mul_right_cancel₀ hys this
  have hres_fs0 : Rg.residue ⟨fs, hfsO⟩ ≠ 0 := by
    intro h0
    apply hrs0
    have : ((Rg.residue ⟨fs, hfsO⟩ : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓM M H))) :
      LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = 0 := by rw [h0]; rfl
    rw [hres_fs] at this
    exact_mod_cast this

  obtain ⟨uO, huO⟩ := Rg.isUnit_of_residue_ne_zero hres_fs0
  have hfs0 : fs ≠ 0 := fun h => hres_fs0 (by
    have : (⟨fs, hfsO⟩ : Rg.integers) = 0 := Subtype.ext h
    rw [this, map_zero])
  have hinvO : (↑(uO⁻¹) : Rg.integers).1 = fs⁻¹ := by
    have hmul : (↑uO : Rg.integers).1 * (↑(uO⁻¹) : Rg.integers).1 = (1 : Rg.integers).1 :=
      congrArg Subtype.val (Units.mul_inv uO)
    rw [huO] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul)
  have hbpO : b ^ p ∈ Rg.integers := by
    have hb : b ^ p = f * fs⁻¹ := by rw [hfb, mul_inv_cancel_right₀ hfs0]
    rw [hb, ← hinvO]
    exact Rg.integers.toSubring.mul_mem hfO (↑(uO⁻¹) : Rg.integers).2
  have hbO : b ∈ Rg.integers := PPR.mem_of_pow_mem Rg.integers (NeZero.ne p) hbpO

  have hresO : Rg.residue ⟨f, hfO⟩ = Rg.residue ⟨b, hbO⟩ ^ p * Rg.residue ⟨fs, hfsO⟩ := by
    rw [← map_pow, ← map_mul]
    congr 1
    exact Subtype.ext hfb

  obtain ⟨b', hb'⟩ := ModularCurve.exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP p M H hpM hpM2 hHp
    (IsLocalRing.ResidueField ↥Pl) (Rg.residue ⟨b, hbO⟩)

  have hgLS : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      ((b' ^ p * rs : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries _) := by
    rw [hg, ← hres_f, hresO]
    push_cast
    rw [hb', hres_fs]
  have hg' : g = b' ^ p * rs := Subtype.ext hgLS
  have hg0 : g ≠ 0 := by
    intro h0
    apply hy
    rw [← hg, h0]
    rfl
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    apply hg0
    rw [hg', zero_pow (NeZero.ne p), zero_mul]
  have hordg : ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord g =
      (p : ℤ) * ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Pbar).ord b' := by
    rw [hg', AlgebraicCurve.Place.ord_mul _ (pow_ne_zero p hb'0) hrs0, hord0, add_zero,
      ← zpow_natCast, AlgebraicCurve.Place.ord_zpow]
  exact ⟨_, hordg⟩

end S_ModularCurve_JHNeronObjectAtP_dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue (solution)
