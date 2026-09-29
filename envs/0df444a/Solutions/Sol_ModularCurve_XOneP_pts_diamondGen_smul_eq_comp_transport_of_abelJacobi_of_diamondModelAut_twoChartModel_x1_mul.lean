-- Prove2me | solution 1 for ModularCurve.XOneP.pts_diamondGen_smul_eq_comp_transport_of_abelJacobi_of_diamondModelAut_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b1586622-7607-51d9-af6e-8b045901eaba

import Mathlib
import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Theorems.Thm_ModularCurve_XOneP_pointEquivPlace_eq_diamondAutBar_inv_smul_of_chartPin_of_diamondModelAut_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul
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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_pts_diamondGen_smul_eq_comp_transport_of_abelJacobi_of_diamondModelAut_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u

theorem DR_theta_pullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (g : C ⟶ C) (hg : g ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) g hg t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h.classify t N hN)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (postComp θ a)).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        ((Scheme.Modules.pullback (curveChange (c := c) (c' := c) g hg t)).obj (h.poincare.pullbackAlong a).L)) := by
  classical
  let P := h.poincare
  let cW : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)), pullback c s ⟶ pullback c s :=
    fun s => curveChange (c := c) (c' := c) g hg s

  have CUT : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R))
      (M : RigidifiedLineBundle c ε s), FibrewiseAlgEquivZero M →
      FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε)
        ((Scheme.Modules.pullback (cW s)).obj M.L) (M.isInvertible.pullback _)) := by
    intro S s M hM k _ _ x
    obtain ⟨e49⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
      (rigSection c s ε) (pullback.snd c s) ((Scheme.Modules.pullback (cW s)).obj M.L)
      (M.isInvertible.pullback _) k x
    rw [RigidifiedLineBundle.ofInvertible_L]
    refine IsAlgEquivZero.of_iso e49.symm ?_
    let e : Limits.pullback (pullback.snd c s) x ⟶ Limits.pullback (pullback.snd c s) x :=
      pullback.map _ _ _ _ (cW s) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, curveChange_snd]) (by simp)
    have he : e ≫ fibreAt c s x = fibreAt c s x := by
      simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
    have hfst : e ≫ pullback.fst (pullback.snd c s) x = pullback.fst (pullback.snd c s) x ≫ cW s := by
      simp only [e, pullback.lift_fst]
    refine IsAlgEquivZero.of_iso ?_ ((hM k x).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm

  have IDpt : Nonempty ((P.pullbackAlong (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase)).L ≅ P.L) := by
    have hb : baseChangeSnd c (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase) = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [BaseChange.baseChangeSnd_fst', Category.id_comp]
      · rw [BaseChange.baseChangeSnd_snd', Category.id_comp]; exact (Category.comp_id _).symm
    exact ⟨(Scheme.Modules.pullbackCongr hb).app _ ≪≫ (Scheme.Modules.pullbackId _).app _⟩

  let N₀ := RigidifiedLineBundle.ofInvertible (ε := ε) ((Scheme.Modules.pullback (cW D.toBase)).obj P.L) (P.isInvertible.pullback _)
  have hN₀ : FibrewiseAlgEquivZero N₀ := CUT D.toBase P h.poincare_mem
  have Iθ : Nonempty ((P.pullbackAlong θ).L ≅ N₀.L) := by
    have hid : (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase) = h.classify D.toBase P h.poincare_mem :=
      h.classify_unique _ _ _ _ IDpt
    have hcl : postComp θ (h.classify D.toBase P h.poincare_mem) = h.classify D.toBase N₀ hN₀ :=
      hθ D.toBase P h.poincare_mem N₀ hN₀ (rigCorrection ε D.toBase ((Scheme.Modules.pullback (cW D.toBase)).obj P.L))
        (((P.isInvertible.pullback _).pullback _).dual).1 ⟨Iso.refl _⟩
    have hθeq : postComp θ (h.classify D.toBase P h.poincare_mem) = θ := by
      rw [← hid]; exact Subtype.ext (Category.id_comp _)
    rw [hθeq] at hcl
    rw [hcl]
    exact h.classify_spec D.toBase N₀ hN₀

  have hcWnat : ∀ {S S' : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)} {s' : S' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver s' s), baseChangeSnd c ψ ≫ cW s = cW s' ≫ baseChangeSnd c ψ :=
    fun ψ => (curveChange_baseChangeSnd g hg ψ).symm

  obtain ⟨iθ⟩ := Iθ
  obtain ⟨inat⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) a
    (L := (Scheme.Modules.pullback (cW D.toBase)).obj P.L) (P.isInvertible.pullback _)
  have isq : (Scheme.Modules.pullback (baseChangeSnd c a)).obj ((Scheme.Modules.pullback (cW D.toBase)).obj P.L) ≅
      (Scheme.Modules.pullback (cW t)).obj (P.pullbackAlong a).L :=
    (Scheme.Modules.pullbackComp _ _).app P.L ≪≫ (Scheme.Modules.pullbackCongr (hcWnat a)).app P.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app P.L).symm
  obtain ⟨icongr⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((P.isInvertible.pullback _).pullback _) ((P.pullbackAlong a).isInvertible.pullback _) isq
  refine ⟨(RigidifiedLineBundle.pullbackAlongPullbackAlongIso' P θ a).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c a)).mapIso iθ ≪≫ inat ≪≫ icongr ≪≫ ?_⟩
  rw [RigidifiedLineBundle.ofInvertible_L]

theorem DR_theta_mul_zero
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (g : C ⟶ C) (hg : g ≫ c = c)
    (θ : SchemeHomOver D.toBase D.toBase)
    (hν : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (postComp θ a)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          ((Scheme.Modules.pullback (curveChange (c := c) (c' := c) g hg t)).obj (h.poincare.pullbackAlong a).L))) :
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        postComp θ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t (postComp θ x) (postComp θ y)) ∧
      D.zeroSection ≫ θ.1 = D.zeroSection := by
  obtain ⟨N, hN, hNmul, hN0⟩ :=
    RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange (ε := ε) (ε' := ε) g hg h h
  have hθN : θ = N := by
    let i : SchemeHomOver D.toBase D.toBase := ⟨𝟙 D.P, Category.id_comp _⟩
    have h1 : postComp θ i = θ := Subtype.ext (Category.id_comp _)
    have h2 : NeronModelInfra.schemeHomOverComp i N = N := Subtype.ext (Category.id_comp _)
    have e1 := hν D.toBase i
    have e2 := hN D.toBase i
    rw [h1] at e1
    rw [h2] at e2
    exact h.ext_of_iso D.toBase θ N ⟨e1.some ≪≫ e2.some.symm⟩
  subst hθN
  exact ⟨fun t x y => hNmul t x y, hN0⟩

theorem DR_isIso_curveChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (g : C ⟶ C) [IsIso g] (hg : g ≫ c = c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsIso (curveChange (c := c) (c' := c) g hg t) := by
  unfold curveChange; infer_instance

theorem DR_pullback_curveChange_ofPoint_lineBundle
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)]
    (g : C ⟶ C) [IsIso g] (hg : g ≫ c = c)
    (y y' : T ⟶ C) (hy : y ≫ c = t) (hy' : y' ≫ c = t) (hyy' : y' ≫ g = y) :
    Nonempty ((Scheme.Modules.pullback (curveChange (c := c) (c' := c) g hg t)).obj
        (RelEffCartierDiv.ofPoint c y hy).lineBundle ≅ (RelEffCartierDiv.ofPoint c y' hy').lineBundle) := by
  haveI := DR_isIso_curveChange (c := c) g hg t
  have hp : graphOver c y' hy' ≫ curveChange (c := c) (c' := c) g hg t = graphOver c y hy := by
    apply pullback.hom_ext
    · simp only [curveChange, graphOver, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hyy']
    · simp only [curveChange, graphOver, Category.assoc, pullback.lift_snd, Category.comp_id]
  have hI : (graphOver c y hy).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y hy)
  have hI' : (graphOver c y' hy').ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y' hy')
  have key := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (curveChange (c := c) (c' := c) g hg t) (graphOver c y hy) (graphOver c y' hy') hp hI hI' 1
  rw [pow_one, pow_one] at key
  exact key.1

set_option maxHeartbeats 6400000 in
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
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

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
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

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

    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (w : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hw : w.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (ρ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((ρ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = θ b)
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ w.hom = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (θw : SchemeHomOver D.toBase D.toBase)
    (hθw : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A))
        (P₁ : RigidifiedLineBundle (ModularCurve.TwoChart.modelTo A (↥K) j) ε t) (hP₁ : FibrewiseAlgEquivZero P₁)
        (P₂ : RigidifiedLineBundle (ModularCurve.TwoChart.modelTo A (↥K) j) ε t) (hP₂ : FibrewiseAlgEquivZero P₂)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (P₂.L ≅ (Scheme.Modules.pullback (curveChange (c := ModularCurve.TwoChart.modelTo A (↥K) j)
            (c' := ModularCurve.TwoChart.modelTo A (↥K) j) w.hom hw t)).obj P₁.L ⊗
          (Scheme.Modules.pullback (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) t)).obj Q) →
        postComp θw (hrep.some.classify t P₁ hP₁) = hrep.some.classify t P₂ hP₂) :
    letI := ModularCurve.heckeModuleOneBar (M * p)
    ∀ x : ModularCurve.JOne (M * p), (gpts (ModularCurve.diamondGen d • x)).1 = (gpts x).1 ≫ θw.1 := by
  letI := ModularCurve.heckeModuleOneBar (M * p)
  classical

  let Xm := ModularCurve.TwoChart.modelTo A (↥K) j
  let Qb := AlgebraicClosure ℚ
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of A) := specMap A Qb
  let h := hrep.some
  let P := h.poincare
  let Glaw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut Xm ε) h
  letI grp : Group (SchemeHomOver tQ D.toBase) := Glaw.pointGroup tQ
  let cW := curveChange (c := Xm) (c' := Xm) w.hom hw tQ

  have hθpull : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((P.pullbackAlong (postComp θw a)).L ≅
        Scheme.Modules.rigidify (rigSection Xm t ε) (pullback.snd Xm t)
          ((Scheme.Modules.pullback (curveChange (c := Xm) (c' := Xm) w.hom hw t)).obj (P.pullbackAlong a).L)) :=
    fun t a => DR_theta_pullback h w.hom hw θw (fun t M hM N hN Q hQ hiso => hθw t M hM N hN Q hQ hiso) t a
  have hθmz := DR_theta_mul_zero h w.hom hw θw (fun t a => hθpull t a)
  have hθmul : ∀ x y : SchemeHomOver tQ D.toBase, postComp θw (x * y) = postComp θw x * postComp θw y :=
    fun x y => hθmz.1 tQ x y
  have hθ0 : D.zeroSection ≫ θw.1 = D.zeroSection := hθmz.2

  have hone : ((1 : SchemeHomOver tQ D.toBase)).1 = tQ ≫ D.zeroSection := by
    have hn := RelativeGroupLaw.one_natural Glaw (𝟙 _) tQ tQ (Category.comp_id _)
    have h1 : (Glaw.one (𝟙 _)).1 = D.zeroSection := RepresentsRelSubPic.relativeGroupLaw_one (P := algEquivZeroGroupCut Xm ε) h
    change (Glaw.one tQ).1 = _
    rw [← hn, GoodReductionJacobian.schemeHomOverComp_coe, h1]
  have hθone : postComp θw (1 : SchemeHomOver tQ D.toBase) = 1 := by
    apply Subtype.ext
    change (1 : SchemeHomOver tQ D.toBase).1 ≫ θw.1 = _
    rw [hone, Category.assoc, hθ0]
  have hθinv : ∀ x : SchemeHomOver tQ D.toBase, postComp θw x⁻¹ = (postComp θw x)⁻¹ := by
    intro x
    apply eq_inv_of_mul_eq_one_left
    rw [← hθmul, inv_mul_cancel, hθone]

  have hgmul : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) = gpts x * gpts y := fun x y => hgadd x y
  have hg0 : gpts 0 = 1 := by
    have h00 := hgmul 0 0
    rw [add_zero] at h00
    have h2 : gpts 0 * gpts 0 = gpts 0 * 1 := by rw [mul_one]; exact h00.symm
    exact mul_left_cancel h2
  have hgneg : ∀ x : ModularCurve.JOne (M * p), gpts (-x) = (gpts x)⁻¹ := by
    intro x
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← hgmul, add_neg_cancel, hg0]
  have hgsub : ∀ x y : ModularCurve.JOne (M * p), gpts (x - y) = gpts x * (gpts y)⁻¹ := by
    intro x y; rw [sub_eq_add_neg, hgmul, hgneg]

  have hw' : w.inv ≫ Xm = Xm := by rw [Iso.inv_comp_eq, hw]
  have hsndi : inv eη ≫ Mη.toBase = pullback.snd Xm tQ := by rw [← heη, IsIso.inv_hom_id_assoc]
  let AJ : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} → SchemeHomOver tQ D.toBase :=
    fun b => ⟨b.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, ← Category.assoc, b.2, Category.id_comp]⟩
  let bar : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} → SchemeHomOver tQ Xm :=
    fun b => ⟨b.1 ≫ eη ≫ pullback.fst Xm tQ, by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, b.2,
        Category.id_comp]⟩
  let wb : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    fun b => ⟨b.1 ≫ eη ≫ curveChange (c := Xm) (c' := Xm) w.inv hw' tQ ≫ inv eη, by
      rw [Category.assoc, Category.assoc, Category.assoc, hsndi, curveChange_snd, heη]; exact b.2⟩

  have hwbR : ∀ b, b.1 ≫ eη ≫ pullback.fst Xm tQ = (wb b).1 ≫ eη ≫ pullback.fst Xm tQ ≫ w.hom := by
    intro b
    show _ = (b.1 ≫ eη ≫ curveChange (c := Xm) (c' := Xm) w.inv hw' tQ ≫ inv eη) ≫ eη ≫ pullback.fst Xm tQ ≫ w.hom
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, curveChange, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id]
  have hwbL : ∀ b, ((wb b).1 ≫ eη ≫ pullback.fst Xm tQ) ≫ w.hom = b.1 ≫ eη ≫ pullback.fst Xm tQ := by
    intro b; rw [Category.assoc, Category.assoc]; exact (hwbR b).symm

  have hAJε : AJ εbar = 1 := by
    apply Subtype.ext
    change εbar.1 ≫ ajbar = (1 : SchemeHomOver tQ D.toBase).1
    rw [hone]; exact hεbar_aj

  have hgpl : ∀ b, AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • Mη.pointEquivPlace b =
      Mη.pointEquivPlace (wb b) := by
    intro b
    have hDP := ModularCurve.XOneP.pointEquivPlace_eq_diamondAutBar_inv_smul_of_chartPin_of_diamondModelAut_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj Mη eη heη hMηpin d hd θ hθ w.hom hw ρ hρ hwρ (wb b) b (hwbR b)
    rw [hDP, smul_inv_smul]

  haveI hsmQ : SmoothOfRelativeDimension 1 (pullback.snd Xm tQ) := by
    rw [← hsndi]; exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (inv eη ≫ Mη.toBase))
  haveI : IsSeparated Xm := inferInstance
  haveI hcWiso : IsIso cW := DR_isIso_curveChange (c := Xm) w.hom hw tQ

  have hI1 : ∀ b, Nonempty ((P.pullbackAlong (AJ b)).L ≅
      (RelEffCartierDiv.ofPoint Xm (bar b).1 (bar b).2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint Xm (tQ ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by
    intro b
    have hb := ModularCurve.XOneP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ε D hrep hsm hsep hsmL hgiL hprL hgcL Mη eη heη hMηpin hgal hin hcomm hΓA gpts hDL ajL kL
      ajbar εbar hPL hajLε hajL hkL₁ hkL₂ hajbar hajbar_over hεbar hεbar_aj hpts_aj b (bar b) rfl (AJ b) rfl
    exact hb

  have hθQ : ∀ x : SchemeHomOver tQ D.toBase,
      Nonempty ((P.pullbackAlong (postComp θw x)).L ≅ (Scheme.Modules.pullback cW).obj (P.pullbackAlong x).L) := by
    intro x
    obtain ⟨e1⟩ := hθpull tQ x
    obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field (ε := ε) tQ
      (L := (Scheme.Modules.pullback cW).obj (P.pullbackAlong x).L) ((P.pullbackAlong x).isInvertible.pullback _)
    exact ⟨e1 ≪≫ e2⟩

  have hOw : ∀ b, Nonempty ((Scheme.Modules.pullback cW).obj (RelEffCartierDiv.ofPoint Xm (bar b).1 (bar b).2).lineBundle ≅
      (RelEffCartierDiv.ofPoint Xm (bar (wb b)).1 (bar (wb b)).2).lineBundle) := by
    intro b
    exact DR_pullback_curveChange_ofPoint_lineBundle Xm tQ w.hom hw (bar b).1 (bar (wb b)).1 (bar b).2 (bar (wb b)).2
      (hwbL b)

  have hkey2 : ∀ b b', postComp θw (AJ b) * AJ (wb b') = AJ (wb b) * postComp θw (AJ b') := by
    intro b b'
    apply h.ext_of_iso tQ
    obtain ⟨m1⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut Xm ε) h
      (T := Over.mk tQ) (schemeHomOverToOverHom (postComp θw (AJ b))) (schemeHomOverToOverHom (AJ (wb b')))
    obtain ⟨m2⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut Xm ε) h
      (T := Over.mk tQ) (schemeHomOverToOverHom (AJ (wb b))) (schemeHomOverToOverHom (postComp θw (AJ b')))
    obtain ⟨t1⟩ := hθQ (AJ b)
    obtain ⟨t2⟩ := hθQ (AJ b')
    obtain ⟨i1⟩ := hI1 b
    obtain ⟨i2⟩ := hI1 b'
    obtain ⟨i3⟩ := hI1 (wb b)
    obtain ⟨i4⟩ := hI1 (wb b')
    obtain ⟨o1⟩ := hOw b
    obtain ⟨o2⟩ := hOw b'

    let Ob := (RelEffCartierDiv.ofPoint Xm (bar (wb b)).1 (bar (wb b)).2).lineBundle
    let Ob' := (RelEffCartierDiv.ofPoint Xm (bar (wb b')).1 (bar (wb b')).2).lineBundle
    let Iε := (RelEffCartierDiv.ofPoint Xm (tQ ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule
    let Iw := (Scheme.Modules.pullback cW).obj Iε

    have eθb : (P.pullbackAlong (postComp θw (AJ b))).L ≅ Ob ⊗ Iw :=
      t1 ≪≫ (Scheme.Modules.pullback cW).mapIso i1 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o1 ⊗ᵢ Iso.refl _)
    have eθb' : (P.pullbackAlong (postComp θw (AJ b'))).L ≅ Ob' ⊗ Iw :=
      t2 ≪≫ (Scheme.Modules.pullback cW).mapIso i2 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o2 ⊗ᵢ Iso.refl _)
    have eL : (P.pullbackAlong (postComp θw (AJ b) * AJ (wb b'))).L ≅ (Ob ⊗ Iw) ⊗ (Ob' ⊗ Iε) :=
      m1 ≪≫ (eθb ⊗ᵢ i4)
    have eR : (P.pullbackAlong (AJ (wb b) * postComp θw (AJ b'))).L ≅ (Ob ⊗ Iε) ⊗ (Ob' ⊗ Iw) :=
      m2 ≪≫ (i3 ⊗ᵢ eθb')
    refine ⟨eL ≪≫ Scheme.Modules.tensorTensorTensorComm Ob Iw Ob' Iε ≪≫ (Iso.refl _ ⊗ᵢ β_ Iw Iε) ≪≫
      (Scheme.Modules.tensorTensorTensorComm Ob Iε Ob' Iw).symm ≪≫ eR.symm⟩

  have hkey : ∀ b, postComp θw (AJ b) = AJ (wb b) * (AJ (wb εbar))⁻¹ := by
    intro b
    have hk := hkey2 b εbar
    rw [hAJε, hθone, mul_one] at hk
    rw [← hk, mul_inv_cancel_right]

  have hgen : ∀ (a : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),
      (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace a) 1 - Finsupp.single (Mη.pointEquivPlace εbar) 1 →
      gpts (ModularCurve.diamondGen d • Pic0.mk Dv) = postComp θw (gpts (Pic0.mk Dv)) := by
    intro a Dv hDv

    obtain ⟨Dv', hDv', hgp⟩ := hpts_aj a εbar hεbar
    obtain rfl : Dv = Dv' := Subtype.ext (hDv.trans hDv'.symm)
    obtain ⟨D1, hD1, hgp1⟩ := hpts_aj (wb a) εbar hεbar
    obtain ⟨D2, hD2, hgp2⟩ := hpts_aj (wb εbar) εbar hεbar
    have hA0 : gpts (Pic0.mk Dv) = AJ a := Subtype.ext hgp
    have hA1 : gpts (Pic0.mk D1) = AJ (wb a) := Subtype.ext hgp1
    have hA2 : gpts (Pic0.mk D2) = AJ (wb εbar) := Subtype.ext hgp2

    have hsm : ModularCurve.diamondGen d • Pic0.mk Dv = Pic0.mk D1 - Pic0.mk D2 := by
      rw [ModularCurve.heckeModuleOneBar_diamondGen_smul hcomm, ModularCurve.diamondOneBar_apply,
        AlgebraicCurve.SemilinearAut.pic0_smul_mk]
      have hcoe : (AlgebraicCurve.SemilinearAut.degZeroSMulHom
            (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d)) Dv) = D1 - D2 := by
        apply Subtype.ext
        rw [AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom, AddSubgroupClass.coe_sub, hD1, hD2, hDv, smul_sub,
          AlgebraicCurve.SemilinearAut.smul_single, AlgebraicCurve.SemilinearAut.smul_single, hgpl, hgpl]
        abel
      rw [hcoe]
      exact QuotientAddGroup.mk_sub _ D1 D2
    rw [hsm, hgsub, hA0, hA1, hA2, hkey]

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)), v.deg = 1 := fun v =>
    ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ)
      (CongruenceSubgroup.Gamma1 (M * p)) hT (ModularCurve.x1FunctionField (M * p)) rfl v
  have hall : ∀ x : ModularCurve.JOne (M * p), gpts (ModularCurve.diamondGen d • x) = postComp θw (gpts x) := by
    intro x
    have hx := AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single hdeg1 (Mη.pointEquivPlace εbar) x
    refine AddSubgroup.closure_induction (p := fun x _ => gpts (ModularCurve.diamondGen d • x) = postComp θw (gpts x))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨V, hV, rfl⟩
      exact hgen (Mη.pointEquivPlace.symm V) ⟨_, hV⟩ (by rw [Equiv.apply_symm_apply])
    · rw [smul_zero, hg0, hθone]
    · intro x y _ _ hx hy
      try dsimp only at hx hy ⊢
      rw [smul_add, hgmul, hgmul, hx, hy, hθmul]
    · intro x _ hx
      try dsimp only at hx ⊢
      rw [smul_neg, hgneg, hgneg, hx, hθinv]
  intro x
  exact congrArg Subtype.val (hall x)

end S_ModularCurve_XOneP_pts_diamondGen_smul_eq_comp_transport_of_abelJacobi_of_diamondModelAut_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_pts_diamondGen_smul_eq_comp_transport_of_abelJacobi_of_diamondModelAut_twoChartModel_x1_mul (solution)
