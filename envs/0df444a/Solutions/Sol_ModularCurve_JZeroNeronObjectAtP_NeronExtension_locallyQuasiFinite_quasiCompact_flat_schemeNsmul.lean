-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.locallyQuasiFinite_quasiCompact_flat_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f73d926b-d0da-5b6f-961f-a4bd33e41e2b

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_sections_forall_exists_mem_range_openImm_comp_mul
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange_shStr
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal"
p2m_attr_erase "instance" "PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero PresheafOfModules.ExteriorPower.instModulePresheafAb ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRModelPackage.LegTwoInput.mk.injEq ModularCurve.DRModelPackage.LegTwoInput.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one"
p2m_attr_erase "simp" "GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul.GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.one_natural RelativeGroupLaw.nsmul_zero RelativeGroupLaw.nsmul_succ RelativeGroupLaw.idPoint RelativeGroupLaw.schemeNsmul RelativeGroupLaw.baseChangeStr"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative pointGroup mul_inv_cancel one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over baseChangeStr baseChangePointToBase baseChange baseChangePointToBase_mul baseChangePointToBase_one"
namespace CH2
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem comp_schemeNsmul (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t f) :
    z.1 ≫ L.schemeNsmul n = (L.nsmul t n z).1 := by
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (idPoint (f := f)) = z :=
    Subtype.ext (Category.comp_id _)
  have key := congrArg Subtype.val (L.nsmul_natural f t z.1 z.2 n idPoint)
  rw [e, GoodReductionJacobian.schemeHomOverComp_coe] at key
  exact key

abbrev nsmulOver (n : ℕ) : SchemeHomOver f f := ⟨L.schemeNsmul n, L.schemeNsmul_over n⟩

theorem nsmul_mul (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x y : SchemeHomOver t f) : L.nsmul t n (L.mul t x y) = L.mul t (L.nsmul t n x) (L.nsmul t n y) := by
  induction n with
  | zero => simp only [nsmul_zero]; exact (L.one_mul t _).symm
  | succ n ih =>
      simp only [nsmul_succ, ih]
      letI := L.pointGroup t
      show (L.nsmul t n x * L.nsmul t n y) * (x * y) = (L.nsmul t n x * x) * (L.nsmul t n y * y)
      rw [_root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (L.nsmul t n y), show L.nsmul t n y * x = x * L.nsmul t n y from hc t _ _,
        _root_.mul_assoc]

theorem isHom_nsmulOver (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.mul t x y) (nsmulOver L n) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (nsmulOver L n)) (NeronModelInfra.schemeHomOverComp y (nsmulOver L n)) := by
  have key : ∀ z : SchemeHomOver t f, NeronModelInfra.schemeHomOverComp z (nsmulOver L n) = L.nsmul t n z :=
    fun z => Subtype.ext (comp_schemeNsmul L n z)
  rw [key, key, key, nsmul_mul L hc]

def reb {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (x : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨x.1, x.2.trans e⟩

theorem nsmul_reb_coe {T : Scheme.{u}} {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (n : ℕ)
    (x : SchemeHomOver s f) : (L.nsmul s' n (reb e x)).1 = (L.nsmul s n x).1 := by
  cases e; rfl

variable {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem baseChangePointToBase_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((L.baseChange ι).nsmul t' n x) = L.nsmul (t' ≫ ι) n (baseChangePointToBase ι x) := by
  induction n with
  | zero => rw [nsmul_zero, nsmul_zero, baseChangePointToBase_one]
  | succ n ih => rw [nsmul_succ, nsmul_succ, baseChangePointToBase_mul, ih]

theorem schemeNsmul_baseChange (n : ℕ) :
    (L.baseChange ι).schemeNsmul n = (NeronSpecialFibreInfra.fibreRestrictAlong ι f f (nsmulOver L n)).1 := by
  apply pullback.hom_ext
  ·
    rw [NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst]
    have h1 : (L.baseChange ι).schemeNsmul n ≫ pullback.fst f ι =
        (L.nsmul (pullback.snd f ι ≫ ι) n (baseChangePointToBase ι (idPoint (f := baseChangeStr ι f)))).1 := by
      rw [← baseChangePointToBase_nsmul]; rfl
    have h2 : pullback.fst f ι ≫ (nsmulOver L n).1 =
        (L.nsmul (pullback.fst f ι ≫ f) n ⟨pullback.fst f ι, rfl⟩).1 :=
      comp_schemeNsmul L n ⟨pullback.fst f ι, rfl⟩
    have h3 : baseChangePointToBase ι (idPoint (f := baseChangeStr ι f)) =
        reb (pullback.condition) ⟨pullback.fst f ι, rfl⟩ :=
      Subtype.ext (Category.id_comp _)
    rw [h1, h2, h3, nsmul_reb_coe]
  · rw [NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd]
    exact (L.baseChange ι).schemeNsmul_over n

theorem isPullback_schemeNsmul_baseChange (n : ℕ) :
    IsPullback ((L.baseChange ι).schemeNsmul n) (pullback.fst f ι) (pullback.fst f ι) (L.schemeNsmul n) := by
  rw [schemeNsmul_baseChange]
  have sq : IsPullback (pullback.snd f ι) (pullback.fst f ι) ι f := (IsPullback.of_hasPullback f ι).flip
  refine IsPullback.of_right (h₁₂ := pullback.snd f ι) (h₂₂ := f) (v₁₃ := ι) ?_ ?_ sq
  · rw [NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd]
    change IsPullback (pullback.snd f ι) (pullback.fst f ι) ι (L.schemeNsmul n ≫ f)
    rw [L.schemeNsmul_over]
    exact sq
  · exact NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst ι f f (nsmulOver L n)

end GoodReductionJacobian.RelativeGroupLaw.CH2

end

noncomputable section

namespace NSMULTransport

open GoodReductionJacobian.RelativeGroupLaw.CH2

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A} {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension)

def cst (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T : Scheme.{0}} (t : T ⟶ shBase A) : SchemeHomOver t F.gN :=
  ⟨t ≫ σ.1, (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) σ.2).trans (Category.comp_id t))⟩

theorem cst_comp (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T T' : Scheme.{0}} (t : T ⟶ shBase A) (t' : T' ⟶ shBase A)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (cst F σ t) = cst F σ t' :=
  Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe]; show ψ ≫ t ≫ σ.1 = t' ≫ σ.1; rw [← Category.assoc, hψ])

theorem comp_eq_cst (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T : Scheme.{0}} (t : T ⟶ shBase A) (ht : t ≫ 𝟙 _ = t) :
    GoodReductionJacobian.schemeHomOverComp t ht σ = cst F σ t :=
  Subtype.ext rfl

def transl (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) : F.Nfull ⟶ F.Nfull :=
  (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN)).1

theorem transl_over (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) : transl F σ ≫ F.gN = F.gN :=
  (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN)).2

theorem comp_transl (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) {T : Scheme.{0}} {t : T ⟶ shBase A} (z : SchemeHomOver t F.gN) :
    z.1 ≫ transl F σ = (F.LN.mul t z (cst F σ t)).1 := by
  have key := congrArg Subtype.val (F.LN.mul_natural F.gN t z.1 z.2 ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN))
  rw [GoodReductionJacobian.schemeHomOverComp_coe, cst_comp] at key
  have hz : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ : SchemeHomOver F.gN F.gN) = z :=
    Subtype.ext (Category.comp_id _)
  rw [hz] at key
  exact key

theorem transl_comp_transl (σ τ : SchemeHomOver (𝟙 (shBase A)) F.gN) :
    transl F σ ≫ transl F τ = transl F (F.LN.mul (𝟙 _) σ τ) := by
  have h1 : transl F σ ≫ transl F τ = (F.LN.mul F.gN (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN)) (cst F τ F.gN)).1 :=
    comp_transl F τ _
  have h2 : cst F (F.LN.mul (𝟙 _) σ τ) F.gN = F.LN.mul F.gN (cst F σ F.gN) (cst F τ F.gN) := by
    have := F.LN.mul_natural (𝟙 _) F.gN F.gN (Category.comp_id _) σ τ
    rw [comp_eq_cst F σ, comp_eq_cst F τ, comp_eq_cst F (F.LN.mul (𝟙 _) σ τ)] at this
    exact this
  rw [h1, transl, h2, F.LN.mul_assoc]

theorem transl_one : transl F (F.LN.one (𝟙 _)) = 𝟙 F.Nfull := by
  have h : cst F (F.LN.one (𝟙 _)) F.gN = F.LN.one F.gN := by
    have := GoodReductionJacobian.RelativeGroupLaw.one_natural F.LN (𝟙 _) F.gN F.gN (Category.comp_id _)
    rw [comp_eq_cst F (F.LN.one (𝟙 _))] at this
    exact this
  rw [transl, h, F.LN.mul_one]

scoped instance isIso_transl (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) : IsIso (transl F σ) :=
  ⟨⟨transl F (F.LN.inv (𝟙 _) σ), by rw [transl_comp_transl, F.LN.mul_inv_cancel, transl_one],
    by rw [transl_comp_transl, F.LN.inv_mul_cancel, transl_one]⟩⟩

theorem transl_comp_schemeNsmul (σ : SchemeHomOver (𝟙 (shBase A)) F.gN) (m : ℕ) :
    transl F σ ≫ F.LN.schemeNsmul m = F.LN.schemeNsmul m ≫ transl F (F.LN.nsmul (𝟙 _) m σ) := by
  have hc : F.LN.IsCommutative := F.commN

  have hl : transl F σ ≫ F.LN.schemeNsmul m =
      (F.LN.nsmul F.gN m (F.LN.mul F.gN ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩ (cst F σ F.gN))).1 :=
    comp_schemeNsmul F.LN m _

  have hr : F.LN.schemeNsmul m ≫ transl F (F.LN.nsmul (𝟙 _) m σ) =
      (F.LN.mul F.gN (F.LN.nsmul F.gN m ⟨𝟙 F.Nfull, Category.id_comp F.gN⟩) (cst F (F.LN.nsmul (𝟙 _) m σ) F.gN)).1 :=
    comp_transl F _ ⟨F.LN.schemeNsmul m, F.LN.schemeNsmul_over m⟩
  have hcst : cst F (F.LN.nsmul (𝟙 _) m σ) F.gN = F.LN.nsmul F.gN m (cst F σ F.gN) := by
    have := F.LN.nsmul_natural (𝟙 _) F.gN F.gN (Category.comp_id _) m σ
    rw [comp_eq_cst F σ, comp_eq_cst F (F.LN.nsmul (𝟙 _) m σ)] at this
    exact this
  rw [hl, hr, hcst, nsmul_mul F.LN hc]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in

theorem openImm_comp_schemeNsmul (m : ℕ) :
    F.openImm.1 ≫ F.LN.schemeNsmul m = (O.L.baseChange Λ.shStr).schemeNsmul m ≫ F.openImm.1 := by

  have hone : ∀ {T : Scheme.{0}} (s : T ⟶ shBase A),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).one s) F.openImm = F.LN.one s := by
    intro T s
    letI := F.LN.pointGroup s
    have h := F.openImm_mul s ((O.L.baseChange Λ.shStr).one s) ((O.L.baseChange Λ.shStr).one s)
    rw [(O.L.baseChange Λ.shStr).one_mul] at h

    have : NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).one s) F.openImm * 1 =
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).one s) F.openImm *
          NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).one s) F.openImm := by
      rw [_root_.mul_one]; exact h
    exact (mul_left_cancel this).symm
  have hpow : ∀ {T : Scheme.{0}} (s : T ⟶ shBase A) (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).nsmul s m x) F.openImm =
        F.LN.nsmul s m (NeronModelInfra.schemeHomOverComp x F.openImm) := by
    intro T s x
    induction m with
    | zero => rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]; exact hone s
    | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, F.openImm_mul, ih]
  have hl : F.openImm.1 ≫ F.LN.schemeNsmul m = (F.LN.nsmul _ m F.openImm).1 := comp_schemeNsmul F.LN m F.openImm
  have hr : (O.L.baseChange Λ.shStr).schemeNsmul m ≫ F.openImm.1 =
      (NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.shStr).nsmul _ m
        (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := RelativeGroupLaw.baseChangeStr Λ.shStr O.g))) F.openImm).1 := rfl
  have hid : NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.RelativeGroupLaw.idPoint (f := RelativeGroupLaw.baseChangeStr Λ.shStr O.g)) F.openImm = F.openImm :=
    Subtype.ext (Category.id_comp _)
  rw [hl, hr, hpow, hid]

end NSMULTransport
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul.NSMULTransport"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul.NSMULTransport"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) (m : ℕ) (hm : 0 < m) :
    LocallyQuasiFinite (F.LN.schemeNsmul m) ∧ QuasiCompact (F.LN.schemeNsmul m) ∧ Flat (F.LN.schemeNsmul m) := by
  classical
  obtain ⟨hDVR, -, -, -⟩ := ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
  haveI : IsDiscreteValuationRing ↥(shRing A) := hDVR
  have hN := F.hN
  haveI := hN.quasiCompact
  haveI := hN.separated
  haveI : IsOpenImmersion F.openImm.1 := F.openImm_isOpenImmersion
  obtain ⟨hlqfG, -, hflatG⟩ := locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange_shStr N₀ p hpN₀ A hA Λ hΛ O m hm
  obtain ⟨y, -, hcov⟩ := NeronExtension.exists_sections_forall_exists_mem_range_openImm_comp_mul N₀ p hpN₀ A hA Λ hΛ O F

  let 𝒰 : F.Nfull.OpenCover := Scheme.Cover.mkOfCovers (componentGroup O.width) (fun _ => pullback O.g Λ.shStr)
    (fun φ => F.openImm.1 ≫ NSMULTransport.transl F (y φ))
    (fun n => by obtain ⟨φ, x, hx⟩ := hcov n; exact ⟨φ, x, hx⟩)

  have hchart : ∀ φ, 𝒰.f φ ≫ F.LN.schemeNsmul m =
      (O.L.baseChange Λ.shStr).schemeNsmul m ≫ F.openImm.1 ≫ NSMULTransport.transl F (F.LN.nsmul (𝟙 _) m (y φ)) := by
    intro φ
    show (F.openImm.1 ≫ NSMULTransport.transl F (y φ)) ≫ F.LN.schemeNsmul m = _
    rw [Category.assoc, NSMULTransport.transl_comp_schemeNsmul, ← Category.assoc,
      NSMULTransport.openImm_comp_schemeNsmul, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · refine IsZariskiLocalAtSource.of_openCover (P := @LocallyQuasiFinite) 𝒰 (fun φ => ?_)
    rw [hchart]
    exact MorphismProperty.comp_mem _ _ _ hlqfG (MorphismProperty.comp_mem _ _ _ inferInstance inferInstance)
  · have : QuasiCompact (F.LN.schemeNsmul m ≫ F.gN) := by rw [F.LN.schemeNsmul_over]; infer_instance
    exact QuasiCompact.of_comp _ F.gN
  · refine IsZariskiLocalAtSource.of_openCover (P := @Flat) 𝒰 (fun φ => ?_)
    rw [hchart]
    exact MorphismProperty.comp_mem _ _ _ hflatG (MorphismProperty.comp_mem _ _ _ inferInstance inferInstance)

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_locallyQuasiFinite_quasiCompact_flat_schemeNsmul (solution)
