-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.multidegree_mem_range_intersectionAlpha_of_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f8dfc40a-c898-5d4d-83a8-a36ed4f45f9d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_ComponentGroup
import Theorems.Thm_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization

open MazurRapoportAppendix

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackage ModularPolynomialData modularFunctionFieldFull arithmeticGalois modularFunctionFieldBar JZero crossingCoord crossingCoord_apply inertiaInvariants modularFunctionFieldC characterLattice mem_characterLattice gramMap_apply componentGroup componentGroupProj PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence nodePairsOfPlaces fst_mem_of_mem_nodePairsOfPlaces nodeEquivOfPlaces coe_nodeEquivOfPlaces_symm_apply widthOfPlaces widthOfPlaces_apply ssPlaces arithFrobC DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqResolvedTable exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed deg_eq_one_modularFunctionFieldBar ssPlaces_nonempty"
p2m_open "ModularCurve"

namespace RCore

variable {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℕ)

abbrev cc (s : ι) : Module.Dual ℤ (characterLattice ι) :=
  (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype

@[scoped simp] theorem cc_apply (s : ι) (γ : characterLattice ι) : cc s γ = γ.1 s := rfl

theorem proj_smul_cc_eq (s s' : ι) :
    componentGroupProj w ((w s : ℤ) • cc s) = componentGroupProj w ((w s' : ℤ) • cc s') := by
  rw [← sub_eq_zero, ← map_sub]
  change Submodule.Quotient.mk _ = (0 : componentGroup w)
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨⟨Pi.single s 1 - Pi.single s' 1, ?_⟩, ?_⟩
  · rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]
  · apply LinearMap.ext
    intro γ
    rw [gramMap_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, cc_apply, smul_eq_mul, Pi.sub_apply]
    by_cases hss : s = s'
    · subst hss; simp
    · rw [Finset.sum_eq_add_of_mem s s' (Finset.mem_univ _) (Finset.mem_univ _) hss]
      · simp [hss, Ne.symm hss]; ring
      · intro x _ hx
        simp [hx.1, hx.2]

def Q (s₀ : ι) : X0MqComponents w → Module.Dual ℤ (characterLattice ι)
  | Sum.inl j => if j = 1 then (w s₀ : ℤ) • cc s₀ else 0
  | Sum.inr σ => ((σ.2 : ℤ) + 1) • cc σ.1

def pathLin (s₀ : ι) (a : X0MqComponents w → ℤ) : Module.Dual ℤ (characterLattice ι) :=
  ∑ x, a x • Q w s₀ x

theorem pathLin_eq (s₀ : ι) (a : X0MqComponents w → ℤ) :
    pathLin w s₀ a =
      (((∑ s : ι, (∑ k : Fin (w s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) •
            (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)) +
          ((w s₀ : ℤ) * a (Sum.inl 1)) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ)).comp
        (characterLattice ι).subtype) := by
  apply LinearMap.ext
  intro γ
  have hL : pathLin w s₀ a γ = a (Sum.inl 1) * ((w s₀ : ℤ) * γ.1 s₀) +
      ∑ s, ∑ k : Fin (w s - 1), a (Sum.inr ⟨s, k⟩) * (((k : ℤ) + 1) * γ.1 s) := by
    simp only [pathLin, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Fintype.sum_sum_type, Fin.sum_univ_two]
    simp only [Q, Fin.isValue, zero_ne_one, ↓reduceIte, LinearMap.zero_apply, mul_zero, zero_add,
      LinearMap.smul_apply, cc_apply, smul_eq_mul]
    congr 1
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  have hR : ((((∑ s : ι, (∑ k : Fin (w s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) •
            (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)) +
          ((w s₀ : ℤ) * a (Sum.inl 1)) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ)).comp
        (characterLattice ι).subtype) γ) =
      (∑ s, (∑ k : Fin (w s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) * γ.1 s) +
        ((w s₀ : ℤ) * a (Sum.inl 1)) * γ.1 s₀ := by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, Submodule.subtype_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [hL, hR, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  · ring

theorem pathLin_single (s₀ : ι) (x : X0MqComponents w) (c : ℤ) :
    pathLin w s₀ (Pi.single x c) = c • Q w s₀ x := by
  simp only [pathLin]
  rw [Finset.sum_eq_single x (fun y _ hy => by rw [Pi.single_eq_of_ne hy, zero_smul]) (by simp)]
  rw [Pi.single_eq_same]

theorem pathLin_sum_single (s₀ : ι) {m : ℕ} (v : Fin m → X0MqComponents w) (c : Fin m → ℤ) :
    pathLin w s₀ (⇑(∑ j, Finsupp.single (v j) (c j))) = ∑ j, c j • Q w s₀ (v j) := by
  have hlin : ∀ a b : X0MqComponents w → ℤ, pathLin w s₀ (a + b) = pathLin w s₀ a + pathLin w s₀ b := by
    intro a b
    simp only [pathLin, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have h0 : pathLin w s₀ 0 = 0 := by simp [pathLin]

  let Φ : (X0MqComponents w → ℤ) →+ Module.Dual ℤ (characterLattice ι) :=
    { toFun := pathLin w s₀, map_zero' := h0, map_add' := hlin }
  have : pathLin w s₀ (⇑(∑ j, Finsupp.single (v j) (c j))) = Φ (⇑(∑ j, Finsupp.single (v j) (c j))) := rfl
  rw [this, Finsupp.coe_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change pathLin w s₀ _ = _
  rw [Finsupp.single_eq_pi_single, pathLin_single]

theorem proj_Q_chainPos (s₀ s : ι) (d : ℕ) (hd : d ≤ w s) :
    componentGroupProj w (Q w s₀ (DRResolvedModelPackage.chainPos w s d)) = (d : ℤ) • componentGroupProj w (cc s) := by
  by_cases h0 : d = 0
  · subst h0
    simp [DRResolvedModelPackage.chainPos, Q]
  · by_cases hlt : d < w s
    · have : DRResolvedModelPackage.chainPos w s d = Sum.inr ⟨s, ⟨d - 1, by omega⟩⟩ := by
        simp [DRResolvedModelPackage.chainPos, h0, hlt]
      rw [this]
      simp only [Q, map_zsmul]
      congr 1
      push_cast
      omega
    · have hd' : d = w s := by omega
      have : DRResolvedModelPackage.chainPos w s d = Sum.inl 1 := by
        simp [DRResolvedModelPackage.chainPos, h0, hlt]
      rw [this]
      simp only [Q, ↓reduceIte]
      rw [proj_smul_cc_eq w s₀ s, map_zsmul, hd']

end RCore
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.ModularCurve.RCore"

namespace RCore

variable {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℕ)

theorem coe_sum_single_mem_degreeZeroSublattice {m : ℕ} (v : Fin m → X0MqComponents w) (c : Fin m → ℤ)
    (hc : ∑ j, c j = 0) :
    (⇑(∑ j, Finsupp.single (v j) (c j)) : X0MqComponents w → ℤ) ∈ degreeZeroSublattice (x0MqResolvedTable w) := by
  rw [mem_degreeZeroSublattice]
  simp only [x0MqResolvedTable, Nat.cast_one, mul_one, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm]
  simpa [Finset.sum_ite_eq'] using hc

omit [DecidableEq ι] in

theorem mem_range_of_map_class_eq_zero (t : SpecialFibreComponentTable (X0MqComponents w))
    {G : Type*} [AddGroup G] (ψ : AppendixComponentGroup t →+ G) (hψ : Function.Injective ψ)
    (a : X0MqComponents w → ℤ) (ha : a ∈ degreeZeroSublattice t) (h0 : ψ (appendixComponentGroupClass t ⟨a, ha⟩) = 0) :
    a ∈ (intersectionAlpha t).range := by
  have h0' : appendixComponentGroupClass t ⟨a, ha⟩ = 0 := hψ (by rw [h0, map_zero])
  have hmem : (⟨a, ha⟩ : ↥(degreeZeroSublattice t)) ∈ imageOfIntersectionAlpha t := by
    rwa [appendixComponentGroupClass, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h0'
  obtain ⟨c, hc⟩ := mem_imageOfIntersectionAlpha.mp hmem
  exact ⟨c, hc⟩

def lawTerm (s₀ : ι) (c : ℤ) (isFst isSnd : Prop) [Decidable isFst] [Decidable isSnd] (nd : ι) (dp : ℕ) :
    Module.Dual ℤ (characterLattice ι) :=
  (if isFst ∨ isSnd then 0 else (c * (dp : ℤ)) • cc nd) + (if isSnd then c • ((w s₀ : ℤ) • cc s₀) else 0)

theorem proj_smul_Q_dict (s₀ : ι) (c : ℤ) (isFst isSnd : Prop) [Decidable isFst] [Decidable isSnd]
    (hexcl : ¬ (isFst ∧ isSnd)) (nd : ι) (dp : ℕ) (hdp : ¬ isFst → ¬ isSnd → dp ≤ w nd) (swap : Bool)
    (x : X0MqComponents w)
    (hx : x = if isFst then (if swap then Sum.inl 1 else Sum.inl 0)
        else if isSnd then (if swap then Sum.inl 0 else Sum.inl 1)
        else DRResolvedModelPackage.chainPos w nd (if swap then w nd - dp else dp)) :
    componentGroupProj w (c • Q w s₀ x) =
      if swap then c • componentGroupProj w ((w s₀ : ℤ) • cc s₀) - componentGroupProj w (lawTerm w s₀ c isFst isSnd nd dp)
      else componentGroupProj w (lawTerm w s₀ c isFst isSnd nd dp) := by
  have hW : (w nd : ℤ) • componentGroupProj w (cc nd) = (w s₀ : ℤ) • componentGroupProj w (cc s₀) := by
    have := proj_smul_cc_eq w nd s₀
    simpa only [map_smul] using this
  by_cases hF : isFst
  · have hS : ¬ isSnd := fun h => hexcl ⟨hF, h⟩
    subst hx
    cases swap <;> simp [hF, hS, Q, lawTerm]
  · by_cases hS : isSnd
    · subst hx
      cases swap <;> simp [hF, hS, Q, lawTerm]
    · have hd := hdp hF hS
      subst hx
      cases swap
      · simp only [hF, hS, Bool.false_eq_true, ↓reduceIte, lawTerm, or_self, add_zero, map_smul]
        rw [proj_Q_chainPos w s₀ nd dp hd]
        module
      · simp only [hF, hS, ↓reduceIte, lawTerm, or_self, add_zero, map_smul]
        rw [proj_Q_chainPos w s₀ nd (w nd - dp) (Nat.sub_le _ _), Nat.cast_sub hd, sub_smul, hW]
        module

theorem coe_sum_single_mem_range_intersectionAlpha (hw : ∀ s, 0 < w s) (s₀ : ι) {m : ℕ} (c : Fin m → ℤ)
    (hc : ∑ j, c j = 0)
    (isFst isSnd : Fin m → Prop) [DecidablePred isFst] [DecidablePred isSnd]
    (hexcl : ∀ j, ¬ (isFst j ∧ isSnd j))
    (nd : Fin m → ι) (dp : Fin m → ℕ) (hdp : ∀ j, ¬ isFst j → ¬ isSnd j → dp j ≤ w (nd j))
    (swap : Bool) (v : Fin m → X0MqComponents w)
    (hv : ∀ j, v j = if isFst j then (if swap then Sum.inl 1 else Sum.inl 0)
        else if isSnd j then (if swap then Sum.inl 0 else Sum.inl 1)
        else DRResolvedModelPackage.chainPos w (nd j) (if swap then w (nd j) - dp j else dp j))
    (hlaw : componentGroupProj w
        ((∑ j, if isFst j ∨ isSnd j then 0 else (c j * (dp j : ℤ)) • cc (nd j)) +
          (∑ j, if isSnd j then c j else 0) • ((w s₀ : ℤ) • cc s₀)) = 0) :
    (⇑(∑ j, Finsupp.single (v j) (c j)) : X0MqComponents w → ℤ) ∈
      (intersectionAlpha (x0MqResolvedTable w)).range := by
  have ha := coe_sum_single_mem_degreeZeroSublattice w v c hc
  obtain ⟨ψ, hψ, -⟩ := exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj w hw s₀
  refine mem_range_of_map_class_eq_zero w _ ψ.toAddMonoidHom ψ.injective _ ha ?_
  rw [AddEquiv.coe_toAddMonoidHom, hψ _ ha, ← pathLin_eq, pathLin_sum_single, map_sum]
  rw [Finset.sum_congr rfl fun j _ =>
    proj_smul_Q_dict w s₀ (c j) (isFst j) (isSnd j) (hexcl j) (nd j) (dp j) (hdp j) swap (v j) (hv j)]

  have hL : (∑ j, lawTerm w s₀ (c j) (isFst j) (isSnd j) (nd j) (dp j)) =
      (∑ j, if isFst j ∨ isSnd j then 0 else (c j * (dp j : ℤ)) • cc (nd j)) +
        (∑ j, if isSnd j then c j else 0) • ((w s₀ : ℤ) • cc s₀) := by
    simp only [lawTerm, Finset.sum_add_distrib, Finset.sum_smul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  have hPL : (∑ j, componentGroupProj w (lawTerm w s₀ (c j) (isFst j) (isSnd j) (nd j) (dp j))) = 0 := by
    rw [← map_sum, hL, hlaw]
  cases swap
  · simpa using hPL
  · simp only [↓reduceIte, Finset.sum_sub_distrib, hPL, sub_zero]
    rw [← Finset.sum_smul, hc, zero_smul]

end RCore
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.ModularCurve.RCore"

namespace RCore

def latticeComap {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (τ : ι₁ ≃ ι₂) :
    characterLattice ι₂ →ₗ[ℤ] characterLattice ι₁ :=
  ((LinearMap.funLeft ℤ ℤ τ).comp (characterLattice ι₂).subtype).codRestrict (characterLattice ι₁) (by
    intro γ
    rw [mem_characterLattice]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.funLeft_apply]
    rw [Equiv.sum_comp τ (fun y => γ.1 y)]
    exact mem_characterLattice.mp γ.2)

@[scoped simp] theorem latticeComap_apply_coe {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (τ : ι₁ ≃ ι₂)
    (γ : characterLattice ι₂) (x : ι₁) : (latticeComap τ γ).1 x = γ.1 (τ x) := rfl

theorem cc_comp_latticeComap {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (τ : ι₁ ≃ ι₂) (s : ι₁) :
    (cc s).comp (latticeComap τ) = cc (τ s) := by
  apply LinearMap.ext; intro γ; rfl

theorem proj_comp_latticeComap_eq_zero {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (e₁ : ι₁ → ℕ) (e₂ : ι₂ → ℕ) (τ : ι₁ ≃ ι₂) (hτ : ∀ x, e₂ (τ x) = e₁ x)
    (F : Module.Dual ℤ (characterLattice ι₁)) (hF : componentGroupProj e₁ F = 0) :
    componentGroupProj e₂ (F.comp (latticeComap τ)) = 0 := by
  change Submodule.Quotient.mk _ = (0 : componentGroup e₁) at hF
  change Submodule.Quotient.mk _ = (0 : componentGroup e₂)
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hF ⊢
  obtain ⟨D, rfl⟩ := hF
  refine ⟨latticeComap τ.symm D, ?_⟩
  apply LinearMap.ext
  intro γ
  rw [gramMap_apply, LinearMap.comp_apply, gramMap_apply]
  rw [← Equiv.sum_comp τ]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [hτ]

end RCore
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.ModularCurve.RCore"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.ModularCurve.RCore P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.ModularCurve"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (e : Place k (modularFunctionFieldC k 1) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) → ℕ)
    (comp : ↥(inertiaInvariants A (1 * p)) →+ componentGroup (widthOfPlaces (arithFrobC p k 1) W e))
    (hlaw : P.DepthCompLaw (arithFrobC p k 1) W e depth comp)

    (O : Type) [CommRing O] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (swap : Bool)

    (x : ↥(inertiaInvariants A (1 * p))) (hx : comp x = 0)
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
    (hD₀ : Pic0.mk D₀ = (x : JZero (1 * p)))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V' = V') ∧
        (P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W))
    (m : ℕ) (pos neg : Fin m → ℕ)
    (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support))
    (hcoef : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
      (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
        (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))

    (hdepth : ∀ j, ¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        ¬ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        ∀ hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ∈ W,
          depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ≤
            e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))))

    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hdict : ∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ∈ W then
           DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨_, hw⟩)
             (if swap then 𝔛reg.width (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
         else Sum.inl 0)) :
    (fun w : X0MqComponents 𝔛reg.width => (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) w) ∈
      (MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)).range := by
  classical

  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
  have hdeg1 : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), V.deg = 1 :=
    ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * p)

  let Fpl : Fin m → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) := fun j => (idx j : _)
  let c : Fin m → ℤ := fun j => (pos j : ℤ) - (neg j : ℤ)
  have hcD : ∀ j, c j = (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (Fpl j) := fun j => hcoef j
  have hreidx : ∀ {β : Type} [AddCommMonoid β]
      (f : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) → β),
      ∑ V ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support, f V = ∑ j, f (Fpl j) := by
    intro β _ f
    rw [← Finset.sum_coe_sort, ← Equiv.sum_comp idx]

  have hc0 : ∑ j, c j = 0 := by
    have h := D₀.2
    rw [Divisor.mem_degZero, Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at h
    simp only [AddMonoidHom.coe_mulRight, hdeg1, Nat.cast_one, mul_one] at h
    rw [hreidx] at h
    simpa only [hcD] using h

  have hp1 : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  have hexcl : ∀ j, ¬ (P.IsStrictFst (Fpl j) ∧ P.IsStrictSnd (Fpl j)) := by
    rintro j ⟨h1, h2⟩
    exact h1.2 (by rw [h1.1]; exact h2.1.symm)
  have hstrictW : ∀ j, (P.IsStrictFst (Fpl j) ∨ P.IsStrictSnd (Fpl j)) → P.reduceFst (Fpl j) ∉ W := by
    intro j hj hw
    exact (P.isStrictFst_or_isStrictSnd_iff (Fpl j)).mp hj
      (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k 1 hp1 data hKr _
        ((hW _).mp hw))
  have hnodeW : ∀ j, ¬ P.IsStrictFst (Fpl j) → ¬ P.IsStrictSnd (Fpl j) → P.reduceFst (Fpl j) ∈ W := by
    intro j h1 h2
    rcases (hadm (Fpl j) (idx j).2).2 with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h

  obtain ⟨w₀, hw₀'⟩ := ModularCurve.ssPlaces_nonempty p 1 hp1 k
  have hw₀ : w₀ ∈ W := (hW w₀).mpr hw₀'
  let nd : Fin m → 𝔛reg.node := fun j =>
    if h : P.reduceFst (Fpl j) ∈ W then σN ⟨_, h⟩ else σN ⟨w₀, hw₀⟩
  let dp : Fin m → ℕ := fun j => depth (Fpl j)
  have hnd : ∀ j (h : P.reduceFst (Fpl j) ∈ W), nd j = σN ⟨_, h⟩ := fun j h => dif_pos h
  have hdp : ∀ j, ¬ P.IsStrictFst (Fpl j) → ¬ P.IsStrictSnd (Fpl j) → dp j ≤ 𝔛reg.width (nd j) := by
    intro j h1 h2
    rw [hnd j (hnodeW j h1 h2), hσN]
    exact hdepth j h1 h2 (hnodeW j h1 h2)

  have hv : ∀ j, v j = if P.IsStrictFst (Fpl j) then (if swap then Sum.inl 1 else Sum.inl 0)
      else if P.IsStrictSnd (Fpl j) then (if swap then Sum.inl 0 else Sum.inl 1)
      else DRResolvedModelPackage.chainPos 𝔛reg.width (nd j) (if swap then 𝔛reg.width (nd j) - dp j else dp j) := by
    intro j
    rw [hdict j]
    by_cases h1 : P.IsStrictFst (Fpl j)
    · simp [Fpl, h1]
    · by_cases h2 : P.IsStrictSnd (Fpl j)
      · simp [Fpl, h1, h2]
      · have hw := hnodeW j h1 h2
        simp only [Fpl] at h1 h2 hw
        simp only [h1, h2, ↓reduceIte, hw, ↓reduceDIte, Fpl, dp]
        rw [hnd j hw]

  let g := arithFrobC p k 1
  let s₀ : ↥(nodePairsOfPlaces g W) := nodeEquivOfPlaces g W ⟨w₀, hw₀⟩
  have hH : Pic0.mk D₀ ∈ inertiaInvariants A (1 * p) := by rw [hD₀]; exact x.2
  have hlaw0 := hlaw D₀ hH hadm s₀.1 s₀.2
  have hx' : comp ⟨Pic0.mk D₀, hH⟩ = 0 := by
    have : (⟨Pic0.mk D₀, hH⟩ : ↥(inertiaInvariants A (1 * p))) = x := Subtype.ext hD₀
    rw [this, hx]
  have hzero := (hx'.symm.trans hlaw0).symm

  let τ : ↥(nodePairsOfPlaces g W) ≃ 𝔛reg.node := (nodeEquivOfPlaces g W).symm.trans σN
  have hτ : ∀ s, 𝔛reg.width (τ s) = widthOfPlaces g W e s := fun s => by
    simp only [τ, Equiv.trans_apply, widthOfPlaces_apply]
    rw [hσN]
    rfl
  have hB := RCore.proj_comp_latticeComap_eq_zero (widthOfPlaces g W e) 𝔛reg.width τ hτ _ hzero

  have hsnd : Divisor.degree (P.sndDiv (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))) =
      ∑ j, if P.IsStrictSnd (Fpl j) then c j else 0 := by
    have hsub : ((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).filter P.IsStrictSnd).support ⊆
        (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support := by
      rw [Finsupp.support_filter]; exact Finset.filter_subset _ _
    change Divisor.degree ((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).filter P.IsStrictSnd) = _
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset _ hsub _ (fun _ _ => by simp)]
    simp only [AddMonoidHom.coe_mulRight, hdeg1, Nat.cast_one, mul_one, Finsupp.filter_apply]
    rw [hreidx]
    exact Finset.sum_congr rfl fun j _ => by simp only [hcD]

  have hdepthDiv : ∀ w' : Place k (modularFunctionFieldC k 1),
      P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) w' =
        ∑ j, if P.reduceFst (Fpl j) = w' then c j * (dp j : ℤ) else 0 := by
    intro w'
    change ((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).sum
      fun V n => Finsupp.single (P.reduceFst V) (n * (depth V : ℤ))) w' = _
    rw [Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [Finsupp.single_apply]
    rw [hreidx]
    exact Finset.sum_congr rfl fun j _ => by simp only [hcD]; rfl
  have hinner : ∀ (γ : characterLattice 𝔛reg.node) (j : Fin m),
      (∑ s : ↥(nodePairsOfPlaces g W), (if P.reduceFst (Fpl j) = s.1.1 then c j * (dp j : ℤ) else 0) * γ.1 (τ s)) =
        if P.IsStrictFst (Fpl j) ∨ P.IsStrictSnd (Fpl j) then 0 else c j * (dp j : ℤ) * γ.1 (nd j) := by
    intro γ j
    by_cases hj : P.IsStrictFst (Fpl j) ∨ P.IsStrictSnd (Fpl j)
    · rw [if_pos hj]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg, zero_mul]
      intro h
      exact hstrictW j hj (h ▸ fst_mem_of_mem_nodePairsOfPlaces s.2)
    · rw [if_neg hj]
      have hw : P.reduceFst (Fpl j) ∈ W := by
        push Not at hj
        exact hnodeW j hj.1 hj.2
      let sj : ↥(nodePairsOfPlaces g W) := nodeEquivOfPlaces g W ⟨_, hw⟩
      rw [Finset.sum_eq_single sj]
      · have h1 : P.reduceFst (Fpl j) = sj.1.1 := rfl
        rw [if_pos h1]
        have h2 : τ sj = nd j := by
          rw [hnd j hw]
          simp only [τ, sj, Equiv.trans_apply, Equiv.symm_apply_apply]
        rw [h2]
      · intro s _ hs
        rw [if_neg, zero_mul]
        intro h
        apply hs
        apply (nodeEquivOfPlaces g W).symm.injective
        apply Subtype.ext
        simp only [coe_nodeEquivOfPlaces_symm_apply]
        rw [← h]
        rfl
      · intro h; exact absurd (Finset.mem_univ _) h
  have hdepthDual : ∀ γ : characterLattice 𝔛reg.node,
      P.depthDual g W depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
          (RCore.latticeComap τ γ) =
        ∑ j, if P.IsStrictFst (Fpl j) ∨ P.IsStrictSnd (Fpl j) then 0 else c j * (dp j : ℤ) * γ.1 (nd j) := by
    intro γ
    change (∑ s : ↥(nodePairsOfPlaces g W),
      P.depthDiv depth (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) s.1.1 •
        crossingCoord s) (RCore.latticeComap τ γ) = _
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, crossingCoord_apply, smul_eq_mul,
      RCore.latticeComap_apply_coe, hdepthDiv, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hinner γ j
  refine RCore.coe_sum_single_mem_range_intersectionAlpha 𝔛reg.width (fun s => 𝔛reg.one_le_width s) (τ s₀) c hc0
    (fun j => P.IsStrictFst (Fpl j)) (fun j => P.IsStrictSnd (Fpl j)) hexcl nd dp hdp swap v hv ?_
  refine (congrArg (componentGroupProj 𝔛reg.width) ?_).trans hB
  apply LinearMap.ext
  intro γ
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hdepthDual γ]
  simp only [hsnd]
  simp only [LinearMap.coe_sum, Finset.sum_apply, smul_eq_mul,
    RCore.latticeComap_apply_coe, crossingCoord_apply, hτ s₀, widthOfPlaces_apply]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · simp [mul_assoc]

end S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero (solution)
