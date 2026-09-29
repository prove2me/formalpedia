-- Prove2me | solution 1 for ModularCurve.exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a0e700b1-e2ae-5231-8e1b-da65f29d9db3

import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_WeierstrassCurve_MapPoint
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_frobeniusSemilinear_torsionModel_ofJ_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve~CycSub P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve"
open scoped Pointwise

universe u

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace CyclicModuli
p2m_open "ModularCurve~CycSub"

section Gen

open AddSubgroup

variable {A : Type u} [AddCommGroup A]

private theorem exists_nsmul_coprime_of_mem_zmultiples {N : ℕ} [NeZero N] {T T' : A}
    (hT : addOrderOf T = N) (hT' : addOrderOf T' = N)
    (hmem : T' ∈ zmultiples T) :
    ∃ k : ℕ, k.Coprime N ∧ T' = k • T := by
  obtain ⟨m, hm⟩ := mem_zmultiples_iff.mp hmem
  have hN0 : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have hNT : (N : ℤ) • T = 0 := by
    have h0 : N • T = 0 := hT ▸ addOrderOf_nsmul_eq_zero T
    simpa [natCast_zsmul] using h0
  set k : ℕ := (m % (N : ℤ)).toNat with hkdef
  have hmod : (m % (N : ℤ)) = (k : ℤ) :=
    (Int.toNat_of_nonneg (Int.emod_nonneg m hN0)).symm
  have hsplit : m • T = (k : ℤ) • T := by
    conv_lhs => rw [← Int.mul_ediv_add_emod m (N : ℤ)]
    rw [add_zsmul, mul_comm, mul_zsmul, hNT, smul_zero, zero_add, hmod]
  have hTT : T' = k • T := by
    rw [← hm, hsplit, natCast_zsmul]
  have hfin : IsOfFinAddOrder T :=
    addOrderOf_pos_iff.mp (hT ▸ Nat.pos_of_ne_zero (NeZero.ne N))
  have hordk : addOrderOf (k • T) = N := hTT ▸ hT'
  rw [hfin.addOrderOf_nsmul, hT] at hordk
  rcases Nat.div_eq_self.mp hordk with h0 | h1
  · exact absurd h0 (NeZero.ne N)
  · exact ⟨k, Nat.coprime_comm.mp h1, hTT⟩

private theorem exists_generator_of_isAddCyclic_card (H : AddSubgroup A) (N : ℕ)
    (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    ∃ g : A, addOrderOf g = N ∧ H = zmultiples g := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h2 : addOrderOf g = Nat.card H := addOrderOf_eq_card_of_forall_mem_zmultiples hg
  refine ⟨(g : A), ?_, ?_⟩
  · exact (addOrderOf_injective H.subtype (AddSubgroup.subtype_injective H) g).trans
      (h2.trans hcard)
  · ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
      exact mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zmultiples_iff.mp hx
      rw [← hk]
      exact zsmul_mem g.2 k

end Gen

section Moduli

variable {N : ℕ} [NeZero N] {K : Type u} [Field K] [DecidableEq K]

private def pairOf (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (T : E₀.toAffine.Point)
    (hT : addOrderOf T = N) : Gamma0Pair N K :=
  ⟨E₀, ‹_›, T, hT⟩

private def moduliOf (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (T : E₀.toAffine.Point)
    (hT : addOrderOf T = N) : ModuliPoint N K :=
  Quot.mk _ (pairOf E₀ T hT)

omit [NeZero N] in
@[scoped simp] private theorem j_moduliOf (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (T : E₀.toAffine.Point)
    (hT : addOrderOf T = N) : ModuliPoint.j (moduliOf E₀ T hT) = E₀.j :=
  rfl

omit [DecidableEq K] in

private theorem heq_vcInvFun_one (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    HEq (WeierstrassCurve.Affine.Point.vcInvFun 1 W.toAffine P) P := by
  have h1 : ((1 : WeierstrassCurve.VariableChange K) • W.toAffine).toAffine = W.toAffine := by
    rw [one_smul]
  cases P with
  | zero =>
      exact ModularCurve.Point.heq_zero h1
  | some x y hns =>
      have hx : WeierstrassCurve.Affine.vcXInv (1 : WeierstrassCurve.VariableChange K) x = x := by
        show ((((1 : Kˣ)⁻¹ : Kˣ)) : K) ^ 2 * (x - 0) = x
        norm_num
      have hy : WeierstrassCurve.Affine.vcYInv (1 : WeierstrassCurve.VariableChange K) x y = y := by
        show ((((1 : Kˣ)⁻¹ : Kˣ)) : K) ^ 3 * (y - 0 - 0 * (x - 0)) = y
        norm_num
      exact ModularCurve.Point.heq_some h1 hx hy

private theorem moduliOf_eq_of_zmultiples_eq (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    {T T' : E₀.toAffine.Point} (hT : addOrderOf T = N) (hT' : addOrderOf T' = N)
    (hz : AddSubgroup.zmultiples T = AddSubgroup.zmultiples T') :
    moduliOf E₀ T hT = moduliOf E₀ T' hT' := by
  have hmem : T' ∈ AddSubgroup.zmultiples T := hz ▸ AddSubgroup.mem_zmultiples T'
  obtain ⟨k, hk, hTT⟩ := exists_nsmul_coprime_of_mem_zmultiples hT hT' hmem
  have h1 : ((1 : WeierstrassCurve.VariableChange K) • E₀.toAffine).toAffine = E₀.toAffine := by
    rw [one_smul]
  refine Quot.sound ⟨1, ⟨one_smul _ _, k, hk, ?_⟩⟩
  exact (heq_of_eq hTT).trans
    ((ModularCurve.Point.heq_nsmul h1 k (heq_vcInvFun_one E₀ T)).symm)

private noncomputable def orbitMap (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    ModuliPoint N K :=
  moduliOf E₀ (exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2).choose
    (exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2).choose_spec.1

omit [NeZero N] in

private theorem j_orbitMap (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    ModuliPoint.j (orbitMap E₀ H) = E₀.j :=
  rfl

private theorem orbitMap_eq_moduliOf (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
    {T : E₀.toAffine.Point} (hT : addOrderOf T = N)
    (hHT : H.1 = AddSubgroup.zmultiples T) :
    orbitMap E₀ H = moduliOf E₀ T hT :=
  moduliOf_eq_of_zmultiples_eq E₀ _ hT
    (((exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2).choose_spec.2.symm.trans hHT))

end Moduli

section Coords

variable {K : Type u} [Field K]

private theorem vcXInv_inv (γ : WeierstrassCurve.VariableChange K) (x : K) :
    WeierstrassCurve.Affine.vcXInv γ⁻¹ x = WeierstrassCurve.Affine.vcX γ x := by
  simp only [WeierstrassCurve.Affine.vcXInv, WeierstrassCurve.Affine.vcX,
    WeierstrassCurve.VariableChange.inv_def]
  simp only [inv_inv, Units.val_inv_eq_inv_val]
  field_simp
  ring

private theorem vcYInv_inv (γ : WeierstrassCurve.VariableChange K) (x y : K) :
    WeierstrassCurve.Affine.vcYInv γ⁻¹ x y = WeierstrassCurve.Affine.vcY γ x y := by
  simp only [WeierstrassCurve.Affine.vcYInv, WeierstrassCurve.Affine.vcY,
    WeierstrassCurve.VariableChange.inv_def]
  simp only [inv_inv, Units.val_inv_eq_inv_val]
  field_simp
  ring

private theorem vcXInv_mul (γ₁ γ₂ : WeierstrassCurve.VariableChange K) (x : K) :
    WeierstrassCurve.Affine.vcXInv (γ₂ * γ₁) x
      = WeierstrassCurve.Affine.vcXInv γ₂ (WeierstrassCurve.Affine.vcXInv γ₁ x) := by
  simp only [WeierstrassCurve.Affine.vcXInv, WeierstrassCurve.VariableChange.mul_def]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
  ring

private theorem vcYInv_mul (γ₁ γ₂ : WeierstrassCurve.VariableChange K) (x y : K) :
    WeierstrassCurve.Affine.vcYInv (γ₂ * γ₁) x y
      = WeierstrassCurve.Affine.vcYInv γ₂ (WeierstrassCurve.Affine.vcXInv γ₁ x)
          (WeierstrassCurve.Affine.vcYInv γ₁ x y) := by
  simp only [WeierstrassCurve.Affine.vcYInv, WeierstrassCurve.Affine.vcXInv,
    WeierstrassCurve.VariableChange.mul_def]
  simp only [mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
  ring

end Coords

section HEqLaws

variable {K : Type u} [Field K] [DecidableEq K]

private noncomputable def vcAddEquiv (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    W.toAffine.Point ≃+ (C • W).toAffine.Point :=
  AddEquiv.mk' (WeierstrassCurve.Affine.Point.variableChangeEquiv C W.toAffine).symm
    (WeierstrassCurve.Affine.Point.vcInvFun_add C W.toAffine)

@[scoped simp] private theorem vcAddEquiv_apply (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K)
    (P : W.toAffine.Point) :
    vcAddEquiv C W P = WeierstrassCurve.Affine.Point.vcInvFun C W.toAffine P := rfl

private def pointAddEquivOfEq {W V : WeierstrassCurve K} (h : W = V) :
    W.toAffine.Point ≃+ V.toAffine.Point := by
  subst h; exact AddEquiv.refl _

@[scoped simp] private theorem pointAddEquivOfEq_rfl (W : WeierstrassCurve K) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ := rfl

omit [DecidableEq K] in

private theorem heq_vcInvFun_inv (γ : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K)
    (y : (γ • W).toAffine.Point) :
    HEq (WeierstrassCurve.Affine.Point.vcInvFun γ⁻¹ (γ • W).toAffine y)
      (WeierstrassCurve.Affine.Point.vcFun γ W.toAffine y) := by
  have h1 : (γ⁻¹ • (γ • W).toAffine).toAffine = W.toAffine := by
    rw [inv_smul_smul]
  cases y with
  | zero => exact ModularCurve.Point.heq_zero h1
  | some x y hns => exact ModularCurve.Point.heq_some h1 (vcXInv_inv γ x) (vcYInv_inv γ x y)

omit [DecidableEq K] in

private theorem heq_vcInvFun_mul (γ₁ γ₂ : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K)
    (P : W.toAffine.Point) :
    HEq (WeierstrassCurve.Affine.Point.vcInvFun (γ₂ * γ₁) W.toAffine P)
      (WeierstrassCurve.Affine.Point.vcInvFun γ₂ (γ₁ • W).toAffine
        (WeierstrassCurve.Affine.Point.vcInvFun γ₁ W.toAffine P)) := by
  have h1 : ((γ₂ * γ₁) • W.toAffine).toAffine = (γ₂ • (γ₁ • W).toAffine).toAffine := by
    rw [mul_smul]
  cases P with
  | zero => exact ModularCurve.Point.heq_zero h1.symm |>.symm
  | some x y hns =>
      exact (ModularCurve.Point.heq_some h1.symm
        (vcXInv_mul γ₁ γ₂ x).symm (vcYInv_mul γ₁ γ₂ x y).symm).symm

private theorem heq_pointAddEquivOfEq {W V : WeierstrassCurve K} (h : W = V) (P : W.toAffine.Point) :
    HEq (pointAddEquivOfEq h P) P := by
  subst h
  simp [pointAddEquivOfEq_rfl]

private theorem vcInvFun_nsmul (γ : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) (k : ℕ)
    (P : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.vcInvFun γ W.toAffine (k • P)
      = k • WeierstrassCurve.Affine.Point.vcInvFun γ W.toAffine P :=
  map_nsmul (vcAddEquiv γ W) k P

private theorem vcFun_nsmul (γ : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) (k : ℕ)
    (y : (γ • W).toAffine.Point) :
    WeierstrassCurve.Affine.Point.vcFun γ W.toAffine (k • y)
      = k • WeierstrassCurve.Affine.Point.vcFun γ W.toAffine y :=
  map_nsmul (vcAddEquiv γ W).symm k y

private theorem vcFun_vcInvFun (γ : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K)
    (P : W.toAffine.Point) :
    WeierstrassCurve.Affine.Point.vcFun γ W.toAffine
      (WeierstrassCurve.Affine.Point.vcInvFun γ W.toAffine P) = P :=
  WeierstrassCurve.Affine.Point.vcFun_rightInverse P

end HEqLaws

section Coprime

open AddSubgroup

variable {A : Type u} [AddCommGroup A] {N : ℕ} [NeZero N]

private theorem addOrderOf_nsmul_of_coprime {T : A} (hT : addOrderOf T = N) {k : ℕ} (hk : k.Coprime N) :
    addOrderOf (k • T) = N := by
  have hfin : IsOfFinAddOrder T :=
    addOrderOf_pos_iff.mp (hT ▸ Nat.pos_of_ne_zero (NeZero.ne N))
  rw [hfin.addOrderOf_nsmul, hT, Nat.Coprime.gcd_eq_one hk.symm, Nat.div_one]

private theorem zmultiples_nsmul_eq_of_coprime {T : A} (hT : addOrderOf T = N) {k : ℕ}
    (hk : k.Coprime N) : zmultiples (k • T) = zmultiples T := by
  haveI : Finite (zmultiples T) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hT]; exact NeZero.ne N)
  refine AddSubgroup.eq_of_le_of_card_ge (zmultiples_le.mpr (nsmul_mem (mem_zmultiples T) k)) ?_
  rw [Nat.card_zmultiples, Nat.card_zmultiples, hT, addOrderOf_nsmul_of_coprime hT hk]

private theorem exists_coprime_nsmul_iff_map_le (e : A ≃+ A) {T T' : A} (hT : addOrderOf T = N)
    (hT' : addOrderOf T' = N) :
    (∃ k : ℕ, k.Coprime N ∧ T' = k • e T) ↔ ∀ x ∈ zmultiples T, e x ∈ zmultiples T' := by
  have heT : addOrderOf (e T) = N := by rw [AddEquiv.addOrderOf_eq]; exact hT
  constructor
  · rintro ⟨k, hk, hTk⟩ x hx
    obtain ⟨m, rfl⟩ := mem_zmultiples_iff.mp hx
    rw [map_zsmul]
    have hz : zmultiples T' = zmultiples (e T) := by
      rw [hTk]; exact zmultiples_nsmul_eq_of_coprime heT hk
    rw [hz]
    exact zsmul_mem (mem_zmultiples (e T)) m
  · intro hmap
    have hle : zmultiples (e T) ≤ zmultiples T' := zmultiples_le.mpr (hmap T (mem_zmultiples T))
    haveI : Finite (zmultiples T') :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hT']; exact NeZero.ne N)
    have hz : zmultiples (e T) = zmultiples T' :=
      AddSubgroup.eq_of_le_of_card_ge hle
        (by rw [Nat.card_zmultiples, Nat.card_zmultiples, hT', heT])
    exact exists_nsmul_coprime_of_mem_zmultiples heT hT' (by rw [hz]; exact mem_zmultiples T')

end Coprime

section StepEquiv

variable {N : ℕ} {K : Type u} [Field K] [DecidableEq K]

private theorem step_refl (P : Gamma0Pair N K) : Gamma0Pair.Step P P :=
  ⟨1, one_smul _ _, 1, Nat.coprime_one_left N, by rw [one_nsmul]; exact (heq_vcInvFun_one _ _).symm⟩

private theorem step_symm [NeZero N] {P Q : Gamma0Pair N K} (h : Gamma0Pair.Step P Q) :
    Gamma0Pair.Step Q P := by
  obtain ⟨PC, Pell, Pgen, Pord⟩ := P
  obtain ⟨QC, Qell, Qgen, Qord⟩ := Q
  obtain ⟨γ, hγ, k, hk, hheq⟩ := h
  have e : γ • PC = QC := hγ
  subst e
  have hQ : Qgen = k • WeierstrassCurve.Affine.Point.vcInvFun γ PC.toAffine Pgen := eq_of_heq hheq
  have hPord : addOrderOf Pgen = N := Pord
  have himg : WeierstrassCurve.Affine.Point.vcFun γ PC.toAffine Qgen = k • Pgen := by
    rw [hQ, vcFun_nsmul, vcFun_vcInvFun]
  have hord : addOrderOf (WeierstrassCurve.Affine.Point.vcFun γ PC.toAffine Qgen) = N := by
    rw [himg]; exact addOrderOf_nsmul_of_coprime hPord hk
  have hmem : Pgen ∈ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.vcFun γ PC.toAffine Qgen) := by
    rw [himg, zmultiples_nsmul_eq_of_coprime hPord hk]; exact AddSubgroup.mem_zmultiples Pgen
  obtain ⟨k', hk', hPk⟩ := exists_nsmul_coprime_of_mem_zmultiples hord hPord hmem
  refine ⟨γ⁻¹, inv_smul_smul γ PC, k', hk', ?_⟩
  show HEq Pgen (k' • WeierstrassCurve.Affine.Point.vcInvFun γ⁻¹ (γ • PC).toAffine Qgen)
  have h1 : (γ⁻¹ • (γ • PC).toAffine).toAffine = PC.toAffine := by rw [inv_smul_smul]
  rw [hPk]
  exact (ModularCurve.Point.heq_nsmul h1 k' (heq_vcInvFun_inv γ PC Qgen)).symm

private theorem step_trans {P Q R : Gamma0Pair N K} (h₁ : Gamma0Pair.Step P Q) (h₂ : Gamma0Pair.Step Q R) :
    Gamma0Pair.Step P R := by
  obtain ⟨PC, Pell, Pgen, Pord⟩ := P
  obtain ⟨QC, Qell, Qgen, Qord⟩ := Q
  obtain ⟨RC, Rell, Rgen, Rord⟩ := R
  obtain ⟨γ₁, hγ₁, k₁, hk₁, hh₁⟩ := h₁
  obtain ⟨γ₂, hγ₂, k₂, hk₂, hh₂⟩ := h₂
  have e₁ : γ₁ • PC = QC := hγ₁
  subst e₁
  have e₂ : γ₂ • (γ₁ • PC) = RC := hγ₂
  subst e₂
  have hQ : Qgen = k₁ • WeierstrassCurve.Affine.Point.vcInvFun γ₁ PC.toAffine Pgen := eq_of_heq hh₁
  have hR : Rgen = k₂ • WeierstrassCurve.Affine.Point.vcInvFun γ₂ (γ₁ • PC).toAffine Qgen :=
    eq_of_heq hh₂
  refine ⟨γ₂ * γ₁, mul_smul γ₂ γ₁ PC, k₂ * k₁, Nat.Coprime.mul_left hk₂ hk₁, ?_⟩
  show HEq Rgen ((k₂ * k₁) • WeierstrassCurve.Affine.Point.vcInvFun (γ₂ * γ₁) PC.toAffine Pgen)
  have h1 : ((γ₂ * γ₁) • PC.toAffine).toAffine = (γ₂ • (γ₁ • PC).toAffine).toAffine := by
    rw [mul_smul]
  rw [hR, hQ, vcInvFun_nsmul, ← mul_nsmul']
  exact (ModularCurve.Point.heq_nsmul h1 (k₂ * k₁) (heq_vcInvFun_mul γ₁ γ₂ PC Pgen)).symm

private theorem step_equivalence [NeZero N] : Equivalence (Gamma0Pair.Step (N := N) (L := K)) :=
  ⟨step_refl, step_symm, step_trans⟩

private theorem mk_eq_mk_iff_step [NeZero N] (P Q : Gamma0Pair N K) :
    (Quot.mk _ P : ModuliPoint N K) = Quot.mk _ Q ↔ Gamma0Pair.Step P Q :=
  Quot.eq.trans step_equivalence.eqvGen_iff

end StepEquiv

section Bridge

variable {N : ℕ} [NeZero N] {K : Type u} [Field K] [DecidableEq K]

private noncomputable def stabEquiv (E₀ : WeierstrassCurve K) {γ : WeierstrassCurve.VariableChange K}
    (hγ : γ • E₀ = E₀) : E₀.toAffine.Point ≃+ E₀.toAffine.Point :=
  (vcAddEquiv γ E₀).trans (pointAddEquivOfEq hγ)

omit [NeZero N] in
private theorem heq_stabEquiv (E₀ : WeierstrassCurve K) {γ : WeierstrassCurve.VariableChange K}
    (hγ : γ • E₀ = E₀) (T : E₀.toAffine.Point) :
    HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) (stabEquiv E₀ hγ T) :=
  (heq_pointAddEquivOfEq hγ (vcAddEquiv γ E₀ T)).symm

omit [NeZero N] in

private theorem step_pairOf_iff (E₀ : WeierstrassCurve K) [E₀.IsElliptic] {T T' : E₀.toAffine.Point}
    (hT : addOrderOf T = N) (hT' : addOrderOf T' = N) :
    Gamma0Pair.Step (pairOf E₀ T hT) (pairOf E₀ T' hT') ↔
      ∃ γ : WeierstrassCurve.VariableChange K, ∃ hγ : γ • E₀ = E₀, ∃ k : ℕ,
        k.Coprime N ∧ T' = k • stabEquiv E₀ hγ T := by
  constructor
  · rintro ⟨γ, hγ, k, hk, hh⟩
    have hγ' : γ • E₀ = E₀ := hγ
    refine ⟨γ, hγ', k, hk, ?_⟩
    have hh' : HEq T' (k • WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) := hh
    have h1 : γ • E₀.toAffine = E₀.toAffine := hγ'
    exact eq_of_heq (hh'.trans (ModularCurve.Point.heq_nsmul h1 k (heq_stabEquiv E₀ hγ' T)))
  · rintro ⟨γ, hγ, k, hk, hTk⟩
    refine ⟨γ, hγ, k, hk, ?_⟩
    show HEq T' (k • WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T)
    have h1 : γ • E₀.toAffine = E₀.toAffine := hγ
    rw [hTk]
    exact (ModularCurve.Point.heq_nsmul h1 k (heq_stabEquiv E₀ hγ T)).symm

private theorem moduliOf_eq_moduliOf_iff (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    {T T' : E₀.toAffine.Point} (hT : addOrderOf T = N) (hT' : addOrderOf T' = N) :
    moduliOf E₀ T hT = moduliOf E₀ T' hT' ↔
      ∃ γ : WeierstrassCurve.VariableChange K, ∃ hγ : γ • E₀ = E₀, ∃ k : ℕ,
        k.Coprime N ∧ T' = k • stabEquiv E₀ hγ T :=
  (mk_eq_mk_iff_step _ _).trans (step_pairOf_iff E₀ hT hT')

private theorem orbitMap_eq_orbitMap_iff (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (H H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    orbitMap E₀ H = orbitMap E₀ H' ↔ ∃ γ : WeierstrassCurve.VariableChange K, γ • E₀ = E₀ ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1,
        HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) T' := by
  obtain ⟨g, hg, hHg⟩ := exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2
  obtain ⟨g', hg', hHg'⟩ := exists_generator_of_isAddCyclic_card H'.1 N H'.2.1 H'.2.2
  rw [orbitMap_eq_moduliOf E₀ H hg hHg, orbitMap_eq_moduliOf E₀ H' hg' hHg',
    moduliOf_eq_moduliOf_iff]
  constructor
  · rintro ⟨γ, hγ, k, hk, hTk⟩
    refine ⟨γ, hγ, fun T hT => ⟨stabEquiv E₀ hγ T, ?_, heq_stabEquiv E₀ hγ T⟩⟩
    have hT₂ : T ∈ AddSubgroup.zmultiples g := hHg ▸ hT
    rw [hHg']
    exact (exists_coprime_nsmul_iff_map_le (stabEquiv E₀ hγ) hg hg').mp ⟨k, hk, hTk⟩ T hT₂
  · rintro ⟨γ, hγ, hmap⟩
    refine ⟨γ, hγ, ?_⟩
    refine (exists_coprime_nsmul_iff_map_le (stabEquiv E₀ hγ) hg hg').mpr fun T hT => ?_
    have hT₁ : T ∈ H.1 := by rw [hHg]; exact hT
    obtain ⟨T', hT', hh⟩ := hmap T hT₁
    have hTT : stabEquiv E₀ hγ T = T' := eq_of_heq ((heq_stabEquiv E₀ hγ T).symm.trans hh)
    rw [hTT, ← hHg']
    exact hT'

end Bridge

section Surj

variable {N : ℕ} [NeZero N] {K : Type u} [Field K] [DecidableEq K]

private theorem isAddCyclic_zmultiples {A : Type u} [AddCommGroup A] (g : A) :
    IsAddCyclic (AddSubgroup.zmultiples g) := by
  refine ⟨⟨g, AddSubgroup.mem_zmultiples g⟩, fun x => ?_⟩
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.2
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

omit [NeZero N] in

private theorem exists_generator_moduliPoint_eq (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    [IsAlgClosed K] (x : ModuliPoint N K) (hx : ModuliPoint.j x = E₀.j) :
    ∃ (T : E₀.toAffine.Point) (hT : addOrderOf T = N),
      IsAddCyclic (AddSubgroup.zmultiples T) ∧ Nat.card (AddSubgroup.zmultiples T) = N ∧
      (Quot.mk _ (⟨E₀, ‹_›, T, hT⟩ : Gamma0Pair N K) : ModuliPoint N K) = x := by
  revert hx
  induction x using Quot.ind with
  | _ P =>
  intro hx
  rw [ModuliPoint.j_mk] at hx
  obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq P.toCurve E₀ hx
  refine ⟨pointAddEquivOfEq hγ (vcAddEquiv γ P.toCurve P.gen),
    ?_, ?_⟩
  · rw [AddEquiv.addOrderOf_eq, AddEquiv.addOrderOf_eq]
    exact P.addOrderOf_gen
  · refine ⟨isAddCyclic_zmultiples _, ?_, ?_⟩
    · rw [Nat.card_zmultiples, AddEquiv.addOrderOf_eq, AddEquiv.addOrderOf_eq]
      exact P.addOrderOf_gen
    · refine (Quot.sound ⟨γ, hγ, 1, Nat.coprime_one_left N, ?_⟩).symm
      rw [one_nsmul]
      show HEq (pointAddEquivOfEq hγ
        (vcAddEquiv γ P.toCurve P.gen)) _
      rw [vcAddEquiv_apply]
      exact heq_pointAddEquivOfEq hγ _

end Surj

section Assembly

private theorem u1_assembly
    (N : ℕ) (K : Type u) [Field K] [DecidableEq K] [IsAlgClosed K]
    (hN : (N : K) ≠ 0) (E₀ : WeierstrassCurve K) [E₀.IsElliptic] :
    ∃ g : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
        ModuliPoint N K,
      (∀ H, ModuliPoint.j (g H) = E₀.j) ∧
      (∀ x : ModuliPoint N K, ModuliPoint.j x = E₀.j → ∃ H, g H = x) ∧
      (∀ H H', g H = g H' ↔ ∃ γ : WeierstrassCurve.VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1,
          HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) T') := by
  haveI : NeZero N := ⟨fun h => hN (by rw [h, Nat.cast_zero])⟩
  refine ⟨orbitMap E₀, fun H => j_orbitMap E₀ H, fun x hx => ?_,
    fun H H' => orbitMap_eq_orbitMap_iff E₀ H H'⟩
  obtain ⟨T, hT, hcyc, hcard, hx'⟩ := exists_generator_moduliPoint_eq E₀ x hx
  refine ⟨⟨AddSubgroup.zmultiples T, hcyc, hcard⟩, ?_⟩
  rw [orbitMap_eq_moduliOf E₀ _ hT rfl]
  exact hx'

end Assembly

end ModularCurve.CyclicModuli
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace PlacesOrbit
p2m_open "ModularCurve~CycSub"

p2m_open "AlgebraicCurve ModularCurve~CycSub P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"

section FinsetSupply

variable (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K]

omit [IsAlgClosed K] [DecidableEq K] in

private theorem finite_ord_fibre (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (j₀ : K) :
    {P : Place K (modularFunctionFieldC K N) |
      0 < P.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) j₀)}.Finite :=
  ModularCurve.finite_setOf_ord_jGeomGen_sub_pos K N
    (ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero K N hN) j₀

end FinsetSupply
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

section JointFibre

variable {N : ℕ} {K : Type*} [Field K] [DecidableEq K]

private def GammaRel (E₀ : WeierstrassCurve K)
    (H H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) : Prop :=
  ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
    ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'

private theorem jointFibre_iff (E₀ : WeierstrassCurve K) {P : Type*}
    (f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → P)
    (g : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
        ModuliPoint N K)
    (hf3 : ∀ H H', f H = f H' ↔ GammaRel E₀ H H')
    (hg3 : ∀ H H', g H = g H' ↔ GammaRel E₀ H H') :
    ∀ H H', g H = g H' ↔ f H = f H' := fun H H' =>
  (hg3 H H').trans (hf3 H H').symm

end JointFibre
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

end ModularCurve.PlacesOrbit
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace FrobOrbit
p2m_open "ModularCurve~CycSub"

p2m_open "WeierstrassCurve WeierstrassCurve.Affine ModularCurve~CycSub P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve"

noncomputable section

section Cast

variable {K : Type u} [Field K] [DecidableEq K]

private def castPt {V V' : WeierstrassCurve K} (h : V' = V) : V'.toAffine.Point ≃+ V.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

private theorem heq_castPt {V V' : WeierstrassCurve K} (h : V' = V) (P : V'.toAffine.Point) :
    HEq (castPt h P) P := by
  subst h
  rfl

private theorem castPt_eq_of_heq {V V' : WeierstrassCurve K} (h : V' = V) {P : V'.toAffine.Point}
    {Q : V.toAffine.Point} (hPQ : HEq P Q) : castPt h P = Q := by
  subst h
  exact eq_of_heq hPQ

private theorem castPt_injective {V V' : WeierstrassCurve K} (h : V' = V) : Function.Injective (castPt h) :=
  (castPt h).injective

omit [DecidableEq K] in

private theorem heq_vcInvFun_congr (γ : VariableChange K) {V V' : WeierstrassCurve K} (h : V' = V)
    {P : V'.toAffine.Point} {Q : V.toAffine.Point} (hPQ : HEq P Q) :
    HEq (Point.vcInvFun γ V'.toAffine P) (Point.vcInvFun γ V.toAffine Q) := by
  subst h
  rw [eq_of_heq hPQ]

omit [DecidableEq K] in

private theorem heq_mapPoint_congr {K' : Type u} [Field K'] (σ : K →+* K') {V V' : WeierstrassCurve K}
    (h : V' = V) {P : V'.toAffine.Point} {Q : V.toAffine.Point} (hPQ : HEq P Q) :
    HEq (mapPoint σ (W₀ := V') P) (mapPoint σ (W₀ := V) Q) := by
  subst h
  rw [eq_of_heq hPQ]

private theorem gamma0Pair_eq {N : ℕ} {P Q : Gamma0Pair N K} (hC : P.toCurve = Q.toCurve)
    (hg : HEq P.gen Q.gen) : P = Q := by
  obtain ⟨C, i, g, h⟩ := P
  obtain ⟨C', i', g', h'⟩ := Q
  cases hC
  cases hg
  rfl

end Cast
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

section Frob

variable {K : Type u} [Field K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
variable {E₀ : WeierstrassCurve K} (hfr : E₀.map (frobenius K q) = E₀)

private def frobPt : E₀.toAffine.Point →+ E₀.toAffine.Point :=
  (castPt hfr).toAddMonoidHom.comp (mapPointHom (frobenius K q) (W₀ := E₀))

private theorem frobPt_apply (P : E₀.toAffine.Point) :
    frobPt q hfr P = castPt hfr (mapPoint (frobenius K q) (W₀ := E₀) P) :=
  rfl

private theorem heq_frobPt (P : E₀.toAffine.Point) :
    HEq (mapPoint (frobenius K q) (W₀ := E₀) P) (frobPt q hfr P) :=
  (heq_castPt hfr _).symm

private theorem frobPt_injective : Function.Injective (frobPt q hfr) := fun _ _ h =>
  mapPoint_injective (frobenius K q) (W₀ := E₀) ((castPt hfr).injective h)

private theorem addOrderOf_frobPt (P : E₀.toAffine.Point) : addOrderOf (frobPt q hfr P) = addOrderOf P :=
  addOrderOf_injective (frobPt q hfr) (frobPt_injective q hfr) P

private def frobSub (H : AddSubgroup E₀.toAffine.Point) : AddSubgroup E₀.toAffine.Point :=
  H.map (frobPt q hfr)

private theorem mem_frobSub {H : AddSubgroup E₀.toAffine.Point} {T : E₀.toAffine.Point} :
    T ∈ frobSub q hfr H ↔ ∃ T₀ ∈ H, frobPt q hfr T₀ = T :=
  AddSubgroup.mem_map

private theorem frobPt_mem_frobSub {H : AddSubgroup E₀.toAffine.Point} {T : E₀.toAffine.Point} (hT : T ∈ H) :
    frobPt q hfr T ∈ frobSub q hfr H :=
  AddSubgroup.mem_map_of_mem _ hT

private theorem frobSub_zmultiples (T : E₀.toAffine.Point) :
    frobSub q hfr (AddSubgroup.zmultiples T) = AddSubgroup.zmultiples (frobPt q hfr T) :=
  AddMonoidHom.map_zmultiples _ _

private theorem isAddCyclic_frobSub (H : AddSubgroup E₀.toAffine.Point) [hH : IsAddCyclic H] :
    IsAddCyclic (frobSub q hfr H) :=
  isAddCyclic_of_surjective ((frobPt q hfr).addSubgroupMap H) ((frobPt q hfr).addSubgroupMap_surjective H)

private theorem natCard_frobSub (H : AddSubgroup E₀.toAffine.Point) : Nat.card (frobSub q hfr H) = Nat.card H :=
  AddSubgroup.card_map_of_injective (frobPt_injective q hfr)

private def frobSubN (N : ℕ) (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
  ⟨frobSub q hfr H.1, ⟨@isAddCyclic_frobSub K _ _ q _ _ E₀ hfr H.1 H.2.1, (natCard_frobSub q hfr H.1).trans H.2.2⟩⟩

@[scoped simp] private theorem coe_frobSubN (N : ℕ) (H : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    (frobSubN q hfr N H).1 = frobSub q hfr H.1 :=
  rfl

section Moduli

variable [hE : E₀.IsElliptic] {N : ℕ}

private theorem gamma0Pair_map_frobenius_eq (T : E₀.toAffine.Point) (hT : addOrderOf T = N) :
    Gamma0Pair.map (frobenius K q) (⟨E₀, hE, T, hT⟩ : Gamma0Pair N K) =
      ⟨E₀, hE, frobPt q hfr T, (addOrderOf_frobPt q hfr T).trans hT⟩ :=
  gamma0Pair_eq hfr (heq_frobPt q hfr T)

private theorem moduliPoint_map_frobenius_mk (T : E₀.toAffine.Point) (hT : addOrderOf T = N) :
    ModuliPoint.map (frobenius K q) (Quot.mk _ (⟨E₀, hE, T, hT⟩ : Gamma0Pair N K) : ModuliPoint N K) =
      (Quot.mk _ (⟨E₀, hE, frobPt q hfr T, (addOrderOf_frobPt q hfr T).trans hT⟩ : Gamma0Pair N K) :
        ModuliPoint N K) := by
  rw [ModuliPoint.map_mk, gamma0Pair_map_frobenius_eq q hfr T hT]

end Moduli
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

private def OrbitRel (E₀ : WeierstrassCurve K) (H H' : AddSubgroup E₀.toAffine.Point) : Prop :=
  ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
    ∀ T ∈ H, ∃ T' ∈ H', HEq (Point.vcInvFun γ E₀.toAffine T) T'

omit [DecidableEq K] in
include hfr in

private theorem map_frobenius_smul_eq {γ : VariableChange K} (hγ : γ • E₀ = E₀) :
    γ.map (frobenius K q) • E₀ = E₀ :=
  calc γ.map (frobenius K q) • E₀ = γ.map (frobenius K q) • E₀.map (frobenius K q) := by rw [hfr]
    _ = (γ • E₀).map (frobenius K q) := map_variableChange E₀ γ (frobenius K q)
    _ = E₀ := by rw [hγ, hfr]

private theorem orbitRel_frobSub {H H' : AddSubgroup E₀.toAffine.Point} (h : OrbitRel E₀ H H') :
    OrbitRel E₀ (frobSub q hfr H) (frobSub q hfr H') := by
  obtain ⟨γ, hγ, hpts⟩ := h
  refine ⟨γ.map (frobenius K q), map_frobenius_smul_eq q hfr hγ, ?_⟩
  intro T₁ hT₁
  obtain ⟨T, hT, rfl⟩ := (mem_frobSub q hfr).mp hT₁
  obtain ⟨T', hT', hTT'⟩ := hpts T hT
  refine ⟨frobPt q hfr T', frobPt_mem_frobSub q hfr hT', ?_⟩
  have h1 : HEq (Point.vcInvFun (γ.map (frobenius K q)) E₀.toAffine (frobPt q hfr T))
      (Point.vcInvFun (γ.map (frobenius K q)) (E₀.map (frobenius K q)).toAffine
        (mapPoint (frobenius K q) (W₀ := E₀) T)) :=
    heq_vcInvFun_congr (γ.map (frobenius K q)) hfr.symm (heq_frobPt q hfr T).symm
  have h2 : HEq (Point.vcInvFun (γ.map (frobenius K q)) (E₀.map (frobenius K q)).toAffine
        (mapPoint (frobenius K q) (W₀ := E₀) T))
      (mapPoint (frobenius K q) (W₀ := γ • E₀) (Point.vcInvFun γ E₀.toAffine T)) :=
    (mapPoint_vcInvFun_heq (frobenius K q) γ E₀ T).symm
  have h3 : HEq (mapPoint (frobenius K q) (W₀ := γ • E₀) (Point.vcInvFun γ E₀.toAffine T))
      (mapPoint (frobenius K q) (W₀ := E₀) T') :=
    heq_mapPoint_congr (frobenius K q) hγ hTT'
  exact h1.trans (h2.trans (h3.trans (heq_frobPt q hfr T')))

private theorem orbitRel_frobSubN (N : ℕ) {H H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}}
    (h : OrbitRel E₀ H.1 H'.1) : OrbitRel E₀ (frobSubN q hfr N H).1 (frobSubN q hfr N H').1 :=
  orbitRel_frobSub q hfr h

end Frob
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

end ModularCurve.FrobOrbit
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace FrobTwist
p2m_open "ModularCurve~CycSub"

section Sign

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

private theorem map_map_eq_of_sign (θ : A →+ B) (frE : A →+ A) (fr₀ : B →+ B) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (H : AddSubgroup A) (hH : ∀ P ∈ H, θ (frE P) = ε • fr₀ (θ P)) :
    (H.map frE).map θ = (H.map θ).map fr₀ := by
  ext T
  simp only [AddSubgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    rcases hε with rfl | rfl
    · exact ⟨θ P, ⟨P, hP, rfl⟩, by rw [hH P hP, one_zsmul]⟩
    · exact ⟨θ (-P), ⟨-P, neg_mem hP, rfl⟩, by rw [hH P hP, map_neg, map_neg, neg_one_zsmul]⟩
  · rintro ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    rcases hε with rfl | rfl
    · exact ⟨frE P, ⟨P, hP, rfl⟩, by rw [hH P hP, one_zsmul]⟩
    · exact ⟨frE (-P), ⟨-P, neg_mem hP, rfl⟩, by rw [map_neg, map_neg, hH P hP, neg_one_zsmul, neg_neg]⟩

end Sign
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

section Twist

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem twist_of_forall_mem (g : SemilinearAut K F) (G : SemilinearAut K F')
    (hbase : ∀ a : K, SemilinearAut.baseAut g a = SemilinearAut.baseAut G a)
    (ψ ψ' : F →ₐ[K] F') (S : Set F) (hS : ∀ s ∈ S, ψ' (g • s) = G • ψ s)
    (hgen : ∀ x : F, x ∈ Subfield.closure (Set.range (algebraMap K F) ∪ S)) (x : F) :
    ψ' (g • x) = G • ψ x := by
  let φ₁ : F →+* F' := ψ'.toRingHom.comp (SemilinearAut.toRingAut g).toRingHom
  let φ₂ : F →+* F' := (SemilinearAut.toRingAut G).toRingHom.comp ψ.toRingHom
  have h1 : ∀ y, φ₁ y = ψ' (g • y) := fun _ => rfl
  have h2 : ∀ y, φ₂ y = G • ψ y := fun _ => rfl
  suffices h : Subfield.closure (Set.range (algebraMap K F) ∪ S) ≤ RingHom.eqLocusField φ₁ φ₂ by
    have hx := h (hgen x)
    rw [RingHom.mem_eqLocusField, h1, h2] at hx
    exact hx
  refine Subfield.closure_le.mpr ?_
  rintro y (⟨a, rfl⟩ | hy)
  · show φ₁ (algebraMap K F a) = φ₂ (algebraMap K F a)
    rw [h1, h2, SemilinearAut.smul_algebraMap, AlgHom.commutes, AlgHom.commutes, SemilinearAut.smul_algebraMap,
      hbase]
  · show φ₁ y = φ₂ y
    rw [h1, h2]
    exact hS y hy

private theorem mem_restrictAlong_iff (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : Place K F') (x : F) :
    x ∈ (W.restrictAlong ψ hψ).toValuationSubring ↔ ψ x ∈ W.toValuationSubring :=
  Iff.rfl

private theorem restrictAlong_twist (g : SemilinearAut K F) (G : SemilinearAut K F') (W : Place K F')
    (hW : G • W = W) (ψ ψ' : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (htw : ∀ x : F, ψ' (g • x) = G • ψ x) :
    W.restrictAlong ψ' hψ' = g • W.restrictAlong ψ hψ := by
  apply Place.ext
  ext x
  rw [mem_restrictAlong_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_restrictAlong_iff]
  have hx : ψ' x = G • ψ (g⁻¹ • x) := by
    rw [← htw (g⁻¹ • x), smul_inv_smul]
  rw [hx]
  conv_lhs => rw [← hW, SemilinearAut.smul_toValuationSubring]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

end Twist
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

end ModularCurve.FrobTwist
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

p2m_open "WeierstrassCurve WeierstrassCurve.Affine ModularCurve~CycSub P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve AlgebraicCurve"
open scoped IntermediateField

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace TorsionOrbit
namespace Assembly
p2m_open "ModularCurve~CycSub"

section AutPt

variable {L : Type*} [Field L] [DecidableEq L]

private def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

private theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

private def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

private theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

private theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

private theorem autPt_injective {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    Function.Injective (autPt γ hγ) := by
  intro P Q h
  rw [autPt_apply, autPt_apply] at h
  exact (Point.vcFun_rightInverse (C := γ) (W := W.toAffine)).injective ((castPt hγ).injective h)

end AutPt
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

section CycSub

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N : ℕ)

private abbrev CycSub (A : Type*) [AddCommGroup A] (N : ℕ) : Type _ :=
  {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}

variable {N}

private theorem _root_.ModularCurve.TorsionOrbit.Assembly.exists_generator (hN : N ≠ 0) (H : CycSub A N) :
    ∃ g : A, addOrderOf g = N ∧ AddSubgroup.zmultiples g = H.1 := by
  obtain ⟨hc, hcard⟩ := H.2
  haveI := hc
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
  have hfin : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hog : addOrderOf g = N := (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcard
  refine ⟨g.1, by rw [AddSubgroup.addOrderOf_coe, hog], ?_⟩
  have hle : AddSubgroup.zmultiples (g.1) ≤ H.1 := by
    rw [AddSubgroup.zmultiples_le]; exact g.2
  refine AddSubgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zmultiples, AddSubgroup.addOrderOf_coe, hog]

p2m_export "ModularCurve.TorsionOrbit.Assembly" "exists_generator"
private def cycOf (g : A) (hg : addOrderOf g = N) : CycSub A N :=
  ⟨AddSubgroup.zmultiples g, ⟨⟨g, AddSubgroup.mem_zmultiples g⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, hg]⟩

private theorem nsmul_eq_zero_of_mem (H : CycSub A N) {x : A} (hx : x ∈ H.1) : N • x = 0 := by
  have h : Nat.card H.1 • (⟨x, hx⟩ : H.1) = 0 := card_nsmul_eq_zero'
  rw [H.2.2] at h
  exact congrArg Subtype.val h

private def mapCyc (φ : A →+ B) (H : CycSub A N) (hφ : Set.InjOn φ H.1) : CycSub B N := by
  refine ⟨H.1.map φ, ?_, ?_⟩
  · obtain ⟨hc, -⟩ := H.2
    haveI := hc
    obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H.1)
    refine ⟨⟨⟨φ g.1, AddSubgroup.mem_map_of_mem φ g.2⟩, fun y => ?_⟩⟩
    obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp y.2
    obtain ⟨n, hn⟩ := hg ⟨x, hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : n • g.1 = x := congrArg Subtype.val hn
    simp only [AddSubgroup.coe_zsmul, ← hxy, ← hn', map_zsmul]
  · have h := Nat.card_image_of_injOn hφ
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
    have hc : Nat.card (H.1.map φ) = Nat.card H.1 := by
      rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe H.1, Nat.card_coe_set_eq,
        Nat.card_coe_set_eq, AddSubgroup.coe_map]
      exact h
    exact hc.trans H.2.2

@[scoped simp] private theorem mapCyc_val (φ : A →+ B) (H : CycSub A N) (hφ : Set.InjOn φ H.1) :
    (mapCyc φ H hφ).1 = H.1.map φ := rfl

private def tors (A : Type*) [AddCommGroup A] (N : ℕ) : Set A := {x | N • x = 0}

private theorem subset_tors (H : CycSub A N) : (H.1 : Set A) ⊆ tors A N :=
  fun _ hx => nsmul_eq_zero_of_mem H hx

private theorem injOn_of_injOn_tors {φ : A →+ B} (hφ : Set.InjOn φ (tors A N)) (H : CycSub A N) :
    Set.InjOn φ H.1 :=
  hφ.mono (subset_tors H)

private theorem mapCyc_injective {φ : A →+ B} (hφ : Set.InjOn φ (tors A N)) {H H' : CycSub A N}
    (h : mapCyc φ H (injOn_of_injOn_tors hφ H) = mapCyc φ H' (injOn_of_injOn_tors hφ H')) :
    H = H' := by
  have h1 : (φ '' (H.1 : Set A)) = φ '' (H'.1 : Set A) := by
    have := congrArg (fun X : CycSub B N => ((X.1 : AddSubgroup B) : Set B)) h
    simpa only [mapCyc_val, AddSubgroup.coe_map] using this
  have h2 : (H.1 : Set A) = H'.1 := (hφ.image_eq_image_iff (subset_tors H) (subset_tors H')).mp h1
  exact Subtype.ext (SetLike.coe_injective h2)

private theorem mapCyc_surjective (hN : N ≠ 0) {φ : A →+ B} (hφ : Set.InjOn φ (tors A N))
    (hsurj : ∀ y ∈ tors B N, ∃ x ∈ tors A N, φ x = y) (H₀ : CycSub B N) :
    ∃ H : CycSub A N, mapCyc φ H (injOn_of_injOn_tors hφ H) = H₀ := by
  obtain ⟨g₀, hg₀, hgen⟩ := exists_generator hN H₀
  have hg₀t : g₀ ∈ tors B N := by
    show N • g₀ = 0
    rw [← hg₀]; exact addOrderOf_nsmul_eq_zero g₀
  obtain ⟨g, hgt, hgφ⟩ := hsurj g₀ hg₀t
  have hordg : addOrderOf g = N := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hgt) ?_
    rw [← hg₀, ← hgφ]
    exact addOrderOf_map_dvd φ g
  refine ⟨cycOf g hordg, Subtype.ext ?_⟩
  show (AddSubgroup.zmultiples g).map φ = H₀.1
  rw [AddMonoidHom.map_zmultiples, hgφ, hgen]

private theorem eq_of_le_of_card_eq {H H' : AddSubgroup B} (hle : H ≤ H') (hH : Nat.card H = N)
    (hH' : Nat.card H' = N) (hN : N ≠ 0) : H = H' := by
  haveI : Finite H' := Nat.finite_of_card_ne_zero (by rw [hH']; exact hN)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [hH, hH'])

private theorem map_neg_eq (H : AddSubgroup B) : H.map (-(AddMonoidHom.id B)) = H := by
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.neg_apply, AddMonoidHom.id_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact H.neg_mem hy
  · intro hx; exact ⟨-x, H.neg_mem hx, neg_neg x⟩

end CycSub
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

section Assemble

variable {L : Type*} [Field L] [DecidableEq L] {E₀ : WeierstrassCurve L} {N : ℕ}
variable {Pt : Type*} [AddCommGroup Pt]
variable {G : Type*}
variable {X : Type*}
variable {Pl : Type*}

private def Rel (E₀ : WeierstrassCurve L) (N : ℕ) (H H' : CycSub E₀.toAffine.Point N) : Prop :=
  ∃ γ : VariableChange L, γ • E₀ = E₀ ∧
    ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T'

private theorem Rel_iff (H H' : CycSub E₀.toAffine.Point N) :
    Rel E₀ N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, ∀ T ∈ H.1, autPt γ hγ T ∈ H'.1 := by
  unfold Rel
  constructor
  · rintro ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, fun T hT => ?_⟩
    obtain ⟨T', hT', hh⟩ := h T hT
    rwa [(autPt_eq_iff_heq γ hγ T T').mpr hh]
  · rintro ⟨γ, hγ, h⟩
    exact ⟨γ, hγ, fun T hT => ⟨autPt γ hγ T, h T hT, (autPt_eq_iff_heq γ hγ T _).mp rfl⟩⟩

private theorem Rel_iff_map_eq (hN : N ≠ 0) (H H' : CycSub E₀.toAffine.Point N) :
    Rel E₀ N H H' ↔ ∃ γ : VariableChange L, ∃ hγ : γ • E₀ = E₀, H.1.map (autPt γ hγ) = H'.1 := by
  rw [Rel_iff]
  refine exists_congr fun γ => exists_congr fun hγ => ?_
  constructor
  · intro h
    have hle : H.1.map (autPt γ hγ) ≤ H'.1 := by
      rintro _ ⟨T, hT, rfl⟩; exact h T hT
    have hcard : Nat.card (H.1.map (autPt γ hγ)) = N :=
      (mapCyc (autPt γ hγ) H ((autPt_injective γ hγ).injOn)).2.2
    exact eq_of_le_of_card_eq hle hcard H'.2.2 hN
  · intro h T hT
    rw [← h]; exact AddSubgroup.mem_map_of_mem _ hT

end Assemble
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

section AssembleFr

variable {L : Type*} [Field L] [DecidableEq L] {E₀ : WeierstrassCurve L} {N : ℕ}
variable {Pt : Type*} [AddCommGroup Pt] {G : Type*} {X : Type*} {Pl : Type*}

private theorem assemble_fr (hN : N ≠ 0)
    (θ : Pt →+ E₀.toAffine.Point) (hθ : Set.InjOn θ (tors Pt N))
    (hθs : ∀ y ∈ tors E₀.toAffine.Point N, ∃ x ∈ tors Pt N, θ x = y)
    (D : G → Prop) (act : G → (Pt →+ Pt)) (hact : ∀ σ, Function.Injective (act σ))
    (ρ : G → VariableChange L) (hρ : ∀ σ, D σ → ρ σ • E₀ = E₀)
    (hequiv : ∀ σ (hσ : D σ) (P : Pt), θ (act σ P) = autPt (ρ σ) (hρ σ hσ) (θ P))
    (hsurj : ∀ (γ : VariableChange L) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))))
    (Φ : CycSub Pt N ≃ X) (actX : G → X → X)
    (hnat : ∀ σ (H : CycSub Pt N), Φ (mapCyc (act σ) H (hact σ).injOn) = actX σ (Φ H))
    (π : X → Pl) (S : Finset Pl) (hπS : ∀ x, π x ∈ S) (hπsurj : ∀ P ∈ S, ∃ x, π x = P)
    (hπfib : ∀ x x', π x = π x' ↔ ∃ σ, D σ ∧ x' = actX σ x)
    (e : Pl → ℤ) (hπe : ∀ x, e (π x) = Nat.card {x' // π x' = π x})
    (frPt : Pt →+ Pt) (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hfr₀ : Set.InjOn fr₀ (tors E₀.toAffine.Point N))
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hsign : ∀ P ∈ tors Pt N, θ (frPt P) = ε • fr₀ (θ P))
    (frPl : Pl → Pl)
    (hπfr : ∀ (H : CycSub Pt N) (hH : Set.InjOn frPt H.1),
      π (Φ (mapCyc frPt H hH)) = frPl (π (Φ H))) :
    ∃ f : CycSub E₀.toAffine.Point N → Pl,
      (∀ H, f H ∈ S) ∧ (∀ P ∈ S, ∃ H, f H = P) ∧
      (∀ H H', f H = f H' ↔ Rel E₀ N H H') ∧
      (∀ H, e (f H) = Nat.card {H' // f H' = f H}) ∧
      ∀ (H₀ : CycSub E₀.toAffine.Point N) (h₀ : Set.InjOn fr₀ H₀.1),
        f (mapCyc fr₀ H₀ h₀) = frPl (f H₀) := by
  classical

  let Ξf : CycSub Pt N → CycSub E₀.toAffine.Point N := fun H => mapCyc θ H (injOn_of_injOn_tors hθ H)
  have hΞ : Function.Bijective Ξf :=
    ⟨fun H H' h => mapCyc_injective hθ h, fun H₀ => mapCyc_surjective hN hθ hθs H₀⟩
  let Ξ : CycSub Pt N ≃ CycSub E₀.toAffine.Point N := Equiv.ofBijective Ξf hΞ
  have Ξ_val : ∀ H, (Ξ H).1 = H.1.map θ := fun H => rfl

  let εq : CycSub E₀.toAffine.Point N ≃ X := Ξ.symm.trans Φ
  refine ⟨fun H₀ => π (εq H₀), fun H₀ => hπS _, ?_, ?_, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨x, hx⟩ := hπsurj P hP
    exact ⟨εq.symm x, by simp only [Equiv.apply_symm_apply, hx]⟩
  ·
    intro H₀ H₀'
    rw [hπfib, Rel_iff_map_eq hN]
    have key : ∀ σ (hσ : D σ) (H : CycSub Pt N),
        (Ξ (mapCyc (act σ) H (hact σ).injOn)).1 = (Ξ H).1.map (autPt (ρ σ) (hρ σ hσ)) := by
      intro σ hσ H
      rw [Ξ_val, Ξ_val, mapCyc_val, AddSubgroup.map_map, AddSubgroup.map_map]
      congr 1
      ext P
      exact hequiv σ hσ P
    constructor
    · rintro ⟨σ, hσ, hx⟩
      have h1 : Φ (Ξ.symm H₀') = Φ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn) := by
        rw [hnat]; exact hx
      have h2 : Ξ.symm H₀' = mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn := Φ.injective h1
      refine ⟨ρ σ, hρ σ hσ, ?_⟩
      have h3 := key σ hσ (Ξ.symm H₀)
      rw [← h2, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h3
      exact h3.symm
    · rintro ⟨γ, hγ, hmap⟩
      obtain ⟨σ, hσ, hsgn⟩ := hsurj γ hγ
      refine ⟨σ, hσ, ?_⟩
      have h1 : (Ξ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn)).1 = H₀'.1 := by
        rw [Ξ_val, mapCyc_val, AddSubgroup.map_map]
        have hH₀ : (Ξ.symm H₀).1.map θ = H₀.1 := by
          rw [← Ξ_val, Equiv.apply_symm_apply]
        rcases hsgn with h | h
        · have hc : θ.comp (act σ) = (autPt γ hγ).comp θ := by ext P; exact h P
          rw [hc, ← AddSubgroup.map_map, hH₀, hmap]
        · have hc : θ.comp (act σ) = (-(AddMonoidHom.id _)).comp ((autPt γ hγ).comp θ) := by
            ext P; simp [h P]
          rw [hc, ← AddSubgroup.map_map, ← AddSubgroup.map_map, hH₀, hmap, map_neg_eq]
      have h2 : Ξ (mapCyc (act σ) (Ξ.symm H₀) (hact σ).injOn) = H₀' := Subtype.ext h1
      show Φ (Ξ.symm H₀') = actX σ (Φ (Ξ.symm H₀))
      rw [← hnat, ← h2, Equiv.symm_apply_apply]
  ·
    intro H₀
    rw [hπe]
    congr 1
    exact Nat.card_congr ((Equiv.subtypeEquiv εq (fun H₀' => Iff.rfl)).symm)
  ·
    intro H₀ h₀
    have hθtors : ∀ P ∈ tors Pt N, θ P ∈ tors E₀.toAffine.Point N := by
      intro P hP
      show N • θ P = 0
      rw [← map_nsmul, show N • P = 0 from hP, map_zero]
    have hinjfr : Set.InjOn frPt (Ξ.symm H₀).1 := by
      intro P hP Q hQ hPQ
      have hPt : P ∈ tors Pt N := subset_tors _ hP
      have hQt : Q ∈ tors Pt N := subset_tors _ hQ
      have h1 : ε • fr₀ (θ P) = ε • fr₀ (θ Q) := by rw [← hsign P hPt, ← hsign Q hQt, hPQ]
      have h2 : fr₀ (θ P) = fr₀ (θ Q) := by
        rcases hε with rfl | rfl
        · rw [one_zsmul, one_zsmul] at h1
          exact h1
        · rw [neg_one_zsmul, neg_one_zsmul, neg_inj] at h1
          exact h1
      exact hθ hPt hQt (hfr₀ (hθtors P hPt) (hθtors Q hQt) h2)
    have key : Ξ (mapCyc frPt (Ξ.symm H₀) hinjfr) = mapCyc fr₀ H₀ h₀ := by
      apply Subtype.ext
      rw [Ξ_val, mapCyc_val, mapCyc_val,
        ModularCurve.FrobTwist.map_map_eq_of_sign θ frPt fr₀ ε hε _
          (fun P hP => hsign P (subset_tors _ hP))]
      congr 1
      rw [← Ξ_val, Equiv.apply_symm_apply]
    show π (Φ (Ξ.symm (mapCyc fr₀ H₀ h₀))) = frPl (π (Φ (Ξ.symm H₀)))
    rw [← key, Equiv.symm_apply_apply]
    exact hπfr _ hinjfr

end AssembleFr
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

section Supplies

private theorem isIntegral_of_apply_eq {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F]
    [Algebra K M] (x : F) (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral K⟮t⟯ y := Algebra.IsIntegral.isIntegral y
  obtain ⟨q, hqm, hq0⟩ := hy

  have hle : K⟮t⟯ ≤ ψ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨x, hψ⟩

  have hlifts : q.map (algebraMap K⟮t⟯ M) ∈ Polynomial.lifts ψ.toRingHom := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨f, hf⟩ := hle (q.coeff n).2
    exact ⟨f, hf⟩
  obtain ⟨q', hq'map, -, hq'monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (hqm.map _)
  refine ⟨q', hq'monic, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hq0

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

private theorem tors_facts (E₀ : WeierstrassCurve K) [E₀.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) :
    Nat.card (tors E₀.toAffine.Point N) = N ^ 2 ∧ ∃ g : E₀.toAffine.Point, addOrderOf g = N := by
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) E₀ hN
  have hb : (E₀⁄K) = E₀.toAffine := by
    show (E₀.baseChange K).toAffine = E₀.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT
  have hmem : ∀ P : E₀.toAffine.Point, P ∈ Submodule.torsionBy ℤ E₀.toAffine.Point N ↔ P ∈ tors _ N := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    show ((N : ℤ) • P = 0) ↔ N • P = 0
    rw [natCast_zsmul]
  have hset : (Submodule.torsionBy ℤ E₀.toAffine.Point N : Set E₀.toAffine.Point) = tors _ N :=
    Set.ext hmem
  constructor
  · have h1 : Nat.card (Submodule.torsionBy ℤ E₀.toAffine.Point N) = N ^ 2 := by
      rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
    rw [← SetLike.coe_sort_coe, hset] at h1
    exact h1
  · refine ⟨(eT (1, 0)).1, ?_⟩
    have h1 : addOrderOf ((eT (1, 0)).1) = addOrderOf (eT (1, 0)) :=
      addOrderOf_injective (Submodule.torsionBy ℤ E₀.toAffine.Point N).subtype.toAddMonoidHom
        Subtype.val_injective (eT (1, 0))
    rw [h1, AddEquiv.addOrderOf_eq eT, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
      Nat.lcm_one_right]

end Supplies
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

end ModularCurve.TorsionOrbit.Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace FrobOrbit
namespace PointLaw
p2m_open "ModularCurve~CycSub"

open ModularCurve.FrobOrbit ModularCurve.TorsionOrbit.Assembly

variable {K : Type u} [Field K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
variable {E₀ : WeierstrassCurve K} (hfr : E₀.map (frobenius K q) = E₀)

private theorem frobPt_some {x y : K} (h : E₀.toAffine.Nonsingular x y) :
    ∃ h' : E₀.toAffine.Nonsingular (x ^ q) (y ^ q),
      frobPt q hfr (.some x y h) = .some (x ^ q) (y ^ q) h' := by
  have hns : E₀.toAffine.Nonsingular (x ^ q) (y ^ q) := by
    have h1 : (E₀.map (frobenius K q)).toAffine.Nonsingular (x ^ q) (y ^ q) :=
      (E₀.toAffine.map_nonsingular (frobenius K q).injective x y).mpr h
    rw [hfr] at h1
    exact h1
  refine ⟨hns, ?_⟩
  rw [frobPt_apply, WeierstrassCurve.mapPoint_some]
  exact castPt_eq_of_heq hfr
    (ModularCurve.Point.heq_some (congrArg WeierstrassCurve.toAffine hfr)
      (show frobenius K q x = x ^ q from rfl) (show frobenius K q y = y ^ q from rfl))

private theorem eq_frobPt_of_forall_some (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hfr₀ : ∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
      ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') :
    fr₀ = frobPt q hfr := by
  ext P
  rcases P with _ | ⟨x, y, h⟩
  · show fr₀ 0 = frobPt q hfr 0
    rw [map_zero, map_zero]
  · obtain ⟨h', e'⟩ := hfr₀ x y h
    obtain ⟨h'', e''⟩ := frobPt_some q hfr h
    rw [e', e'']

include hfr in

private theorem injOn_tors_of_forall_some (N : ℕ) (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hfr₀ : ∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
      ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') :
    Set.InjOn fr₀ (tors E₀.toAffine.Point N) := by
  have hf := eq_frobPt_of_forall_some q hfr fr₀ hfr₀
  subst hf
  exact (frobPt_injective q hfr).injOn

private theorem mapCyc_eq_frobSubN_of_forall_some (N : ℕ) (fr₀ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hfr₀ : ∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
      ∃ h', fr₀ (.some x y h) = .some (x ^ q) (y ^ q) h') :
    ∀ (H : CycSub E₀.toAffine.Point N) (h : Set.InjOn fr₀ H.1),
      mapCyc fr₀ H h = frobSubN q hfr N H := by
  have hf := eq_frobPt_of_forall_some q hfr fr₀ hfr₀
  subst hf
  intro H h
  exact Subtype.ext (mapCyc_val _ H h)

end ModularCurve.FrobOrbit.PointLaw
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace LevelFieldFrobenius
p2m_open "ModularCurve~CycSub"

section FrobeniusFacts

variable (q : ℕ) (K : Type u) [Field K] [Fact q.Prime] [CharP K q] [PerfectField K] (N : ℕ) [NeZero N]

private theorem arithFrobC_smul_algebraMap :
    ∀ a : K, arithFrobC q K N • algebraMap K (modularFunctionFieldC K N) a =
      algebraMap K (modularFunctionFieldC K N) (a ^ q) := by
  intro a
  rw [SemilinearAut.smul_algebraMap, baseAut_arithFrobC_apply]

private theorem arithFrobC_smul_of_mem_divisorExpansionsC :
    ∀ y : modularFunctionFieldC K N, (y : LaurentSeries K) ∈ divisorExpansionsC K N →
      arithFrobC q K N • y = y := by
  intro y hy
  obtain ⟨d, hd, -, hyd⟩ := hy
  apply Subtype.ext
  rw [arithFrobC, coe_coeffSemilinearAut_smul, hyd, coeffSemilinearAut.coeffMap_qExpand,
    coeffSemilinearAut.coeffMap_jqModC]

end FrobeniusFacts
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

end ModularCurve.LevelFieldFrobenius
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace TorsionOrbit
p2m_open "ModularCurve~CycSub"

private theorem mem_closure_C (q N : ℕ) [NeZero N] (K : Type u) [Field K] [CharP K q] (hqN : ¬ q ∣ N)
    (x : modularFunctionFieldC K N) :
    x ∈ Subfield.closure (Set.range (algebraMap K (modularFunctionFieldC K N)) ∪
        {y : modularFunctionFieldC K N | (y : LaurentSeries K) ∈ divisorExpansionsC K N}) := by
  have hC : modularFunctionFieldC K N = modularFunctionFieldFullC K N :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN
  have hle : Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ divisorExpansionsC K N) ≤
      (Subfield.closure (Set.range (algebraMap K (modularFunctionFieldC K N)) ∪
        {y : modularFunctionFieldC K N | (y : LaurentSeries K) ∈ divisorExpansionsC K N})).map
        (algebraMap (modularFunctionFieldC K N) (LaurentSeries K)) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · exact Subfield.mem_map.mpr ⟨algebraMap K (modularFunctionFieldC K N) a,
        Subfield.subset_closure (Or.inl ⟨a, rfl⟩), rfl⟩
    · have hzC : z ∈ modularFunctionFieldC K N := by
        rw [hC]
        exact IntermediateField.subset_adjoin K _ hz
      exact Subfield.mem_map.mpr ⟨⟨z, hzC⟩, Subfield.subset_closure (Or.inr hz), rfl⟩
  have hx : (x : LaurentSeries K) ∈
      Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ divisorExpansionsC K N) := by
    have hxF : (x : LaurentSeries K) ∈ modularFunctionFieldFullC K N := hC ▸ x.2
    exact hxF
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (hle hx)
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

open Assembly

private theorem sigma_orbitMap_at
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (q : ℕ) [Fact q.Prime] [CharP K q]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hfr : E₀.map (frobenius K q) = E₀)
    (F : IntermediateField K (LaurentSeries K)) (hF : modularFunctionFieldFullC K N = F)
    (hmem : jqModC K ∈ F) (frF : SemilinearAut K F)
    (hfrK : ∀ a : K, frF • algebraMap K F a = algebraMap K F (a ^ q))
    (hfrd : ∀ y : F, (y : LaurentSeries K) ∈ divisorExpansionsC K N → frF • y = y)
    (hgen : ∀ x : F, x ∈ Subfield.closure (Set.range (algebraMap K F) ∪
        {y : F | (y : LaurentSeries K) ∈ divisorExpansionsC K N}))
    (S : Finset (Place K F))
    (hS : ∀ P, P ∈ S ↔ 0 < P.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F E₀.j)) :
    ∃ f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → Place K F,
      (∀ H, f H ∈ S) ∧ (∀ P ∈ S, ∃ H, f H = P) ∧
      (∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ E₀.toAffine T) T') ∧
      (∀ H, (f H).ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F E₀.j) =
        (Nat.card {H' : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
          f H' = f H} : ℤ)) ∧
      (∀ H, f (ModularCurve.FrobOrbit.frobSubN q hfr N H) = frF • f H) := by
  subst hF
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  let F := modularFunctionFieldFullC K N
  let jF : F := ⟨jqModC K, hmem⟩
  have hqN : ¬ q ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K q N).mpr h)

  obtain ⟨M, _iF, _iD, _iA, t, ht, hfin, hgal, W₀, hW₀, θ, ρ, Φ, frM, frE, fr₀, ε, hfull, hθinj, hρE,
      hequivC, hsurjC, hnatA, hfrMK, hfrMt, hfrMW, hfrE, hfr₀, hε, hsign, hF5⟩ :=
    ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ K q N hN E₀ hfr
  haveI := hfin
  haveI := hgal

  let tk : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩
  let E : WeierstrassCurve K⟮t⟯ := WeierstrassCurve.ofJ tk

  let X : Type _ := {ψ : F →ₐ[K] M // ψ jF = t}
  let ΦX : CycSub (E.baseChange M).toAffine.Point N ≃ X := Φ
  have ΦX_val : ∀ H, (ΦX H).1 = (Φ H).1 := fun H => rfl

  have hint : ∀ ψ : F →ₐ[K] M, ψ jF = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_apply_eq jF t ψ hψ

  obtain ⟨hcard₀, g₀, hg₀⟩ := tors_facts E₀ hN
  have hθ : Set.InjOn θ (tors (E.baseChange M).toAffine.Point N) := by
    intro P hP Q hQ h
    have hPQ : N • (P - Q) = 0 := by
      rw [nsmul_sub, show N • P = 0 from hP, show N • Q = 0 from hQ, sub_zero]
    have := hθinj N (P - Q) hqN hPQ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  have hθs : ∀ y ∈ tors E₀.toAffine.Point N, ∃ x ∈ tors (E.baseChange M).toAffine.Point N, θ x = y := by
    let θr : tors (E.baseChange M).toAffine.Point N → tors E₀.toAffine.Point N :=
      fun P => ⟨θ P.1, show N • θ P.1 = 0 by rw [← map_nsmul, show N • P.1 = 0 from P.2, map_zero]⟩
    have hinj : Function.Injective θr := fun P Q h =>
      Subtype.ext (hθ P.2 Q.2 (congrArg Subtype.val h))
    haveI : Finite (tors E₀.toAffine.Point N) :=
      Nat.finite_of_card_ne_zero (by rw [hcard₀]; exact pow_ne_zero 2 hN0)
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hcard₀]
      exact le_of_eq hfull.symm)
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

  obtain ⟨H₁, -⟩ := mapCyc_surjective hN0 hθ hθs (cycOf g₀ hg₀)
  let ι : F →ₐ[K] M := (ΦX H₁).1
  have hι : ι jF = t := (ΦX H₁).2

  obtain ⟨-, hBi, hBii, hBiii, hBiv⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K jF t E₀.j ι hι hfin hgal
      hint W₀ hW₀

  let D : (M ≃ₐ[K⟮t⟯] M) → Prop := fun σ => SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀
  let act : (M ≃ₐ[K⟮t⟯] M) → ((E.baseChange M).toAffine.Point →+ (E.baseChange M).toAffine.Point) :=
    fun σ => WeierstrassCurve.Affine.Point.map (σ : M →ₐ[K⟮t⟯] M)
  have hact : ∀ σ, Function.Injective (act σ) := fun σ =>
    WeierstrassCurve.Affine.Point.map_injective (W' := E) (σ : M →ₐ[K⟮t⟯] M)
  have hσt : ∀ σ : M ≃ₐ[K⟮t⟯] M, σ t = t := fun σ => σ.commutes tk
  let actX : (M ≃ₐ[K⟮t⟯] M) → X → X := fun σ ψ =>
    ⟨((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ.1, by
      show σ (ψ.1 jF) = t
      rw [ψ.2, hσt]⟩
  have hnat : ∀ σ (H : CycSub (E.baseChange M).toAffine.Point N),
      ΦX (mapCyc (act σ) H (hact σ).injOn) = actX σ (ΦX H) := by
    intro σ H
    apply Subtype.ext
    rw [ΦX_val]
    exact hnatA σ H (mapCyc (act σ) H (hact σ).injOn) rfl

  have hequiv : ∀ σ (hσ : D σ) (P : (E.baseChange M).toAffine.Point),
      θ (act σ P) = autPt (ρ σ) (hρE σ hσ) (θ P) :=
    fun σ hσ P => ((autPt_eq_iff_heq _ _ _ _).mpr (hequivC σ hσ P)).symm
  have hsurj : ∀ (γ : VariableChange K) (hγ : γ • E₀ = E₀), ∃ σ, D σ ∧
      ((∀ P, θ (act σ P) = autPt γ hγ (θ P)) ∨ (∀ P, θ (act σ P) = -autPt γ hγ (θ P))) := by
    intro γ hγ
    obtain ⟨σ, hσ, h⟩ := hsurjC γ hγ
    refine ⟨σ, hσ, ?_⟩
    rcases h with h | h
    · exact Or.inl fun P => ((autPt_eq_iff_heq _ _ _ _).mpr (h P)).symm
    · refine Or.inr fun P => ?_
      have := (autPt_eq_iff_heq γ hγ (θ P) _).mpr (h P)
      rw [this, neg_neg]

  let π : X → Place K F := fun ψ => W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2)
  have hπS : ∀ ψ, π ψ ∈ S := fun ψ => (hS _).mpr (hBi ψ.1 ψ.2)
  have hπsurj : ∀ P ∈ S, ∃ ψ, π ψ = P := by
    intro P hP
    obtain ⟨ψ, hψ, h⟩ := hBii P ((hS P).mp hP)
    exact ⟨⟨ψ, hψ⟩, h⟩
  have hπfib : ∀ ψ ψ' : X, π ψ = π ψ' ↔ ∃ σ, D σ ∧ ψ' = actX σ ψ := by
    intro ψ ψ'
    rw [show (π ψ = π ψ') = (W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2) =
      W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2)) from rfl, hBiii ψ.1 ψ'.1 ψ.2 ψ'.2]
    refine exists_congr fun σ => and_congr_right fun _ => ?_
    rw [Subtype.ext_iff]
  let e : Place K F → ℤ := fun P => P.ord (jF - algebraMap K F E₀.j)
  have hπe : ∀ ψ : X, e (π ψ) = Nat.card {ψ' // π ψ' = π ψ} := fun ψ => hBiv ψ.1 ψ.2

  have hbase : ∀ a : K, SemilinearAut.baseAut frF a = SemilinearAut.baseAut frM a := by
    intro a
    have h1 := SemilinearAut.smul_algebraMap frF a
    rw [hfrK] at h1
    have h2 := SemilinearAut.smul_algebraMap frM a
    rw [hfrMK] at h2
    rw [← (algebraMap K F).injective h1, ← (algebraMap K M).injective h2]

  have hfr₀inj : Set.InjOn fr₀ (tors E₀.toAffine.Point N) :=
    ModularCurve.FrobOrbit.PointLaw.injOn_tors_of_forall_some q hfr N fr₀ hfr₀

  have hfr₀N : ∀ (H : CycSub E₀.toAffine.Point N) (h : Set.InjOn fr₀ H.1),
      mapCyc fr₀ H h = ModularCurve.FrobOrbit.frobSubN q hfr N H :=
    ModularCurve.FrobOrbit.PointLaw.mapCyc_eq_frobSubN_of_forall_some q hfr N fr₀ hfr₀

  have hπfr : ∀ (H : CycSub (E.baseChange M).toAffine.Point N) (hH : Set.InjOn frE H.1),
      π (ΦX (mapCyc frE H hH)) = frF • π (ΦX H) := by
    intro H hH
    have htw : ∀ x : F, (ΦX (mapCyc frE H hH)).1 (frF • x) = frM • (ΦX H).1 x := by
      refine ModularCurve.FrobTwist.twist_of_forall_mem frF frM hbase (ΦX H).1
        (ΦX (mapCyc frE H hH)).1 {y : F | (y : LaurentSeries K) ∈ divisorExpansionsC K N} ?_ hgen
      intro y hy
      rw [hfrd y hy]
      obtain ⟨d, hd0, hd, hyd⟩ := hy
      haveI := hd0
      have hy' : y = ⟨qExpand K d (jqModC K), jqModCd_mem_full K N hd⟩ := Subtype.ext hyd
      rw [hy', ΦX_val, ΦX_val]
      exact hF5 H (mapCyc frE H hH) rfl d hd
    exact ModularCurve.FrobTwist.restrictAlong_twist frF frM W₀ hfrMW _ _ _ _ htw

  obtain ⟨f, hfS, hfsurj, hfib, hord, hfrob⟩ := assemble_fr hN0 θ hθ hθs D act hact ρ hρE hequiv hsurj
    ΦX actX hnat π S hπS hπsurj hπfib e hπe frE fr₀ hfr₀inj ε hε (fun P hP => hsign P hP)
    (fun P => frF • P) hπfr
  refine ⟨f, hfS, hfsurj, fun H H' => (hfib H H').trans Iff.rfl, hord, fun H => ?_⟩
  have h₀ : Set.InjOn fr₀ H.1 := fun P hP Q hQ h => hfr₀inj (subset_tors _ hP) (subset_tors _ hQ) h
  rw [← hfr₀N H h₀]
  exact hfrob H h₀

end ModularCurve.TorsionOrbit
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

namespace ModularCurve
p2m_export "ModularCurve" "coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut.coeffMap_jqModC coeffSemilinearAut coe_coeffSemilinearAut_smul arithFrobC baseAut_arithFrobC_apply jqModC modularFunctionFieldC jqModC_mem qExpand jGeomGen mem_restrictAlong_iff Gamma0Pair Gamma0Pair.Step ModuliPoint ModuliPoint.j ModuliPoint.j_mk Point.heq_zero Point.heq_some Point.heq_nsmul mapPoint_vcInvFun_heq Gamma0Pair.map ModuliPoint.map ModuliPoint.map_mk coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand modularFunctionFieldC_eq_modularFunctionFieldFullC finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero exists_frobeniusSemilinear_torsionModel_ofJ_univ"
namespace FrobOrbitMap
p2m_open "ModularCurve~CycSub"

section Main

open WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

private theorem orbitMaps_arithFrobC_compat
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N) (K : Type u) [Field K]
    [DecidableEq K] [CharP K q] [IsAlgClosed K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (hfr : E₀.map (frobenius K q) = E₀) :
    ∃ (f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
          Place K (modularFunctionFieldC K N))
      (g : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
          ModuliPoint N K),
      (∀ H, 0 < (f H).ord (jGeomGen K N -
          algebraMap K (modularFunctionFieldC K N) E₀.j)) ∧
      (∀ w : Place K (modularFunctionFieldC K N),
        0 < w.ord (jGeomGen K N -
          algebraMap K (modularFunctionFieldC K N) E₀.j) → ∃ H, f H = w) ∧
      (∀ H H', f H = f H' ↔ ∃ γ : WeierstrassCurve.VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1,
          HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) T') ∧
      (∀ H H', g H = g H' ↔ f H = f H') ∧
      (∀ H, ModuliPoint.j (g H) = E₀.j) ∧
      (∀ x : ModuliPoint N K, ModuliPoint.j x = E₀.j → ∃ H, g H = x) ∧
      (∀ H, ∃ H', f H' = arithFrobC q K N • f H ∧
        g H' = ModuliPoint.map (frobenius K q) (g H)) := by
  classical
  have hN : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)
  have hfin := ModularCurve.PlacesOrbit.finite_ord_fibre K N hN E₀.j
  have hdef : (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) = jGeomGen K N := rfl

  have hfrK : ∀ a : K, arithFrobC q K N • algebraMap K (modularFunctionFieldC K N) a =
      algebraMap K (modularFunctionFieldC K N) (a ^ q) :=
    ModularCurve.LevelFieldFrobenius.arithFrobC_smul_algebraMap q K N
  have hfrd : ∀ y : modularFunctionFieldC K N, (y : LaurentSeries K) ∈ divisorExpansionsC K N →
      arithFrobC q K N • y = y :=
    ModularCurve.LevelFieldFrobenius.arithFrobC_smul_of_mem_divisorExpansionsC q K N
  have hgen : ∀ x : modularFunctionFieldC K N,
      x ∈ Subfield.closure (Set.range (algebraMap K (modularFunctionFieldC K N)) ∪
        {y : modularFunctionFieldC K N | (y : LaurentSeries K) ∈ divisorExpansionsC K N}) :=
    fun x => ModularCurve.TorsionOrbit.mem_closure_C q N K hqN x
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := ModularCurve.TorsionOrbit.sigma_orbitMap_at K q N hN E₀ hfr
    (modularFunctionFieldC K N) (modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN).symm
    (jqModC_mem K N) (arithFrobC q K N) hfrK hfrd hgen hfin.toFinset
    (fun P => by rw [hdef]; exact hfin.mem_toFinset)
  refine ⟨f, ModularCurve.CyclicModuli.orbitMap E₀, ?_, ?_, hf3, ?_, ?_, ?_, ?_⟩
  · exact fun H => hfin.mem_toFinset.mp (hf1 H)
  · exact fun w hw => hf2 w (hfin.mem_toFinset.mpr hw)
  · exact ModularCurve.PlacesOrbit.jointFibre_iff E₀ f (ModularCurve.CyclicModuli.orbitMap E₀) hf3
      (ModularCurve.CyclicModuli.orbitMap_eq_orbitMap_iff E₀)
  · exact fun H => ModularCurve.CyclicModuli.j_orbitMap E₀ H
  · intro x hx
    obtain ⟨T, hT, hc, hcard, hx'⟩ := ModularCurve.CyclicModuli.exists_generator_moduliPoint_eq E₀ x hx
    refine ⟨⟨AddSubgroup.zmultiples T, hc, hcard⟩, ?_⟩
    rw [ModularCurve.CyclicModuli.orbitMap_eq_moduliOf E₀ _ hT rfl]
    exact hx'
  · intro H
    refine ⟨ModularCurve.FrobOrbit.frobSubN q hfr N H, hf5 H, ?_⟩

    obtain ⟨T, hT, hHT⟩ := ModularCurve.CyclicModuli.exists_generator_of_isAddCyclic_card H.1 N H.2.1 H.2.2
    have hT' : addOrderOf (ModularCurve.FrobOrbit.frobPt q hfr T) = N :=
      (ModularCurve.FrobOrbit.addOrderOf_frobPt q hfr T).trans hT
    have hHT' : (ModularCurve.FrobOrbit.frobSubN q hfr N H).1 =
        AddSubgroup.zmultiples (ModularCurve.FrobOrbit.frobPt q hfr T) := by
      rw [ModularCurve.FrobOrbit.coe_frobSubN, hHT, ModularCurve.FrobOrbit.frobSub_zmultiples]
    rw [ModularCurve.CyclicModuli.orbitMap_eq_moduliOf E₀ H hT hHT, ModularCurve.CyclicModuli.orbitMap_eq_moduliOf E₀ _ hT' hHT']
    exact (ModularCurve.FrobOrbit.moduliPoint_map_frobenius_mk q hfr T hT).symm

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

end ModularCurve.FrobOrbitMap
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"
p2m_reactivate "P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.CyclicModuli P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.FrobOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ.ModularCurve.TorsionOrbit.Assembly"

theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K]
    [DecidableEq K] [CharP K q] [IsAlgClosed K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (hfr : E₀.map (frobenius K q) = E₀) :
    ∃ (f : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
          AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N))
      (g : {H : AddSubgroup E₀.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
          ModularCurve.ModuliPoint N K),
      (∀ H, 0 < (f H).ord (ModularCurve.jGeomGen K N -
          algebraMap K (ModularCurve.modularFunctionFieldC K N) E₀.j)) ∧
      (∀ w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldC K N),
        0 < w.ord (ModularCurve.jGeomGen K N -
          algebraMap K (ModularCurve.modularFunctionFieldC K N) E₀.j) → ∃ H, f H = w) ∧
      (∀ H H', f H = f H' ↔ ∃ γ : WeierstrassCurve.VariableChange K, γ • E₀ = E₀ ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1,
          HEq (WeierstrassCurve.Affine.Point.vcInvFun γ E₀.toAffine T) T') ∧
      (∀ H H', g H = g H' ↔ f H = f H') ∧
      (∀ H, ModularCurve.ModuliPoint.j (g H) = E₀.j) ∧
      (∀ x : ModularCurve.ModuliPoint N K, ModularCurve.ModuliPoint.j x = E₀.j → ∃ H, g H = x) ∧
      (∀ H, ∃ H', f H' = ModularCurve.arithFrobC q K N • f H ∧
        g H' = ModularCurve.ModuliPoint.map (frobenius K q) (g H)) :=
  ModularCurve.FrobOrbitMap.orbitMaps_arithFrobC_compat q N hqN K E₀ hfr

end S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
end P2MW
export P2MW.S_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ (solution)
