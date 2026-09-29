-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6d90557c-b1e6-5681-afe5-949827c73442

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_piFin_range_localizes_of_jqModC_mem
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_exists_numberField_presentation_of_neZero
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.ModularCurve.NodeLocalized ModularCurve.CharPModel"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

noncomputable section

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.ord_nonneg_of_mem_pn" "AlgebraicCurve.Place.ord_nonneg_of_mem_pn"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.mem_of_ord_nonneg_pn" "AlgebraicCurve.Place.mem_of_ord_nonneg_pn"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.ord_algebraMap_pn" "AlgebraicCurve.Place.ord_algebraMap_pn"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.ne_zero_of_ord_pos_pn" "AlgebraicCurve.Place.ne_zero_of_ord_pos_pn"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn" "AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn {K F : Type*} [Field K]
    [Field F] [Algebra K F] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm
  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_pn hsub h0]
    have hnn := v.ord_nonneg_of_mem_pn hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_pn"

private theorem _root_.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {g : F} {c : K} (h : 0 < v.ord (g - algebraMap K F c)) :
    v.HasValue g c := by
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg_pn (v.ne_zero_of_ord_pos_pn h) h.le
  have hg : g ∈ v.toValuationSubring := by
    have h' := add_mem hsub (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at h'
  exact (v.hasValue_iff_eq_or_ord_sub_pos_pn hg c).mpr (Or.inr h)

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn" "AlgebraicCurve.Place.hasValue_of_ord_sub_pos_pn"
namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

omit [Fact (Nat.Prime q)] [CharP k q] in

theorem penA_hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x y : F} {a b : K} (hx : w.HasValue x a) (hy : w.HasValue y b) : w.HasValue (x + y) (a + b) := by
  obtain ⟨hxm, hxr⟩ := hx
  obtain ⟨hym, hyr⟩ := hy
  refine ⟨add_mem hxm hym, ?_⟩
  have e : (⟨x + y, add_mem hxm hym⟩ : w.toValuationSubring) = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
  rw [e, map_add, hxr, hyr, map_add]

omit [Fact (Nat.Prime q)] [CharP k q] in

theorem penA_hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x : F} {a : K} (hx : w.HasValue x a) : w.HasValue (-x) (-a) := by
  obtain ⟨hxm, hxr⟩ := hx
  refine ⟨neg_mem hxm, ?_⟩
  have e : (⟨-x, neg_mem hxm⟩ : w.toValuationSubring) = -⟨x, hxm⟩ := rfl
  rw [e, map_neg, hxr, map_neg]

theorem pnN_coe_algebraMap {L : Type*} [Field L] (E : IntermediateField L (LaurentSeries L))
    (x : L) : ((algebraMap L E x : E) : LaurentSeries L) = algebraMap L (LaurentSeries L) x := by
  rw [IsScalarTower.algebraMap_apply L E (LaurentSeries L) x]
  rfl

theorem penC_residue_surjective [IsAlgClosed k] (v : Place k (modularFunctionFieldC k N)) :
    Function.Surjective (algebraMap k v.ResidueField) := by
  have h1 : Module.finrank k v.ResidueField = 1 := place_deg_eq_one_of_isAlgClosed k N v
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp h1 x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem penC_exists_j_value (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a₀ : A, 0 < w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a₀ : AlgebraicClosure ℚ)) := by
  by_contra hcon
  have hle : ∀ a : A, w.ord (CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
    fun a => not_lt.mp (fun h => hcon ⟨a, h⟩)
  have hpole := P.d0_j_pole w hle
  rw [hw] at hpole
  have hnn : (0 : ℤ) ≤ v.ord (jGeomGen k N) := v.ord_nonneg_of_mem_pn hv1
  exact absurd hnn (not_le.mpr hpole)

theorem penC_sub_mem_nonunits_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : u.HasValue g c) :
    g - algebraMap K F c ∈ u.toValuationSubring.nonunits := by
  have hmem : g - algebraMap K F c ∈ u.toValuationSubring := sub_mem h.mem (u.algebraMap_mem' c)
  have hres : IsLocalRing.residue u.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = 0 := by
    have e : (⟨g - algebraMap K F c, hmem⟩ : u.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K u.toValuationSubring c := rfl
    rw [e, map_sub, h.residue_eq, u.residue_algebraMap, sub_self]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)

theorem penC_hasValue_of_sub_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : Place K F) {g : F} {c : K} (h : g - algebraMap K F c ∈ u.toValuationSubring.nonunits) :
    u.HasValue g c := by
  by_cases hgc : g = algebraMap K F c
  · rw [hgc]
    exact u.hasValue_algebraMap c
  · have hne : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hgc
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
    exact u.hasValue_of_ord_sub_pos_pn ((u.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax)

theorem penC_red_eq_zero_of_mem_maximalIdeal (hred : Function.Surjective red) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  rw [← RingHom.mem_ker, hker]
  exact ha

theorem penC_not_hasValue_zero_of_ne {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (hc : c ≠ 0) : ¬ u.HasValue g 0 :=
  fun h0 => hc (h.unique h0)

theorem penC_frob_mem_nonunits (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits) :
    frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x :=
    ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    intro hmem'
    have h1 := (frobOnPlacesGeomLevel k N data hKr u).ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀] at hinv

  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := by
    intro h0
    apply hinv
    rw [h0, inv_zero]
    exact zero_mem _
  have hFmem : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring :=
    (u.toValuationSubring.mem_or_inv_mem _).resolve_right hinv
  have hFord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := by
    by_contra hle
    apply hinv
    apply u.mem_of_ord_nonneg_pn (inv_ne_zero hFx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hFmem, (u.mem_maximalIdeal_iff_ord_pos hFx0 hFmem).mpr hFord⟩

theorem penC_mem_nonunits_frob_of (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N}
    (hx : frobeniusGeomLevel k N data hKr x ∈ u.toValuationSubring.nonunits) :
    x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.nonunits := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨zero_mem _, Ideal.zero_mem _⟩
  have hFx0 : frobeniusGeomLevel k N data hKr x ≠ 0 := (map_ne_zero _).mpr hx0
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  have hord : 0 < u.ord (frobeniusGeomLevel k N data hKr x) := (u.mem_maximalIdeal_iff_ord_pos hFx0 hmem).mp hmax

  have hinv : x⁻¹ ∉ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := by
    rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀]
    intro hmem'
    have h1 := u.ord_nonneg_of_mem_pn hmem'
    rw [Place.ord_inv] at h1
    omega
  have hxmem : x ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring :=
    ((frobOnPlacesGeomLevel k N data hKr u).toValuationSubring.mem_or_inv_mem x).resolve_right hinv
  have hxord : 0 < (frobOnPlacesGeomLevel k N data hKr u).ord x := by
    by_contra hle
    apply hinv
    apply (frobOnPlacesGeomLevel k N data hKr u).mem_of_ord_nonneg_pn (inv_ne_zero hx0)
    rw [Place.ord_inv]
    omega
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
    ⟨hxmem, ((frobOnPlacesGeomLevel k N data hKr u).mem_maximalIdeal_iff_ord_pos hx0 hxmem).mpr hxord⟩

theorem penC_isAffine_of_isAffine_frob (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u)) : IsAffineGeomPlace k N u := by
  obtain ⟨hj, hjN⟩ := h
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  refine ⟨?_, ?_⟩
  · have h1 : jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hj
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1
  · have h1 : jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring := hjN
    rw [mem_frobOnPlacesGeomLevel_iff] at h1
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2] at h1
    exact u.toValuationSubring.mem_of_pow_mem' hq h1

theorem penC_isAffine_frob_of_isAffine (u : Place k (modularFunctionFieldC k N))
    (h : IsAffineGeomPlace k N u) : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr u) := by
  obtain ⟨hj, hjN⟩ := h
  refine ⟨?_, ?_⟩
  · show jGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jGeomGen k N) = jGeomGen k N ^ q := frobeniusGeomLevel_jq k N data hKr
    rw [h2]
    exact pow_mem hj q
  · show jNGeomGen k N ∈ (frobOnPlacesGeomLevel k N data hKr u).toValuationSubring
    rw [mem_frobOnPlacesGeomLevel_iff]
    have h2 : frobeniusGeomLevel k N data hKr (jNGeomGen k N) = jNGeomGen k N ^ q := frobeniusGeomLevel_jqN k N data hKr
    rw [h2]
    exact pow_mem hjN q

theorem penC_reduceSnd_affine (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    IsAffineGeomPlace k N (P.reduceSnd W) := by
  rcases P.d1 W with h | h
  · have h₁ : P.reduceFst W = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W) := h
    rw [hW] at h₁
    refine penC_isAffine_of_isAffine_frob (data := data) (hKr := hKr) _ ?_
    rw [← h₁]
    exact hvaff
  · have h₁ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst W) = P.reduceSnd W := h
    rw [hW] at h₁
    rw [← h₁]
    exact penC_isAffine_frob_of_isAffine v hvaff

omit [Fact q.Prime] [NeZero N] in

theorem penC_ramificationIndexAlong_pos' (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    0 < Place.ramificationIndexAlong φ W := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact W.ramificationIndex_pos (F := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

omit [Fact q.Prime] [NeZero N] in

theorem penC_hasValue_of_restrictAlong
    (φ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      →ₐ[AlgebraicClosure ℚ] laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    (hφ : φ.toRingHom.IsIntegral) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} {c : AlgebraicClosure ℚ}
    (h : (W.restrictAlong φ hφ).HasValue x c) : W.HasValue (φ x) c := by
  by_cases hxc : x = algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
  · rw [hxc, φ.commutes]
    exact W.hasValue_algebraMap c
  · have hne : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c ≠ 0 :=
      sub_ne_zero.mpr hxc
    have hmem : x - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c
        ∈ (W.restrictAlong φ hφ).toValuationSubring :=
      sub_mem h.mem ((W.restrictAlong φ hφ).algebraMap_mem' c)
    have hmax : (⟨_, hmem⟩ : (W.restrictAlong φ hφ).toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      ValuationSubring.coe_mem_nonunits_iff.mp (penC_sub_mem_nonunits_of_hasValue _ h)
    have hord := ((W.restrictAlong φ hφ).mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax
    apply W.hasValue_of_ord_sub_pos_pn
    rw [← φ.commutes, ← map_sub, W.ord_restrictAlong φ hφ]
    exact mul_pos (by exact_mod_cast penC_ramificationIndexAlong_pos' φ hφ W) hord

theorem penC_hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (n : ℕ) : u.HasValue (g ^ n) (c ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact u.hasValue_one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem penC_mem_nonunits_of_pow_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {n : ℕ} (hn : n ≠ 0) (h : g ^ n ∈ u.toValuationSubring.nonunits) : g ∈ u.toValuationSubring.nonunits := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  have hg : g ∈ u.toValuationSubring := u.toValuationSubring.mem_of_pow_mem' hn hmem
  have hpow : (⟨g ^ n, hmem⟩ : u.toValuationSubring) = (⟨g, hg⟩ : u.toValuationSubring) ^ n := by
    apply Subtype.ext
    simp
  rw [hpow] at hmax
  exact ValuationSubring.coe_mem_nonunits_iff.mpr
    ((IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem n hmax)

theorem penC_hasValue_frob_apply (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t) : u.HasValue (frobeniusGeomLevel k N data hKr x) t := by
  have h1 := penC_frob_mem_nonunits u (penC_sub_mem_nonunits_of_hasValue _ h)
  rw [map_sub, AlgHom.commutes] at h1
  exact penC_hasValue_of_sub_mem_nonunits u h1

theorem penC_hasValue_frobOnPlaces (u : Place k (modularFunctionFieldC k N)) {x : modularFunctionFieldC k N} {t : k}
    (h : u.HasValue (frobeniusGeomLevel k N data hKr x) t) : (frobOnPlacesGeomLevel k N data hKr u).HasValue x t := by
  have h1 := penC_sub_mem_nonunits_of_hasValue u h
  rw [← AlgHom.commutes (frobeniusGeomLevel k N data hKr) t, ← map_sub] at h1
  exact penC_hasValue_of_sub_mem_nonunits _ (penC_mem_nonunits_frob_of u h1)

theorem pnN_const_mem (a : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red := by
  rw [pnN_coe_algebraMap]
  exact CharPReduction.subring_le_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)
    (CharPReduction.constSeries_mem_modularRing N A.toSubring ⟨(a : AlgebraicClosure ℚ), a.2⟩)

noncomputable def packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)).coeff n, x.2 n⟩
  isPWO_support' := (x : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

theorem coeffMap_subtype_packA_g (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (packA_g A x) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n
  rfl

theorem coeffMap_residue_packA_g (A : ValuationSubring (AlgebraicClosure ℚ)) (red : A →+* k)
    (x : CharPReduction.integralCoeffs A.toSubring) :
    coeffMap red (packA_g A x) = CharPReduction.coeffRed A.toSubring red x := by
  ext n
  rw [coeffMap_coeff, CharPReduction.coeffRed_coeff]
  rfl

theorem penC_redBar_comp_residue : R.redBar.comp (IsLocalRing.residue A) = red :=
  RingHom.ext fun a => R.redBar_residue a

theorem penC_good_residue_of_coe_eq (g : modularFunctionFieldBar (N * q)) (y : LaurentSeries A)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : g ∈ R.R₁.integers, ((R.residue₁ ⟨g, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := hg ▸ g.2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  have hgeq : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) = g := Subtype.ext hg.symm
  have key : ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers,
      ((R.residue₁ ⟨_, h⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red y := by
    refine ⟨h, ?_⟩
    rw [R.residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap, penC_redBar_comp_residue]
  exact hgeq ▸ key

theorem penC_bfin_coe_mem_integralCoeffs (fm : FibreModel N A q k red) (b : fm.BFin) :
    ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseFin A N _ (fm.integralFin b)

theorem penC_residue_alpha (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = fm.piFin b := by
  have hint := penC_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (packA_g A ⟨_, hint⟩) := by
    rw [coe_heckeAlphaBar, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_residue_packA_g, FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

theorem penC_residue_beta (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (fm.piFin b) := by
  have hint := penC_bfin_coe_mem_integralCoeffs fm b
  have hcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffMap A.subtype (qExpand A q (packA_g A ⟨_, hint⟩)) := by
    rw [coe_heckeBetaBar, coeffMap_qExpand, coeffMap_subtype_packA_g]
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext (hres.trans ?_)⟩
  rw [coeffMap_qExpand, coeffMap_residue_packA_g, frobeniusGeomLevel_apply_coe,
    FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hint]

theorem penC_residue_const (a : A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  have hcoe : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (HahnSeries.single 0 a) := by
    rw [pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single, coeffMap_single]
    rfl
  obtain ⟨h, hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  refine ⟨h, Subtype.ext ?_⟩
  rw [hres, coeffMap_single, pnN_coe_algebraMap, algebraMap_laurentSeries_eq_single]

theorem penC_bfin_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hv1 : jGeomGen k N ∈ v.toValuationSubring) (b : fm.BFin)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w = v) :
    ∃ a : A, w.HasValue (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a₀, ha₀⟩ := penC_exists_j_value v hv1 _ hw

  have hreg : fm.piFin b ∈ v.toValuationSubring := (FibreModel.piFin_range_localizes_of_jqModC_mem N A q hqN k red fm v hv1).1 b
  obtain ⟨c, hc, -⟩ := v.exists_hasValue_of_surjective (penC_residue_surjective v) hreg
  obtain ⟨a₁, rfl⟩ := hred c

  set b₁ : fm.BFin := b - ⟨CharPModel.constantsHom N A a₁, fm.constFin_mem a₁⟩ with hb₁
  have hpi : (fm.piFin b₁ : modularFunctionFieldC k N)
      = fm.piFin b - algebraMap k (modularFunctionFieldC k N) (red a₁) := by
    rw [hb₁, map_sub, fm.piFin_const]
  have hnu : (fm.piFin b₁ : modularFunctionFieldC k N) ∈ v.toValuationSubring.nonunits := by
    rw [hpi]
    exact penC_sub_mem_nonunits_of_hasValue v hc
  have hsp : fm.spPlace hred dataAll hsep w = v := by
    rw [← hP]
    exact hw
  rw [← hsp] at hnu
  obtain ⟨a₂, ha₂m, ha₂⟩ := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep _ a₀ ha₀ b₁).mp hnu

  have hdiff : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
      = (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
            (a₂ : AlgebraicClosure ℚ) := by
    have hcoe : ((a₁ + a₂ : A) : AlgebraicClosure ℚ) = (a₁ : AlgebraicClosure ℚ) + a₂ := rfl
    have hb₁' : (b₁ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        = (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
              (a₁ : AlgebraicClosure ℚ) := by
      rw [hb₁]
      push_cast
      rfl
    rw [hcoe, hb₁', map_add, sub_sub]
  have ha₂' : (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          ((a₁ + a₂ : A) : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
    rw [hdiff]
    exact ha₂
  have hval_w : w.HasValue
      (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ((a₁ + a₂ : A) : AlgebraicClosure ℚ) :=
    penC_hasValue_of_sub_mem_nonunits _ ha₂'
  refine ⟨a₁ + a₂, hval_w, ?_⟩

  rw [map_add, penC_red_eq_zero_of_mem_maximalIdeal hred ha₂m, add_zero]
  exact hc

theorem penC_alpha_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeAlphaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      v.HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hav⟩ := penC_bfin_values fm hred dataAll hsep hP hqN v hvaff.1 b
    (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hW
  exact ⟨a, penC_hasValue_of_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W haw, hav⟩

theorem penC_beta_values [IsAlgClosed k] (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hP : P.sp = fm.spPlace hred dataAll hsep) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N)) (hvaff : IsAffineGeomPlace k N v) (b : fm.BFin)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hW : P.reduceFst W = v) :
    ∃ a : A, W.HasValue (heckeBetaBar (AlgebraicClosure ℚ) N q
        (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) (a : AlgebraicClosure ℚ) ∧
      (P.reduceSnd W).HasValue (fm.piFin b) (red a) := by
  obtain ⟨a, haw, hau⟩ := penC_bfin_values fm hred dataAll hsep hP hqN (P.reduceSnd W) (penC_reduceSnd_affine v hvaff W hW).1 b
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) rfl
  exact ⟨a, penC_hasValue_of_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W haw, hau⟩

theorem atkinLehnerBar_heckeBetaBar_g (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q t) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q t := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).2
  exact AlgHom.congr_fun hlegs t

theorem penC_beta_mem_snd (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin) :
    heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers := by
  obtain ⟨hαI, -⟩ := penC_residue_alpha R fm b
  rw [R.mem_integersSnd_iff, atkinLehnerBar_heckeBetaBar_g hqN]
  exact (R.mem_integersFst_iff _).mp hαI

theorem penC_residue₂_beta (hqN : ¬ q ∣ N) (fm : FibreModel N A q k red) (b : fm.BFin)
    (h : heckeBetaBar (AlgebraicClosure ℚ) N q (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ = fm.piFin b := by
  obtain ⟨hαI, hαres⟩ := penC_residue_alpha R fm b
  have hAL := atkinLehnerBar_heckeBetaBar_g hqN (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
  have h2 : R.residue₂ ⟨_, h⟩ = R.residue₁ ⟨_, hαI⟩ := by
    show R.ι (R.R₂.residue ⟨_, h⟩) = R.ι (R.R₁.residue ⟨_, hαI⟩)
    rw [R.residue₂_eq]
    exact congrArg R.ι (congrArg R.R₁.residue (Subtype.ext hAL))
  rw [h2, hαres]

section FrobeniusOnPlaces

theorem penC_frob_injective [IsAlgClosed k] {w w' : Place k (modularFunctionFieldC k N)}
    (h : frobOnPlacesGeomLevel k N data hKr w = frobOnPlacesGeomLevel k N data hKr w') : w = w' := by
  rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w,
    ← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w'] at h
  exact smul_left_cancel _ h

theorem penC_frob_not_mem_ssPlaces [IsAlgClosed k] [DecidableEq k] (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) (hss : v ∉ ssPlaces q N k) :
    frobOnPlacesGeomLevel k N data hKr v ∉ ssPlaces q N k := by
  intro h
  apply hss
  have h2 := ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k _ h
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr, hv] at h2
  exact h2

theorem penC_reduceSnd_eq_of_reduceFst_eq_frob [IsAlgClosed k] (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : P.reduceFst V = frobOnPlacesGeomLevel k N data hKr v) : P.reduceSnd V = v := by
  rcases P.d1 V with h | h
  · have h' : P.reduceFst V = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) := h
    exact penC_frob_injective (h'.symm.trans hV)
  · have h' : frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) = P.reduceSnd V := h
    rw [← h', hV, hv]

end FrobeniusOnPlaces

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure"
p2m_open "ModularCurve.NodeLocalized ModularCurve~jBar"

section Basics

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem c4_mem_coeffSubring_iff {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := by
  simp only [coeffSubring, Subring.mem_inf]
  exact Iff.rfl

theorem c4_constSeries_coeffSubring_apply (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := rfl

theorem c4_algebraMap_mem_fieldOver (M : ℕ) [NeZero M] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem c4_jqModC_mem_fieldOver (M : ℕ) [NeZero M] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem c4_jqNModC_mem_fieldOver (M : ℕ) [NeZero M] : jqNModC (AlgebraicClosure ℚ) M ∈ fieldOver M K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem c4_jqModC_mem_jRing : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem c4_constSeries_mem_jRing (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem c4_jRing_le_fieldOver (M : ℕ) [NeZero M] : jRing A K ≤ (fieldOver M K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact c4_algebraMap_mem_fieldOver K M ((c4_mem_coeffSubring_iff A K).mp a.2).2
  · exact c4_jqModC_mem_fieldOver K M

variable {A K} in
theorem c4_coeffSubring_mono {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    coeffSubring A K ≤ coeffSubring A K' :=
  inf_le_inf_left _ (fun _ hx => h hx)

variable {A K} in
theorem c4_jRing_mono {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') : jRing A K ≤ jRing A K' := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact c4_constSeries_mem_jRing A K' ⟨a, c4_coeffSubring_mono h a.2⟩
  · exact c4_jqModC_mem_jRing A K'

variable {K} in
theorem c4_fieldOver_mono (M : ℕ) [NeZero M] {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K') :
    fieldOver M K ≤ fieldOver M K' := by
  rw [fieldOver, Subfield.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨a, h a.2⟩, rfl⟩)
  · exact Subfield.subset_closure (Or.inr hx)

variable {A K} in

theorem c4_jIntegralClosure_mono (M : ℕ) [NeZero M] {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ K')
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ jIntegralClosure M A K) : x ∈ jIntegralClosure M A K' := by
  refine ⟨c4_fieldOver_mono M h hx.1, ?_⟩
  obtain ⟨p, hp, hpx⟩ := hx.2
  refine ⟨p.map (Subring.inclusion (c4_jRing_mono h)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

end Basics

end ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section LevelM

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M]

theorem c4_coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ n x)
      = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) x) := by
  ext m
  by_cases hm : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := hm
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hm, qExpand_coeff_of_not_dvd n _ hm, map_zero]

theorem c4_coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
  exact map_jqModC _

theorem c4_coe_jBar : ((CharPModel.jBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := c4_coeffEmb_jq

theorem c4_coe_jNBar : ((CharPModel.jNBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) M := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) = qExpand (AlgebraicClosure ℚ) M (jqModC (AlgebraicClosure ℚ))
  rw [c4_coeffEmb_qExpand, c4_coeffEmb_jq]

theorem c4_jqModC_mem_bar : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar M := by
  rw [← c4_coe_jBar M]; exact SetLike.coe_mem _

theorem c4_jqNModC_mem_bar : jqNModC (AlgebraicClosure ℚ) M ∈ modularFunctionFieldBar M := by
  rw [← c4_coe_jNBar M]; exact SetLike.coe_mem _

theorem c4_fieldOver_le_bar : (fieldOver M K : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ modularFunctionFieldBar M := by
  intro x hx
  change x ∈ (modularFunctionFieldBar M).toSubfield
  refine (Subfield.closure_le.mpr ?_) hx
  rintro y (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar M).algebraMap_mem (a : AlgebraicClosure ℚ)
  · exact c4_jqModC_mem_bar M
  · exact c4_jqNModC_mem_bar M

variable {A K M} in
theorem c4_bar_mem_of_mem_C {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ jIntegralClosure M A K) :
    x ∈ modularFunctionFieldBar M := c4_fieldOver_le_bar K M hx.1

theorem c4_jRing_le_map_affineBaseFin :
    jRing A K ≤ (CharPModel.affineBaseFin M A).map (modularFunctionFieldBar M).val.toRingHom := by
  rw [jRing, Subring.closure_le]
  rintro y (⟨a, rfl⟩ | rfl)
  · exact ⟨CharPModel.constantsHom M A ⟨(a : AlgebraicClosure ℚ), ((c4_mem_coeffSubring_iff A K).mp a.2).1⟩,
      Subring.subset_closure (Or.inl ⟨_, rfl⟩), rfl⟩
  · exact ⟨CharPModel.jBar M, Subring.subset_closure (Or.inr rfl), c4_coe_jBar M⟩

variable {A K M} in
theorem c4_jRing_to_affineBaseFin {y : LaurentSeries (AlgebraicClosure ℚ)} (hy : y ∈ jRing A K)
    (hy' : y ∈ modularFunctionFieldBar M) :
    (⟨y, hy'⟩ : modularFunctionFieldBar M) ∈ CharPModel.affineBaseFin M A := by
  obtain ⟨z, hz, hzy⟩ := c4_jRing_le_map_affineBaseFin A K M hy
  have : (⟨y, hy'⟩ : modularFunctionFieldBar M) = z := Subtype.ext hzy.symm
  rw [this]
  exact hz

end LevelM

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section Normalisation

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

def c4_jRingToABF (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (M : ℕ) [NeZero M] : ↥(jRing A K) →+* ↥(CharPModel.affineBaseFin M A) where
  toFun y := ⟨⟨(y : LaurentSeries (AlgebraicClosure ℚ)),
      c4_fieldOver_le_bar K M (c4_jRing_le_fieldOver A K M y.2)⟩, c4_jRing_to_affineBaseFin y.2 _⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

theorem c4_exists_monic_affineBaseFin (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0 := by
  obtain ⟨p, hp, hpt⟩ := ht.2
  refine ⟨p.map (c4_jRingToABF A K (N * q)), hp.map _, ?_⟩
  apply Subtype.val_injective
  rw [Polynomial.eval₂_map]
  have h := Polynomial.hom_eval₂ p (((CharPModel.affineBaseFin (N * q) A).subtype).comp (c4_jRingToABF A K (N * q)))
    (modularFunctionFieldBar (N * q)).val.toRingHom t
  refine h.trans ?_
  convert hpt using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip

theorem c4_coe_mem_integralCoeffs (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring :=
  mem_integralCoeffs_of_integral_affineBaseFin A (N * q) t (c4_exists_monic_affineBaseFin K t ht)

theorem c4_mem_integersFst_and_coe_residue₁ (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ h : t ∈ R.R₁.integers, ((R.residue₁ ⟨t, h⟩ : modularFunctionFieldC k N) : LaurentSeries k)
      = coeffMap red (packA_g A ⟨_, c4_coe_mem_integralCoeffs K t ht⟩) :=
  penC_good_residue_of_coe_eq R t (packA_g A ⟨_, c4_coe_mem_integralCoeffs K t ht⟩)
    (coeffMap_subtype_packA_g A ⟨_, c4_coe_mem_integralCoeffs K t ht⟩).symm

theorem c4_mem_integersFst (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) : t ∈ R.R₁.integers :=
  (c4_mem_integersFst_and_coe_residue₁ R K t ht).1

end Normalisation

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section SecondSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem c4_jBar_eq_alpha_jBar :
    CharPModel.jBar (N * q) = heckeAlphaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

theorem c4_atkinLehnerBar_jBar (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q (CharPModel.jBar (N * q))
      = heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N) := by
  have hex := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hσ := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex
  have hlegs := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ).1
  rw [c4_jBar_eq_alpha_jBar]
  exact AlgHom.congr_fun hlegs (CharPModel.jBar N)

theorem c4_isIntegral_affineBaseFin_beta_jBar (dq : ModularPolynomialData q) :
    IsIntegral ↥(CharPModel.affineBaseFin (N * q) A) (heckeBetaBar (AlgebraicClosure ℚ) N q (CharPModel.jBar N)) := by
  let S := CharPModel.affineBaseFin (N * q) A
  let jS : ↥S := ⟨CharPModel.jBar (N * q), Subring.subset_closure (Or.inr rfl)⟩
  let f₀ : Polynomial ℤ →+* ↥S := Polynomial.eval₂RingHom (Int.castRingHom ↥S) jS
  refine ⟨dq.Φ.map f₀, dq.monic.map f₀, ?_⟩
  rw [Polynomial.eval₂_map]
  apply Subtype.val_injective
  show (modularFunctionFieldBar (N * q)).val.toRingHom _ = ((0 : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
  rw [Polynomial.hom_eval₂, ZeroMemClass.coe_zero]
  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) dq.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂] at h0
  convert h0 using 2
  · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    have hX : f₀ Polynomial.X = jS := Polynomial.eval₂_X _ _
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X, c4_coeffEmb_jq, hX]
    exact c4_coe_jBar (N * q)
  · show qExpand (AlgebraicClosure ℚ) q _ = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    rw [c4_coeffEmb_qExpand]
    rfl

theorem c4_isIntegral_affineBaseFin_atkinLehnerBar_of_mem (hqN : ¬ q ∣ N) :
    ∀ y ∈ CharPModel.affineBaseFin (N * q) A,
      IsIntegral ↥(CharPModel.affineBaseFin (N * q) A) (ProlongationTuple.atkinLehnerBar N q y) := by
  let S := CharPModel.affineBaseFin (N * q) A
  let IC := integralClosure ↥S ↥(modularFunctionFieldBar (N * q))
  let W : ↥(modularFunctionFieldBar (N * q)) →+* ↥(modularFunctionFieldBar (N * q)) :=
    (ProlongationTuple.atkinLehnerBar N q).toAlgHom.toRingHom
  have hgen : Set.range (CharPModel.constantsHom (N * q) A) ∪ {CharPModel.jBar (N * q)}
      ⊆ (IC.toSubring.comap W : Set ↥(modularFunctionFieldBar (N * q))) := by
    rintro y (⟨a, rfl⟩ | rfl)
    · show W (CharPModel.constantsHom (N * q) A a) ∈ IC
      have hc : W (CharPModel.constantsHom (N * q) A a) = CharPModel.constantsHom (N * q) A a :=
        (ProlongationTuple.atkinLehnerBar N q).commutes (a : AlgebraicClosure ℚ)
      rw [hc, mem_integralClosure_iff]
      exact isIntegral_algebraMap (R := ↥S) (x := ⟨_, Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩)
    · show W (CharPModel.jBar (N * q)) ∈ IC
      rw [mem_integralClosure_iff]
      show IsIntegral ↥S (ProlongationTuple.atkinLehnerBar N q (CharPModel.jBar (N * q)))
      rw [c4_atkinLehnerBar_jBar hqN]
      obtain ⟨dq⟩ := ModularCurve.nonempty_modularPolynomialData q
      exact c4_isIntegral_affineBaseFin_beta_jBar dq
  intro y hy
  have h := (Subring.closure_le.mpr hgen) hy
  exact (mem_integralClosure_iff _ _).mp h

theorem c4_exists_monic_affineBaseFin_atkinLehnerBar (hqN : ¬ q ∣ N) (t : modularFunctionFieldBar (N * q))
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0) :
    ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype (ProlongationTuple.atkinLehnerBar N q t) p = 0 := by
  obtain ⟨p, hp, hpt⟩ := ht
  let S := CharPModel.affineBaseFin (N * q) A
  let IC := integralClosure ↥S ↥(modularFunctionFieldBar (N * q))
  let W : ↥(modularFunctionFieldBar (N * q)) →+* ↥(modularFunctionFieldBar (N * q)) :=
    (ProlongationTuple.atkinLehnerBar N q).toAlgHom.toRingHom
  have hW : ∀ y : ↥S, (W.comp S.subtype) y ∈ IC.toSubring := fun y =>
    (mem_integralClosure_iff _ _).mpr (c4_isIntegral_affineBaseFin_atkinLehnerBar_of_mem hqN y y.2)
  let ψ : ↥S →+* ↥IC := (W.comp S.subtype).codRestrict IC.toSubring hW
  have hint : IsIntegral ↥IC (W t) := by
    refine ⟨p.map ψ, hp.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap ↥IC ↥(modularFunctionFieldBar (N * q))).comp ψ = W.comp S.subtype :=
      RingHom.ext fun _ => rfl
    rw [hc, ← Polynomial.hom_eval₂, hpt, map_zero]
  have hint' : IsIntegral ↥S (W t) := isIntegral_trans (W t) hint
  obtain ⟨p', hp', h'⟩ := hint'
  exact ⟨p', hp', h'⟩

theorem c4_mem_integersSnd_and_coe_residue₂ (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ (hW : ((ProlongationTuple.atkinLehnerBar N q t : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring)
      (h₂ : t ∈ R.R₂.integers),
      ((R.residue₂ ⟨t, h₂⟩ : modularFunctionFieldC k N) : LaurentSeries k) = coeffMap red (packA_g A ⟨_, hW⟩) := by
  have hW := mem_integralCoeffs_of_integral_affineBaseFin A (N * q) _
    (c4_exists_monic_affineBaseFin_atkinLehnerBar hqN t (c4_exists_monic_affineBaseFin K t ht))
  obtain ⟨h₁, hres⟩ := penC_good_residue_of_coe_eq R (ProlongationTuple.atkinLehnerBar N q t) (packA_g A ⟨_, hW⟩)
    (coeffMap_subtype_packA_g A ⟨_, hW⟩).symm
  have h₂ : t ∈ R.R₂.integers := (R.mem_integers₂_iff t).mpr h₁
  refine ⟨hW, h₂, ?_⟩
  have h2 : R.residue₂ ⟨t, h₂⟩ = R.residue₁ ⟨_, h₁⟩ := by
    show R.ι (R.R₂.residue ⟨t, h₂⟩) = R.ι (R.R₁.residue ⟨_, h₁⟩)
    rw [R.residue₂_eq]
  rw [h2]
  exact hres

theorem c4_mem_integersSnd (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) : t ∈ R.R₂.integers := by
  obtain ⟨-, h₂, -⟩ := c4_mem_integersSnd_and_coe_residue₂ R hqN K t ht
  exact h₂

end SecondSide

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section ResidueRegular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem c4_exists_monic_of_mem_affineBaseFin {s : modularFunctionFieldBar (N * q)}
    (hs : s ∈ CharPModel.affineBaseFin (N * q) A) :
    ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype s p = 0 :=
  ⟨Polynomial.X - Polynomial.C ⟨s, hs⟩, Polynomial.monic_X_sub_C _,
    by rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, Subring.coe_subtype, sub_self]⟩

theorem c4_mem_integersFst_of_exists_monic {t : modularFunctionFieldBar (N * q)}
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0) : t ∈ R.R₁.integers := by
  have hco := mem_integralCoeffs_of_integral_affineBaseFin A (N * q) t ht
  exact (penC_good_residue_of_coe_eq R t (packA_g A ⟨_, hco⟩) (coeffMap_subtype_packA_g A ⟨_, hco⟩).symm).1

theorem c4_mem_integersFst_of_mem_affineBaseFin {s : modularFunctionFieldBar (N * q)}
    (hs : s ∈ CharPModel.affineBaseFin (N * q) A) : s ∈ R.R₁.integers :=
  c4_mem_integersFst_of_exists_monic R (c4_exists_monic_of_mem_affineBaseFin hs)

def c4_abfToIntegersFst : ↥(CharPModel.affineBaseFin (N * q) A) →+* ↥R.R₁.integers where
  toFun s := ⟨s, c4_mem_integersFst_of_mem_affineBaseFin R s.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

def c4_residue₁ABF : ↥(CharPModel.affineBaseFin (N * q) A) →+* modularFunctionFieldC k N :=
  R.residue₁.comp (c4_abfToIntegersFst R)

theorem c4_residue₁ABF_apply (s : ↥(CharPModel.affineBaseFin (N * q) A)) :
    c4_residue₁ABF R s = R.residue₁ ⟨s, c4_mem_integersFst_of_mem_affineBaseFin R s.2⟩ := rfl

theorem c4_residue₁_jBar (h : (CharPModel.jBar (N * q) : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers) :
    R.residue₁ ⟨CharPModel.jBar (N * q), h⟩ = jGeomGen k N := by
  have hcoe : ((CharPModel.jBar (N * q) : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (jqModC A) := by
    rw [c4_coe_jBar]
    exact (map_jqModC _).symm
  obtain ⟨h', hres⟩ := penC_good_residue_of_coe_eq R _ _ hcoe
  apply Subtype.ext
  rw [show (⟨CharPModel.jBar (N * q), h⟩ : ↥R.R₁.integers) = ⟨_, h'⟩ from rfl, hres]
  exact map_jqModC _

theorem c4_residue₁_const (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) := by
  obtain ⟨h', hres⟩ := penC_residue_const R a
  exact hres

theorem c4_residue₁_constantsHom (a : A) (h : CharPModel.constantsHom (N * q) A a ∈ R.R₁.integers) :
    R.residue₁ ⟨CharPModel.constantsHom (N * q) A a, h⟩ = algebraMap k (modularFunctionFieldC k N) (red a) :=
  c4_residue₁_const R a h

theorem c4_residue₁_mem_adjoin_of_mem_affineBaseFin {s : modularFunctionFieldBar (N * q)}
    (hs : s ∈ CharPModel.affineBaseFin (N * q) A) :
    R.residue₁ ⟨s, c4_mem_integersFst_of_mem_affineBaseFin R hs⟩
      ∈ Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)) := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl
      · rw [c4_residue₁_constantsHom R a]
        exact Subalgebra.algebraMap_mem _ _
      · rw [c4_residue₁_jBar R]
        exact Algebra.self_mem_adjoin_singleton k _
  | zero =>
      rw [show (⟨(0 : modularFunctionFieldBar (N * q)), c4_mem_integersFst_of_mem_affineBaseFin R
          (CharPModel.affineBaseFin (N * q) A).zero_mem⟩ : ↥R.R₁.integers) = 0 from Subtype.ext rfl, map_zero]
      exact Subalgebra.zero_mem _
  | one =>
      rw [show (⟨(1 : modularFunctionFieldBar (N * q)), c4_mem_integersFst_of_mem_affineBaseFin R
          (CharPModel.affineBaseFin (N * q) A).one_mem⟩ : ↥R.R₁.integers) = 1 from Subtype.ext rfl, map_one]
      exact Subalgebra.one_mem _
  | add x y hx hy ihx ihy =>
      have e : (⟨x + y, c4_mem_integersFst_of_mem_affineBaseFin R ((CharPModel.affineBaseFin (N * q) A).add_mem hx hy)⟩ :
          ↥R.R₁.integers) = ⟨x, c4_mem_integersFst_of_mem_affineBaseFin R hx⟩ + ⟨y, c4_mem_integersFst_of_mem_affineBaseFin R hy⟩ :=
        Subtype.ext rfl
      rw [e, map_add]
      exact Subalgebra.add_mem _ ihx ihy
  | neg x hx ihx =>
      have e : (⟨-x, c4_mem_integersFst_of_mem_affineBaseFin R ((CharPModel.affineBaseFin (N * q) A).neg_mem hx)⟩ :
          ↥R.R₁.integers) = -⟨x, c4_mem_integersFst_of_mem_affineBaseFin R hx⟩ := Subtype.ext rfl
      rw [e, map_neg]
      exact Subalgebra.neg_mem _ ihx
  | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, c4_mem_integersFst_of_mem_affineBaseFin R ((CharPModel.affineBaseFin (N * q) A).mul_mem hx hy)⟩ :
          ↥R.R₁.integers) = ⟨x, c4_mem_integersFst_of_mem_affineBaseFin R hx⟩ * ⟨y, c4_mem_integersFst_of_mem_affineBaseFin R hy⟩ :=
        Subtype.ext rfl
      rw [e, map_mul]
      exact Subalgebra.mul_mem _ ihx ihy

def c4_residue₁ToAdjoin : ↥(CharPModel.affineBaseFin (N * q) A) →+*
    ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) :=
  (c4_residue₁ABF R).codRestrict (Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))).toSubring
    (fun s => c4_residue₁_mem_adjoin_of_mem_affineBaseFin R s.2)

theorem c4_isIntegral_adjoin_residue₁ {t : modularFunctionFieldBar (N * q)}
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0)
    (h₁ : t ∈ R.R₁.integers) :
    IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N))) (R.residue₁ ⟨t, h₁⟩) := by
  obtain ⟨p, hp, hpt⟩ := ht
  refine ⟨p.map (c4_residue₁ToAdjoin R), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap ↥(Algebra.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N)).comp (c4_residue₁ToAdjoin R) = R.residue₁.comp (c4_abfToIntegersFst R) :=
    RingHom.ext fun _ => rfl
  rw [hc, ← Polynomial.eval₂_map]

  have hev : Polynomial.eval₂ (RingHom.id _) (⟨t, h₁⟩ : ↥R.R₁.integers) (p.map (c4_abfToIntegersFst R)) = 0 := by
    apply Subtype.val_injective
    rw [Polynomial.eval₂_map,
      show ((Polynomial.eval₂ ((RingHom.id ↥R.R₁.integers).comp (c4_abfToIntegersFst R)) ⟨t, h₁⟩ p : ↥R.R₁.integers) :
          modularFunctionFieldBar (N * q))
        = Polynomial.eval₂ ((R.R₁.integers.subtype).comp ((RingHom.id ↥R.R₁.integers).comp (c4_abfToIntegersFst R))) t p
        from Polynomial.hom_eval₂ p _ R.R₁.integers.subtype ⟨t, h₁⟩]
    exact hpt
  have := Polynomial.hom_eval₂ (p.map (c4_abfToIntegersFst R)) (RingHom.id _) R.residue₁ (⟨t, h₁⟩ : ↥R.R₁.integers)
  rw [hev, map_zero, RingHom.comp_id] at this
  rw [Polynomial.eval₂_map] at this ⊢
  exact this.symm

theorem c4_residue₁_mem_toValuationSubring {t : modularFunctionFieldBar (N * q)}
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0)
    (h₁ : t ∈ R.R₁.integers) (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring) :
    (R.residue₁ ⟨t, h₁⟩ : modularFunctionFieldC k N) ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_isIntegral_adjoin hv (c4_isIntegral_adjoin_residue₁ R ht h₁)

end ResidueRegular

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq evalAtJ_X ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC jqNModC map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jNGeomGen IsAffineGeomPlace isAtkinLehnerAutFull_atkinLehnerInvolutionFull coeffMap_qExpand CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.subring_le_localizedAtKer CharPReduction.constSeries CharPReduction.modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.affineBaseFin place_deg_eq_one_of_isAlgClosed mem_integralCoeffs_of_integral_affineBaseFin exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces_univ nonempty_modularPolynomialData exists_ord_sub_pos_of_integral_affineBaseFin"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd sp d0_j_pole d1"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~jBar"

section Values

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (P) in

theorem c4_exists_ord_jBar_sub_pos (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = v) :
    ∃ a₀ : A, 0 < V.ord (CharPModel.jBar (N * q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a₀ : AlgebraicClosure ℚ)) := by
  obtain ⟨a₀, ha₀⟩ := penC_exists_j_value (P := P) v hv (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) hV
  refine ⟨a₀, ?_⟩
  rw [c4_jBar_eq_alpha_jBar, ← (heckeAlphaBar (AlgebraicClosure ℚ) N q).commutes (a₀ : AlgebraicClosure ℚ), ← map_sub,
    V.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα]
  exact mul_pos (by exact_mod_cast penC_ramificationIndexAlong_pos' (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V) ha₀

variable (P) in

theorem c4_exists_hasValue_of_exists_monic {t : modularFunctionFieldBar (N * q)}
    (ht : ∃ p : Polynomial (CharPModel.affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (CharPModel.affineBaseFin (N * q) A).subtype t p = 0)
    (v : Place k (modularFunctionFieldC k N)) (hv : jGeomGen k N ∈ v.toValuationSubring)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = v) :
    ∃ a : A, V.HasValue t (a : AlgebraicClosure ℚ) := by
  obtain ⟨a₀, ha₀⟩ := c4_exists_ord_jBar_sub_pos P v hv V hV
  obtain ⟨a, ha⟩ := ModularCurve.exists_ord_sub_pos_of_integral_affineBaseFin A (N * q) V t ht a₀ ha₀
  exact ⟨a, penC_hasValue_of_sub_mem_nonunits V ha⟩

theorem c4_mem_nodeIntegersOver (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (hw : jGeomGen k N ∈ w.toValuationSubring)
    (t : modularFunctionFieldBar (N * q))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    t ∈ R.nodeIntegersOver K w := by
  refine ⟨⟨c4_mem_integersFst R K t ht, c4_mem_integersSnd R hqN K t ht, fun V hV => ?_⟩, ht.1⟩
  obtain ⟨a, ha⟩ := c4_exists_hasValue_of_exists_monic P (c4_exists_monic_affineBaseFin K t ht) w hw V hV
  exact ha.mem

end Values

end ModularCurve.PlaceSpecialization

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    (∃ h₁ : t ∈ R.R₁.integers, IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N))) ∧
    (∃ h₂ : t ∈ R.R₂.integers, IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N))) ∧
    (∀ v : Place k ↥(modularFunctionFieldC k N), jGeomGen k N ∈ v.toValuationSubring →
      ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = v →
        ∃ a : A, V.HasValue t (a : AlgebraicClosure ℚ)) := by
  have hmon := c4_exists_monic_affineBaseFin K t ht
  have h₁ : t ∈ R.R₁.integers := c4_mem_integersFst R K t ht
  obtain ⟨hW, h₂, -⟩ := c4_mem_integersSnd_and_coe_residue₂ R hqN K t ht
  have hW₁ : ProlongationTuple.atkinLehnerBar N q t ∈ R.R₁.integers := (R.mem_integers₂_iff t).mp h₂
  refine ⟨⟨h₁, c4_isIntegral_adjoin_residue₁ R hmon h₁⟩, ⟨h₂, ?_⟩, fun v hv V hV => c4_exists_hasValue_of_exists_monic P hmon v hv V hV⟩
  have e : R.residue₂ ⟨t, h₂⟩ = R.residue₁ ⟨ProlongationTuple.atkinLehnerBar N q t, hW₁⟩ := by
    show R.ι (R.R₂.residue ⟨t, h₂⟩) = R.ι (R.R₁.residue ⟨_, hW₁⟩)
    rw [R.residue₂_eq]
  rw [e]
  exact c4_isIntegral_adjoin_residue₁ R (c4_exists_monic_affineBaseFin_atkinLehnerBar hqN t hmon) hW₁

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure (solution)
