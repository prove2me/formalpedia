-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_hasValue_of_mem_smoothLocalRingFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/08d26a2f-b361-5eb5-9c98-b34a4a6bf457

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst.ModularCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_a27 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_a27"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_a27 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_a27"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_a27 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_export "AlgebraicCurve.Place" "ord_algebraMap_a27"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_a27 {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_export "AlgebraicCurve.Place" "ne_zero_of_ord_pos_a27"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_a27 {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_export "AlgebraicCurve.Place" "isUnit_iff_ord_eq_zero_a27"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_a27 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
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
  · rw [v.isUnit_iff_ord_eq_zero_a27 hsub h0]
    have hnn := v.ord_nonneg_of_mem_a27 hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_export "AlgebraicCurve.Place" "hasValue_iff_eq_or_ord_sub_pos_a27"

theorem div_mem_of_ord_le_a27 {r t : F} (ht : t ≠ 0) (h : v.ord t ≤ v.ord r) :
    r / t ∈ v.toValuationSubring := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · apply v.mem_of_ord_nonneg_a27 (div_ne_zero hr ht)
    rw [div_eq_mul_inv, v.ord_mul hr (inv_ne_zero ht), v.ord_inv]
    omega

theorem tExpansion_coeff_unique_a27 {t : F} (ht : 0 < v.ord t) (r : F) (c c' : ℕ → K)
    (hc : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c i) * t ^ i) / t ^ m ∈
      v.toValuationSubring)
    (hc' : ∀ m : ℕ, (r - ∑ i ∈ Finset.range m, algebraMap K F (c' i) * t ^ i) / t ^ m ∈
      v.toValuationSubring) :
    c = c' := by
  classical
  have ht0 : t ≠ 0 := v.ne_zero_of_ord_pos_a27 ht
  by_contra hne
  have hex : ∃ m, c m ≠ c' m := by
    by_contra hall
    exact hne (funext fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm, hmin⟩ : ∃ m, c m ≠ c' m ∧ ∀ i < m, c i = c' i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.mp (Nat.find_min hex hi)⟩
  set e : K := c m - c' m with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr hm

  have hdiff : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) / t ^ (m + 1) -
      (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) / t ^ (m + 1) =
      algebraMap K F e / t := by
    rw [← sub_div]
    have hnum : (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i) -
        (r - ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i) =
        algebraMap K F e * t ^ m := by
      have hs : ∑ i ∈ Finset.range (m + 1), algebraMap K F (c i) * t ^ i -
          ∑ i ∈ Finset.range (m + 1), algebraMap K F (c' i) * t ^ i =
          algebraMap K F e * t ^ m := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
          ← sub_mul, ← map_sub]
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hmin i hi, sub_self]
      rw [← hs]; ring
    rw [hnum, pow_succ, mul_comm (t ^ m) t, mul_div_mul_right _ _ (pow_ne_zero m ht0)]
  have hmem : algebraMap K F e / t ∈ v.toValuationSubring := by
    rw [← hdiff]; exact sub_mem (hc' (m + 1)) (hc (m + 1))
  have hord : v.ord (algebraMap K F e / t) < 0 := by
    have hae : algebraMap K F e ≠ 0 := (_root_.map_ne_zero _).mpr he0
    rw [div_eq_mul_inv, v.ord_mul hae (inv_ne_zero ht0), v.ord_inv, v.ord_algebraMap_a27]
    omega
  exact absurd (v.ord_nonneg_of_mem_a27 hmem) (not_le.mpr hord)

end Place
end AlgebraicCurve

namespace Subring p2m_export "Subring" "ext" end Subring
namespace Subring
p2m_open_scoped "Subring" in

private theorem _root_.Subring.inv_mem_of_isUnit_a27 {F : Type*} [Field F] {S : Subring F} {t : F} (h : t ∈ S)
    (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end Subring
p2m_export "" "Subring.inv_mem_of_isUnit_a27"
namespace ValuationSubring p2m_export "ValuationSubring" "ext zero_mem mem_nonunits_iff mul_mem one_mem mem_or_inv_mem add_mem valuation" end ValuationSubring
namespace ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem _root_.ValuationSubring.inv_mem_of_isUnit_a27 {F : Type*} [Field F] {S : ValuationSubring F} {t : F}
    (h : t ∈ S) (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end ValuationSubring
p2m_export "" "ValuationSubring.inv_mem_of_isUnit_a27"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField ord ord_mul ord_inv ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos_a27
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by
  constructor
  · intro h
    exact ⟨h.mem, (v.hasValue_iff_eq_or_ord_sub_pos_a27 h.mem c).mp h⟩
  · rintro ⟨hg, h⟩
    exact (v.hasValue_iff_eq_or_ord_sub_pos_a27 hg c).mpr h
p2m_export "AlgebraicCurve.Place" "hasValue_iff_mem_and_eq_or_ord_sub_pos_a27"
end Place
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData coeffMap coeffMap_single algebraMap_laurentSeries_eq_single modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence modularFunctionFieldFullC isCurveOver_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst IsStrictFst ProlongationTuple.divisorLawFst_oneSided"
p2m_open "ModularCurve.PlaceSpecialization~LevelOneProlongationPair~redFst"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue₁ residue₁_apply IsModel ι_coe R₁ ι redBar_residue redBar smoothLocalRingFst mem_smoothLocalRingFst_iff divisorLawFst_oneSided"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem ι_algebraMap_a27 (R : ProlongationTuple P) (x : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) x)
      = algebraMap k ↥(modularFunctionFieldC k N) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.residue_algebraMap_eq_red (R : ProlongationTuple P) (c : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ = algebraMap k ↥(modularFunctionFieldC k N) (red c) := by
  rw [residue₁_apply]
  have e : (⟨_, h⟩ : R.R₁.integers) = ⟨_, (R.R₁.algebraMap_mem_iff _).mpr c.2⟩ := rfl
  rw [e, R.R₁.residue_algebraMap c, ι_algebraMap_a27, R.redBar_residue]

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue_algebraMap_eq_red"
set_option maxHeartbeats 6400000 in

theorem one_le_ord_residue_fst_of_ord_pos_a27 (hqN : ¬ q ∣ N) {R : ProlongationTuple P} (hR : R.IsModel)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hW : P.IsStrictFst W)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf1 : f ∈ R.R₁.integers) (hres : R.R₁.residue ⟨f, hf1⟩ ≠ 0)
    (hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.IsStrictFst W' → P.reduceFst W' = P.reduceFst W → 0 ≤ W'.ord f)
    (hpos : 0 < W.ord f) : 1 ≤ (P.reduceFst W).ord (R.residue₁ ⟨f, hf1⟩) := by
  classical
  have hf0 : f ≠ 0 := W.ne_zero_of_ord_pos_a27 hpos
  obtain ⟨D, hD, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor f hf0
  have hlaw : Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) (P.reduceFst W) =
      (P.reduceFst W).ord (R.residue₁ ⟨f, hf1⟩) :=
    ProlongationTuple.divisorLawFst_oneSided hqN P R hR f hf1 hres D hD (P.reduceFst W) hW.2
  set x : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := D.filter P.IsStrictFst
    with hx
  have hxapp : ∀ W', x W' = if P.IsStrictFst W' then D W' else 0 := fun W' => by
    rw [hx, Finsupp.filter_apply]
  let g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℤ :=
    fun W' => if P.reduceFst W' = P.reduceFst W then x W' else 0
  have hgnn : ∀ W', 0 ≤ g W' := by
    intro W'
    show 0 ≤ (if P.reduceFst W' = P.reduceFst W then x W' else 0)
    split_ifs with h1
    · rw [hxapp]
      split_ifs with h2
      · rw [hD]; exact hnn W' h2 h1
      · exact le_refl _
    · exact le_refl _
  have hsum : ∑ W' ∈ x.support, g W' = (P.reduceFst W).ord (R.residue₁ ⟨f, hf1⟩) := by
    rw [← hlaw]
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro W' _
    simp only [g, Finsupp.single_apply]
  have hxW : x W = W.ord f := by rw [hxapp, if_pos hW, hD]
  have hWmem : W ∈ x.support := by rw [Finsupp.mem_support_iff, hxW]; exact ne_of_gt hpos
  have hgW : g W = W.ord f := by
    show (if P.reduceFst W = P.reduceFst W then x W else 0) = W.ord f
    rw [if_pos rfl, hxW]
  have h1 := Finset.single_le_sum (f := g) (s := x.support) (fun W' _ => hgnn W') hWmem
  rw [hsum, hgW] at h1
  omega

set_option maxHeartbeats 6400000 in

theorem value_mem_of_mem_smoothLocalRingFst_a27 (hqN : ¬ q ∣ N) {R : ProlongationTuple P} (hR : R.IsModel)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hW : P.IsStrictFst W)
    (r : ↥(modularFunctionFieldBar (N * q))) (h₁ : r ∈ R.R₁.integers)
    (hr : r ∈ R.smoothLocalRingFst (P.reduceFst W)) (c₀ : AlgebraicClosure ℚ)
    (hc₀ : W.HasValue r c₀) : c₀ ∈ A := by
  classical
  have hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst W' → P.reduceFst W' = P.reduceFst W → r ∈ W'.toValuationSubring :=
    fun W' h1 h2 => ((R.mem_smoothLocalRingFst_iff _ _).mp hr).2 W' h1 h2
  by_contra hnot
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl; exact hnot A.zero_mem
  have hεA : c₀⁻¹ ∈ A := (A.mem_or_inv_mem c₀).resolve_left hnot
  set ε : A := ⟨c₀⁻¹, hεA⟩ with hε
  have hεm : ε ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hnot
    have h := ValuationSubring.inv_mem_of_isUnit_a27 hεA hu
    rwa [inv_inv] at h
  have hredε : red ε = 0 := by
    rw [← R.redBar_residue ε, (IsLocalRing.residue_eq_zero_iff ε).mpr hεm, map_zero]
  have hcε : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ε : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr ε.2
  have hg1 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ε : AlgebraicClosure ℚ) * r - 1 ∈
      R.R₁.integers := sub_mem (mul_mem hcε h₁) (one_mem _)
  have hgsub : (⟨_, hg1⟩ : R.R₁.integers) = ⟨_, hcε⟩ * ⟨r, h₁⟩ - 1 := rfl
  have hresg : R.residue₁ ⟨_, hg1⟩ = -1 := by
    rw [hgsub, map_sub, map_mul, map_one, R.residue_algebraMap_eq_red ε hcε, hredε, map_zero, zero_mul,
      zero_sub]
  have hresg' : R.R₁.residue ⟨_, hg1⟩ ≠ 0 := by
    intro h0
    have : R.residue₁ ⟨_, hg1⟩ = 0 := by rw [residue₁_apply, h0, map_zero]
    rw [hresg] at this
    exact (neg_ne_zero.mpr one_ne_zero) this
  have hordg : (P.reduceFst W).ord (R.residue₁ ⟨_, hg1⟩) = 0 := by
    rw [hresg, show (-1 : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (-1) by
      rw [map_neg, map_one]]
    exact (P.reduceFst W).ord_algebraMap_a27 (-1)
  have hnng : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst W' → P.reduceFst W' = P.reduceFst W →
        0 ≤ W'.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ε : AlgebraicClosure ℚ) * r - 1) :=
    fun W' h1 h2 => W'.ord_nonneg_of_mem_a27
      (sub_mem (mul_mem (W'.algebraMap_mem' _) (hrW' W' h1 h2)) (one_mem _))
  have hval1 : W.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
      (ε : AlgebraicClosure ℚ) * r) 1 := by
    have h := (W.hasValue_algebraMap (ε : AlgebraicClosure ℚ)).mul hc₀
    rwa [show (ε : AlgebraicClosure ℚ) * c₀ = 1 from inv_mul_cancel₀ hc₀0] at h
  have hposg : 0 < W.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
      (ε : AlgebraicClosure ℚ) * r - 1) := by
    rcases (W.hasValue_iff_eq_or_ord_sub_pos_a27 hval1.mem 1).mp hval1 with hEq | hpos
    · exfalso
      apply hresg'
      have h0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (ε : AlgebraicClosure ℚ) * r - 1 = 0 := by
        rw [map_one] at hEq; rw [hEq, sub_self]
      have : (⟨_, hg1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    · rwa [map_one] at hpos
  have h := one_le_ord_residue_fst_of_ord_pos_a27 hqN hR hW _ hg1 hresg' hnng hposg
  rw [hordg] at h
  omega

end ProlongationTuple
end PlaceSpecialization
end ModularCurve

set_option maxHeartbeats 6400000 in
p2m_open "ModularCurve.PlaceSpecialization~LevelOneProlongationPair~redFst" in open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst.ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (hW : P.IsStrictFst W)
    (r : ↥(modularFunctionFieldBar (N * q))) (h₁ : r ∈ R.R₁.integers)
    (hr : r ∈ R.smoothLocalRingFst (P.reduceFst W)) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧
      (P.reduceFst W).HasValue (R.residue₁ ⟨r, h₁⟩) (red c) := by
  classical
  have hrW : r ∈ W.toValuationSubring := ((R.mem_smoothLocalRingFst_iff _ _).mp hr).2 W hW rfl
  have hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.IsStrictFst W' → P.reduceFst W' = P.reduceFst W → r ∈ W'.toValuationSubring :=
    fun W' h1 h2 => ((R.mem_smoothLocalRingFst_iff _ _).mp hr).2 W' h1 h2

  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField := IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) W.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hrat : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := W.ResidueField)).2
  obtain ⟨c₀, hc₀, -⟩ := W.exists_hasValue_of_surjective hrat hrW

  have hc₀A : c₀ ∈ A := value_mem_of_mem_smoothLocalRingFst_a27 hqN hR hW r h₁ hr c₀ hc₀
  obtain ⟨c, hc⟩ : ∃ c : A, (c : AlgebraicClosure ℚ) = c₀ := ⟨⟨c₀, hc₀A⟩, rfl⟩
  subst hc
  refine ⟨c, hc₀, ?_⟩

  have hcR : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr c.2
  have hs1 : r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) ∈
      R.R₁.integers := sub_mem h₁ hcR
  have hssub : (⟨_, hs1⟩ : R.R₁.integers) = ⟨r, h₁⟩ - ⟨_, hcR⟩ := rfl
  have hress : R.residue₁ ⟨_, hs1⟩ = R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k N) (red c) := by
    rw [hssub, map_sub, R.residue_algebraMap_eq_red c hcR]
  by_cases hz : R.residue₁ ⟨_, hs1⟩ = 0
  · have h : R.residue₁ ⟨r, h₁⟩ = algebraMap k ↥(modularFunctionFieldC k N) (red c) := by
      rw [hress] at hz; exact sub_eq_zero.mp hz
    rw [h]
    exact (P.reduceFst W).hasValue_algebraMap (red c)
  · have hres' : R.R₁.residue ⟨_, hs1⟩ ≠ 0 := fun h0 => hz (by rw [residue₁_apply, h0, map_zero])
    have hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.IsStrictFst W' → P.reduceFst W' = P.reduceFst W →
          0 ≤ W'.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ)) :=
      fun W' h1 h2 => W'.ord_nonneg_of_mem_a27 (sub_mem (hrW' W' h1 h2) (W'.algebraMap_mem' _))
    have hpos : 0 < W.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))
        (c : AlgebraicClosure ℚ)) := by
      rcases (W.hasValue_iff_eq_or_ord_sub_pos_a27 hrW (c : AlgebraicClosure ℚ)).mp hc₀ with hEq | hpos
      · exfalso
        apply hz
        have h0 : r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c : AlgebraicClosure ℚ) = 0 := by
          rw [hEq, sub_self]
        have : (⟨_, hs1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
        rw [this, map_zero]
      · exact hpos
    have h1 := one_le_ord_residue_fst_of_ord_pos_a27 hqN hR hW _ hs1 hres' hnn hpos
    rw [hress] at h1
    have hpos' : 0 < (P.reduceFst W).ord (R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k N) (red c)) := by
      omega
    rw [(P.reduceFst W).hasValue_iff_mem_and_eq_or_ord_sub_pos_a27]
    refine ⟨?_, Or.inr hpos'⟩
    have hm : R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k N) (red c) ∈
        (P.reduceFst W).toValuationSubring :=
      (P.reduceFst W).mem_of_ord_nonneg_a27 ((P.reduceFst W).ne_zero_of_ord_pos_a27 hpos') hpos'.le
    have h := add_mem hm ((P.reduceFst W).algebraMap_mem' (red c))
    simpa using h

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingFst (solution)
