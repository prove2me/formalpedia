-- Prove2me | solution 1 for ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/378879d3-95f0-5ec9-b5ad-d89953d28455

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
import Theorems.Thm_WeierstrassCurve_exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
import Theorems.Thm_WeierstrassCurve_map_veluQuotientOfSums
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

p2m_open "ModularCurve~dedekindPsi_pos WeierstrassCurve~map_veluGy~map_veluGx"

namespace P2MSeCoord

universe u v

noncomputable def rawJ {F : Type*} [Field F] (V : WeierstrassCurve F) : F := V.c₄ ^ 3 / V.Δ

theorem rawJ_eq_j {F : Type*} [Field F] (V : WeierstrassCurve F) (h : V.IsElliptic) :
    rawJ V = @WeierstrassCurve.j F _ V h := by
  rw [rawJ, WeierstrassCurve.j, div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ']

theorem rawJ_map {F F' : Type*} [Field F] [Field F'] (φ : F →+* F') (V : WeierstrassCurve F) :
    rawJ (V.map φ) = φ (rawJ V) := by
  rw [rawJ, rawJ, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ, map_div₀, map_pow]

section SummingSet

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem coordsOrZero_mem_summingSet (Q : W.toAffine.Point) (N : ℕ) (hQ : addOrderOf Q = N)
    (hN : 0 < N) {T : W.toAffine.Point} (hT : T ∈ AddSubgroup.zmultiples Q) (hT0 : T ≠ 0) :
    T.coordsOrZero ∈ W.oddOrderSummingSet Q (N - 1) := by
  rw [mem_oddOrderSummingSet]
  obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  have hper : ∀ w : ℤ, w • Q = (w % N) • Q := fun w => by
    conv_lhs => rw [← Int.emod_add_mul_ediv w N, add_zsmul, mul_comm, mul_zsmul, natCast_zsmul]
    rw [← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero, add_zero]
  set k := (z % N).toNat with hk
  have hz : z % N = (k : ℤ) :=
    (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hN.ne'))).symm
  have hkQ : z • Q = k • Q := by rw [hper z, hz, natCast_zsmul]
  refine ⟨k, ?_, ?_, by rw [hkQ]⟩
  · by_contra h
    have : k = 0 := by omega
    rw [hkQ, this, zero_nsmul] at hT0
    exact hT0 rfl
  · have : (k : ℤ) < N := hz ▸ Int.emod_lt_of_pos _ (by exact_mod_cast hN)
    omega

theorem oddOrderSummingSet_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N) (hN : 0 < N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.oddOrderSummingSet Q (N - 1) = W.oddOrderSummingSet Q' (N - 1) := by
  have key : ∀ {Q Q' : W.toAffine.Point}, addOrderOf Q = N → addOrderOf Q' = N →
      AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' →
      W.oddOrderSummingSet Q (N - 1) ⊆ W.oddOrderSummingSet Q' (N - 1) := by
    intro Q Q' hQ hQ' h P hP
    rw [mem_oddOrderSummingSet] at hP
    obtain ⟨k, hk1, hkN, rfl⟩ := hP
    have hk0 : k • Q ≠ 0 := by
      intro h0
      have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0
      rw [hQ] at hd
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hmem : k • Q ∈ AddSubgroup.zmultiples Q' :=
      h ▸ (AddSubgroup.zmultiples Q).nsmul_mem (AddSubgroup.mem_zmultiples Q) k
    exact coordsOrZero_mem_summingSet W Q' N hQ' hN hmem hk0
  exact Finset.Subset.antisymm (key hQ hQ' h) (key hQ' hQ h.symm)

theorem fullKernelQuotient_eq_of_zmultiples_eq {Q Q' : W.toAffine.Point} {N : ℕ}
    (hQ : addOrderOf Q = N) (hQ' : addOrderOf Q' = N) (hN : 0 < N)
    (h : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q') :
    W.fullKernelQuotient Q N = W.fullKernelQuotient Q' N := by
  unfold WeierstrassCurve.fullKernelQuotient
  rw [oddOrderSummingSet_eq_of_zmultiples_eq W hQ hQ' hN h]

end SummingSet

section Carrier

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

theorem map_veluGx (x y : R) : φ (W.veluGx x y) = (W.map φ).veluGx (φ x) (φ y) := by
  simp [WeierstrassCurve.veluGx, map_ofNat]

theorem map_veluGy (x y : R) : φ (W.veluGy x y) = (W.map φ).veluGy (φ x) (φ y) := by
  simp [WeierstrassCurve.veluGy, map_ofNat]

theorem map_asymWeight (x y : R) :
    φ (x * W.veluGx x y - y * W.veluGy x y) =
      φ x * (W.map φ).veluGx (φ x) (φ y) - φ y * (W.map φ).veluGy (φ x) (φ y) := by
  rw [map_sub, map_mul, map_mul, map_veluGx, map_veluGy]

def fkqOfSet (T : Finset (R × R)) : WeierstrassCurve R :=
  W.veluQuotientOfSums (∑ P ∈ T, W.veluGx P.1 P.2)
    (∑ P ∈ T, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))

theorem fullKernelQuotient_eq_fkqOfSet {F : Type*} [Field F] [DecidableEq F]
    (V : WeierstrassCurve F) (Q : V.toAffine.Point) (N : ℕ) :
    V.fullKernelQuotient Q N = fkqOfSet V (V.oddOrderSummingSet Q (N - 1)) := rfl

variable [DecidableEq S]

theorem fkqOfSet_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (fkqOfSet W T).map φ = fkqOfSet (W.map φ) (T.image (Prod.map φ φ)) := by
  unfold fkqOfSet
  rw [W.map_veluQuotientOfSums φ, map_sum, map_sum, Finset.sum_image hφ, Finset.sum_image hφ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    rintro ⟨x, y⟩ -
    exact map_veluGx φ W x y
  · refine Finset.sum_congr rfl ?_
    rintro ⟨x, y⟩ -
    exact map_asymWeight φ W x y

end Carrier

section Transport

variable {k : Type*} [Field k] (E : WeierstrassCurve k) {A B : Type*} [Field A] [Field B]
  [Algebra k A] [Algebra k B] [DecidableEq A] [DecidableEq B] (f : A →ₐ[k] B)

theorem coordsOrZero_pointMap (P : (E.baseChange A).toAffine.Point) :
    (WeierstrassCurve.Affine.Point.map f P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0 : B), (0 : B)) = (f 0, f 0)
    simp
  · rfl

theorem oddOrderSummingSet_pointMap (Q : (E.baseChange A).toAffine.Point) (n : ℕ) :
    (E.baseChange B).oddOrderSummingSet (WeierstrassCurve.Affine.Point.map f Q) n =
      ((E.baseChange A).oddOrderSummingSet Q n).image (Prod.map f f) := by
  simp only [WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun m _ => ?_
  show (m • WeierstrassCurve.Affine.Point.map f Q).coordsOrZero = Prod.map f f (m • Q).coordsOrZero
  rw [← map_nsmul, coordsOrZero_pointMap]

theorem fullKernelQuotient_pointMap (Q : (E.baseChange A).toAffine.Point) (N : ℕ) :
    ((E.baseChange A).fullKernelQuotient Q N).map (f : A →+* B) =
      (E.baseChange B).fullKernelQuotient (WeierstrassCurve.Affine.Point.map f Q) N := by
  rw [fullKernelQuotient_eq_fkqOfSet, fullKernelQuotient_eq_fkqOfSet, oddOrderSummingSet_pointMap,
    fkqOfSet_map (f : A →+* B) _ _
      (((f : A →+* B).injective.prodMap (f : A →+* B).injective).injOn),
    ← WeierstrassCurve.map_baseChange (W := E) f]
  rfl

theorem rawJ_fullKernelQuotient_pointMap (Q : (E.baseChange A).toAffine.Point) (N : ℕ) :
    rawJ ((E.baseChange B).fullKernelQuotient (WeierstrassCurve.Affine.Point.map f Q) N) =
      f (rawJ ((E.baseChange A).fullKernelQuotient Q N)) := by
  rw [← fullKernelQuotient_pointMap, rawJ_map]
  rfl

end Transport

theorem separable_fibre (K : Type u) [Field K] {F : Type v} [Field F] [Algebra K F]
    (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (hNK : (N : K) ≠ 0)
    (x : F) (hx : Transcendental K x) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x)).Separable := by
  set φ : Polynomial K →+* F := (Polynomial.aeval (R := K) x).toRingHom with hφ
  have hφinj : Function.Injective φ := transcendental_iff_injective.1 hx
  have hφ0 : nonZeroDivisors (Polynomial K) ≤ (nonZeroDivisors F).comap φ := fun p hp =>
    mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hp (hφinj (h.trans (map_zero φ).symm)))
  set ψ : RatFunc K →+* F := RatFunc.liftRingHom φ hφ0
  have hsep := (data.separable_map_ratFunc_of_natCast_ne_zero K N hNK).map (f := ψ)
  rw [Polynomial.map_map, Polynomial.map_map] at hsep
  convert hsep using 2
  refine Polynomial.ringHom_ext ?_ ?_
  · intro n
    simp [ψ, φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]
    change x = ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
    rw [RatFunc.liftRingHom_algebraMap]
    simp [φ]

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k M : Type*} [Field k] [Field M] [Algebra k M]
    [IsAlgClosed M] [DecidableEq M] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : M) ≠ 0) :
    Nat.card {Q : (E.baseChange M).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := M) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem natCard_cyclicSubgroups_of_isAlgClosed {k M : Type*} [Field k] [Field M] [Algebra k M]
    [IsAlgClosed M] [DecidableEq M] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : M) ≠ 0) :
    Nat.card {H : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} =
      dedekindPsi N := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := M) hN
  exact AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy N e

theorem nsmul_eq_zero_of_mem {A : Type*} [AddCommGroup A] {H : AddSubgroup A} {N : ℕ}
    (hH : Nat.card H = N) {P : A} (hP : P ∈ H) : N • P = 0 := by
  have := card_nsmul_eq_zero' (G := H) (x := ⟨P, hP⟩)
  rw [hH] at this
  exact congrArg Subtype.val this

theorem exists_generator {A : Type*} [AddCommGroup A] {N : ℕ} (H : AddSubgroup A)
    (hH : IsAddCyclic H ∧ Nat.card H = N) :
    ∃ Q : A, H = AddSubgroup.zmultiples Q ∧ addOrderOf Q = N := by
  obtain ⟨Q, hQ⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hH.1
  refine ⟨Q, hQ.symm, ?_⟩
  rw [← Nat.card_zmultiples, hQ, hH.2]

theorem zmultiples_mem_cyclicSubgroups {A : Type*} [AddCommGroup A] {N : ℕ} (Q : A)
    (hQ : addOrderOf Q = N) :
    IsAddCyclic (AddSubgroup.zmultiples Q) ∧ Nat.card (AddSubgroup.zmultiples Q) = N :=
  ⟨inferInstance, by rw [Nat.card_zmultiples, hQ]⟩

theorem dedekindPsi_pos {N : ℕ} (hN : N ≠ 0) : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, hN]
  calc 0 < N / 1 := by rw [Nat.div_one]; exact Nat.pos_of_ne_zero hN
    _ ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
        Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

theorem exists_eq_zmultiples_of_enum {A : Type*} [AddCommGroup A] {N : ℕ} (hN : N ≠ 0)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = dedekindPsi N)
    (Q : ι → A) (hQ : ∀ i, addOrderOf (Q i) = N)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hcard : Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N} = dedekindPsi N)
    (H : AddSubgroup A) (hH : IsAddCyclic H ∧ Nat.card H = N) :
    ∃ i, H = AddSubgroup.zmultiples (Q i) := by
  haveI : Finite {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (dedekindPsi_pos hN).ne')
  let g : ι → {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N} := fun i =>
    ⟨AddSubgroup.zmultiples (Q i), zmultiples_mem_cyclicSubgroups (Q i) (hQ i)⟩
  have hg : Function.Injective g := fun i i' h => hQinj (congrArg Subtype.val h)
  have hbij := hg.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, hι])
  obtain ⟨i, hi⟩ := hbij.2 ⟨H, hH⟩
  exact ⟨i, (congrArg Subtype.val hi).symm⟩

theorem isRoot_prod_X_sub_C_iff {F : Type*} [Field F] {ι : Type*} [Fintype ι] (a : ι → F) (y : F) :
    (∏ i, (Polynomial.X - Polynomial.C (a i))).IsRoot y ↔ ∃ i, y = a i := by
  rw [Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

theorem injective_of_separable_prod_X_sub_C {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (a : ι → F) (hsep : (∏ i, (Polynomial.X - Polynomial.C (a i))).Separable) :
    Function.Injective a := by
  classical
  have hne : (∏ i, (Polynomial.X - Polynomial.C (a i))) ≠ 0 := hsep.ne_zero
  have hnd := Polynomial.nodup_roots hsep
  rw [Polynomial.roots_prod _ _ hne] at hnd
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at hnd
  intro i j h
  exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_val.mpr (Finset.mem_univ i)) j
    (Finset.mem_val.mpr (Finset.mem_univ j)) h

end P2MSeCoord

namespace P2MSeCoord

universe u v

theorem exists_theta (K : Type u) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (hNK : (N : K) ≠ 0) (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Θ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω)
          (algebraMap k Ω E.j))).IsRoot y},
      (∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Θ H').1 : Ω) = σ (Θ H).1) ∧
      (∀ (H : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : (E.baseChange Ω).toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ((Θ H).1 : Ω) = rawJ ((E.baseChange Ω).fullKernelQuotient Q N)) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0

  let M := AlgebraicClosure Ω
  let ι : Ω →ₐ[k] M := IsScalarTower.toAlgHom k Ω M
  have hιalg : ∀ x : Ω, ι x = algebraMap Ω M x := fun x => rfl
  let ιp : (E.baseChange Ω).toAffine.Point →+ (E.baseChange M).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map ι
  have hιp : Function.Injective ιp := WeierstrassCurve.Affine.Point.map_injective ι

  have hNk : (N : k) ≠ 0 := fun h => hNK ((algebraMap K k).injective (by simpa using h))
  have hNΩ : (N : Ω) ≠ 0 := fun h => hNk ((algebraMap k Ω).injective (by simpa using h))
  have hNM : (N : M) ≠ 0 := fun h => hNΩ ((algebraMap Ω M).injective (by simpa using h))

  set x : Ω := algebraMap k Ω E.j with hx
  set pΩ : Polynomial Ω := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x) with hpΩ
  have hxT : Transcendental K x := (transcendental_algebraMap_iff (algebraMap k Ω).injective).2 hE
  have hsep : pΩ.Separable := separable_fibre K N data hNK x hxT
  haveI instEM : (E.baseChange M).IsElliptic :=
    show (E.map (algebraMap k M)).IsElliptic from inferInstance
  have hjM : (E.baseChange M).j = algebraMap Ω M x := by
    change (E.map (algebraMap k M)).j = _
    rw [WeierstrassCurve.map_j, hx, ← IsScalarTower.algebraMap_apply]
  have hpM : pΩ.map (algebraMap Ω M) = fibrePoly data.Φ (E.baseChange M).j := by
    rw [fibrePoly, hpΩ, Polynomial.map_map, hjM]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp
  have hsepM : (pΩ.map (algebraMap Ω M)).Separable := hsep.map

  obtain ⟨ιT, instι, hι, Qe, hQe, hQinj, hΔe⟩ :=
    WeierstrassCurve.exists_enum_cyclic_fullKernelQuotient_discriminant_ne_zero (K := M) hNM
      (E.baseChange M)
  have hprod :=
    ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental
      (h0 := ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental_of_charZero)
      hNM data (E.baseChange M) hι Qe hQe hQinj hΔe

  set a : ιT → M := fun i => rawJ ((E.baseChange M).fullKernelQuotient (Qe i) N) with ha
  have hprod' : pΩ.map (algebraMap Ω M) = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    rw [hpM, hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← rawJ_eq_j]
  have hainj : Function.Injective a :=
    injective_of_separable_prod_X_sub_C a (hprod' ▸ hsepM)
  have hrootM : ∀ y : M, (pΩ.map (algebraMap Ω M)).IsRoot y ↔ ∃ i, y = a i := fun y => by
    rw [hprod']; exact isRoot_prod_X_sub_C_iff a y
  have hrootΩ : ∀ y : Ω, pΩ.IsRoot y ↔ ∃ i, algebraMap Ω M y = a i := fun y => by
    rw [← hrootM, Polynomial.isRoot_map_iff (algebraMap Ω M).injective]

  have hcardS := natCard_cyclicSubgroups_of_isAlgClosed (M := M) E N hNM
  have hexh : ∀ H' : AddSubgroup (E.baseChange M).toAffine.Point,
      IsAddCyclic H' ∧ Nat.card H' = N → ∃ i, H' = AddSubgroup.zmultiples (Qe i) :=
    exists_eq_zmultiples_of_enum hN0 hι Qe hQe hQinj hcardS

  have htorM := natCard_torsion_of_isAlgClosed (M := M) E N hNM
  have hhit : ∀ P' : (E.baseChange M).toAffine.Point, N • P' = 0 → ∃ P, N • P = 0 ∧ ιp P = P' :=
    exists_eq_of_nsmul_eq_zero ιp hιp N hfull htorM

  have hval : ∀ Q : (E.baseChange Ω).toAffine.Point, addOrderOf Q = N →
      ∃ i, AddSubgroup.zmultiples (ιp Q) = AddSubgroup.zmultiples (Qe i) ∧
        algebraMap Ω M (rawJ ((E.baseChange Ω).fullKernelQuotient Q N)) = a i := by
    intro Q hQ
    have hQM : addOrderOf (ιp Q) = N := by rw [addOrderOf_injective ιp hιp, hQ]
    obtain ⟨i, hi⟩ := hexh _ (zmultiples_mem_cyclicSubgroups (ιp Q) hQM)
    refine ⟨i, hi, ?_⟩
    show algebraMap Ω M (rawJ ((E.baseChange Ω).fullKernelQuotient Q N)) =
      rawJ ((E.baseChange M).fullKernelQuotient (Qe i) N)
    rw [← fullKernelQuotient_eq_of_zmultiples_eq (E.baseChange M) hQM (hQe i) hNpos hi]
    exact (rawJ_fullKernelQuotient_pointMap E ι Q N).symm

  have hindep : ∀ {Q Q' : (E.baseChange Ω).toAffine.Point}, addOrderOf Q = N → addOrderOf Q' = N →
      AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' →
      rawJ ((E.baseChange Ω).fullKernelQuotient Q N) = rawJ ((E.baseChange Ω).fullKernelQuotient Q' N) :=
    fun hQ hQ' h => by rw [fullKernelQuotient_eq_of_zmultiples_eq (E.baseChange Ω) hQ hQ' hNpos h]

  have hgen : ∀ H : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N},
      ∃ Q : (E.baseChange Ω).toAffine.Point, H.1 = AddSubgroup.zmultiples Q ∧ addOrderOf Q = N :=
    fun H => exists_generator H.1 H.2
  choose gen hgen1 hgen2 using hgen

  have hroot : ∀ H, pΩ.IsRoot (rawJ ((E.baseChange Ω).fullKernelQuotient (gen H) N)) := fun H => by
    obtain ⟨i, -, hi⟩ := hval (gen H) (hgen2 H)
    exact (hrootΩ _).2 ⟨i, hi⟩
  let Θ₀ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} →
      {y : Ω // pΩ.IsRoot y} := fun H => ⟨rawJ ((E.baseChange Ω).fullKernelQuotient (gen H) N), hroot H⟩
  have hΘ₀ : ∀ H, (Θ₀ H).1 = rawJ ((E.baseChange Ω).fullKernelQuotient (gen H) N) := fun H => rfl

  have hΘ₀val : ∀ H (Q : (E.baseChange Ω).toAffine.Point), H.1 = AddSubgroup.zmultiples Q →
      addOrderOf Q = N → (Θ₀ H).1 = rawJ ((E.baseChange Ω).fullKernelQuotient Q N) := by
    intro H Q hHQ hQ
    rw [hΘ₀]
    exact hindep (hgen2 H) hQ ((hgen1 H).symm.trans hHQ)

  have hinj : Function.Injective Θ₀ := by
    intro H₁ H₂ h
    have h' : algebraMap Ω M (Θ₀ H₁).1 = algebraMap Ω M (Θ₀ H₂).1 := by rw [h]
    obtain ⟨i₁, hi₁, hv₁⟩ := hval (gen H₁) (hgen2 H₁)
    obtain ⟨i₂, hi₂, hv₂⟩ := hval (gen H₂) (hgen2 H₂)
    rw [hΘ₀, hΘ₀, hv₁, hv₂] at h'
    have hii : i₁ = i₂ := hainj h'
    subst hii
    apply Subtype.ext
    apply AddSubgroup.map_injective hιp
    rw [hgen1 H₁, hgen1 H₂, AddMonoidHom.map_zmultiples, AddMonoidHom.map_zmultiples, hi₁, hi₂]

  have hsurj : Function.Surjective Θ₀ := by
    rintro ⟨y, hy⟩
    obtain ⟨i, hi⟩ := (hrootΩ y).1 hy
    have htor : N • Qe i = 0 := by rw [← hQe i]; exact addOrderOf_nsmul_eq_zero (Qe i)
    obtain ⟨P, -, hP⟩ := hhit (Qe i) htor
    have hPord : addOrderOf P = N := by rw [← addOrderOf_injective ιp hιp, hP, hQe i]
    refine ⟨⟨AddSubgroup.zmultiples P, zmultiples_mem_cyclicSubgroups P hPord⟩, ?_⟩
    apply Subtype.ext
    apply (algebraMap Ω M).injective
    show algebraMap Ω M (Θ₀ _).1 = algebraMap Ω M y
    rw [hΘ₀val _ P rfl hPord, hi]
    show _ = rawJ ((E.baseChange M).fullKernelQuotient (Qe i) N)
    have hzm : AddSubgroup.zmultiples (ιp P) = AddSubgroup.zmultiples (Qe i) := by rw [hP]
    rw [← fullKernelQuotient_eq_of_zmultiples_eq (E.baseChange M)
      (by rw [addOrderOf_injective ιp hιp, hPord]) (hQe i) hNpos hzm]
    exact (rawJ_fullKernelQuotient_pointMap E ι P N).symm
  refine ⟨Equiv.ofBijective Θ₀ ⟨hinj, hsurj⟩, ?_, ?_⟩
  ·
    intro σ H H' hH'
    change (Θ₀ H').1 = σ (Θ₀ H).1
    have hgen' : H'.1 = AddSubgroup.zmultiples
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) (gen H)) := by
      rw [hH', hgen1 H, AddMonoidHom.map_zmultiples]
    have hord' : addOrderOf (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) (gen H)) = N := by
      rw [addOrderOf_injective _ (WeierstrassCurve.Affine.Point.map_injective (σ : Ω →ₐ[k] Ω)),
        hgen2 H]
    rw [hΘ₀val H' _ hgen' hord', hΘ₀, rawJ_fullKernelQuotient_pointMap E (σ : Ω →ₐ[k] Ω) (gen H) N]
    rfl
  ·
    intro H Q hHQ hQ
    exact hΘ₀val H Q hHQ hQ

end P2MSeCoord

open P2MSeCoord in
universe u v in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Φ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω //
          ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap k Ω E.j},
      (∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ H).1) ∧
      (∀ (H : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N})
          (Q : (E.baseChange Ω).toAffine.Point), H.1 = AddSubgroup.zmultiples Q → addOrderOf Q = N →
          ∀ hΔ : ((E.baseChange Ω).fullKernelQuotient Q N).Δ ≠ 0,
            (Φ H).1 ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ =
              @WeierstrassCurve.j Ω _ ((E.baseChange Ω).fullKernelQuotient Q N) ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  have hj₀ : Transcendental K (algebraMap k Ω E.j) :=
    (transcendental_algebraMap_iff (algebraMap k Ω).injective).2 hE

  obtain ⟨Θ, hΘ, hΘval⟩ := exists_theta K N data k Ω hN E hE hfull

  obtain ⟨e, he⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
      K N hN data Ω (algebraMap k Ω E.j) hj₀
  refine ⟨Θ.trans e.symm, fun σ H H' hH => ?_, fun H Q hHQ hQ hΔ => ?_⟩
  ·
    set ψ := e.symm (Θ H) with hψ
    have hψσ : ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ.1 ⟨jqModC K, jqModC_mem_full K N⟩ =
        algebraMap k Ω E.j := by
      rw [AlgHom.comp_apply, ψ.2, AlgHom.restrictScalars_apply, AlgHom.commutes]

    have key : e ⟨((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ.1, hψσ⟩ = Θ H' := by
      apply Subtype.ext
      rw [he, hΘ σ H H' hH]
      show σ (ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩) = σ (Θ H).1
      rw [← he ψ, hψ, Equiv.apply_symm_apply]
    show (e.symm (Θ H')).1 = ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ.1
    rw [← key, Equiv.symm_apply_apply]
  ·
    have h1 := he (e.symm (Θ H))
    rw [Equiv.apply_symm_apply] at h1
    show (e.symm (Θ H)).1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ = _
    rw [← h1, hΘval H Q hHQ hQ, ← rawJ_eq_j]

end S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j
end P2MW
export P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_apply_jqNModC_eq_fullKernelQuotient_j (solution)
