-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.hasRamBound_one_of_isRoot_off_zero_1728_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/17d40e66-edaa-5a49-97e8-22dc0bed580f

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries
import Theorems.Thm_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
import Theorems.Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 3200000

p2m_open "HahnSeries Polynomial WeierstrassCurve~specialize"

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝕂" => HahnSeries ℚ (AlgebraicClosure ℚ)

noncomputable section

namespace P2MWs13
namespace Wire

variable {K : Type*} [Field K]

def hahnExpMul (n : ℕ) (hn : 0 < n) : HahnSeries ℚ K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulRight (n : ℚ))
    (mul_left_injective₀ (Nat.cast_ne_zero.mpr hn.ne'))
    (fun _ _ => mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hn))

@[scoped simp] theorem hahnExpMul_single (n : ℕ) (hn : 0 < n) (q : ℚ) (c : K) :
    hahnExpMul n hn (HahnSeries.single q c) = HahnSeries.single (q * n) c := by
  unfold hahnExpMul
  rw [embDomainRingHom_apply, embDomain_single]
  rfl

@[scoped simp] theorem hahnExpMul_coeff_mul (n : ℕ) (hn : 0 < n) (r : HahnSeries ℚ K) (q : ℚ) :
    (hahnExpMul n hn r).coeff (q * n) = r.coeff q :=
  HahnSeries.embDomain_coeff

theorem hasRamBound_one_hahnExpMul_iff (n : ℕ) (hn : 0 < n) (r : HahnSeries ℚ K) :
    HasRamBound 1 (hahnExpMul n hn r) ↔ HasRamBound n r := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · intro h q hq
    have hnq : q * n ∈ (hahnExpMul n hn r).support := by
      rw [HahnSeries.mem_support, hahnExpMul_coeff_mul]; exact hq
    obtain ⟨k, hk⟩ := h hnq
    refine ⟨k, ?_⟩
    simp only [Nat.cast_one, div_one] at hk
    field_simp
    linarith
  · intro h q hq
    obtain ⟨p, rfl⟩ : ∃ p : ℚ, p * n = q := ⟨q / n, div_mul_cancel₀ q hnQ⟩
    have hp : p ∈ r.support := by
      rw [HahnSeries.mem_support, ← hahnExpMul_coeff_mul n hn]; exact hq
    obtain ⟨k, hk⟩ := h hp
    refine ⟨k, ?_⟩
    simp only [Nat.cast_one, div_one]
    field_simp at hk
    linarith [hk]

abbrev spec (Φ : Polynomial (Polynomial ℤ)) (j₀ : HahnSeries ℚ K) : Polynomial (HahnSeries ℚ K) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ K)) j₀)

theorem hahnExpMul_comp_eval (n : ℕ) (hn : 0 < n) (j₀ : HahnSeries ℚ K) :
    (hahnExpMul n hn).comp (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ K)) j₀)
      = Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ K)) (hahnExpMul n hn j₀) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp [Polynomial.eval₂RingHom]

theorem spec_hahnExpMul (n : ℕ) (hn : 0 < n) (Φ : Polynomial (Polynomial ℤ)) (j₀ : HahnSeries ℚ K) :
    spec Φ (hahnExpMul n hn j₀) = (spec Φ j₀).map (hahnExpMul n hn) := by
  rw [spec, spec, Polynomial.map_map, hahnExpMul_comp_eval]

theorem hasRamBound_one_ofPowerSeries (p : PowerSeries K) :
    HasRamBound 1 (HahnSeries.ofPowerSeries ℚ K p) := by
  intro q hq
  have hq' : q ∈ Set.range ((↑) : ℕ → ℚ) := by
    by_contra h
    rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply] at hq
    exact hq (HahnSeries.embDomain_notin_range (by simpa using h))
  obtain ⟨m, rfl⟩ := hq'
  exact ⟨(m : ℤ), by push_cast; ring⟩

theorem algebraMap_eq_C (a : K) : algebraMap K (HahnSeries ℚ K) a = HahnSeries.C a := by
  have h1 : algebraMap K (PowerSeries K) a = PowerSeries.C a := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

theorem transcendental_single_one : Transcendental K (HahnSeries.single (1 : ℚ) (1 : K)) := by
  rw [transcendental_iff_injective]
  have heq : (Polynomial.aeval (R := K) (HahnSeries.single (1:ℚ) (1:K))).toRingHom
      = (HahnSeries.ofPowerSeries ℚ K).comp (Polynomial.coeToPowerSeries.ringHom (R := K)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.aeval (R := K) (HahnSeries.single (1:ℚ) (1:K)) (Polynomial.C a) = _
      rw [Polynomial.aeval_C, algebraMap_eq_C,
        RingHom.coe_comp, Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
    · show Polynomial.aeval (R := K) (HahnSeries.single (1:ℚ) (1:K)) Polynomial.X = _
      rw [Polynomial.aeval_X, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]
  intro p q hpq
  have hpq' : (HahnSeries.ofPowerSeries ℚ K) (p : PowerSeries K)
      = (HahnSeries.ofPowerSeries ℚ K) (q : PowerSeries K) := by
    have hp := congrFun (congrArg DFunLike.coe heq) p
    have hq := congrFun (congrArg DFunLike.coe heq) q
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply] at hp hq
    rw [← hp, ← hq]; exact hpq
  exact Polynomial.coe_injective K (HahnSeries.ofPowerSeries_injective hpq')

theorem transcendental_rat_of_qbar (x : 𝕂) (h : Transcendental ℚ̄ x) : Transcendental ℚ x := by
  rintro ⟨p, hp0, hpx⟩
  refine h ⟨p.map (algebraMap ℚ ℚ̄),
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ̄).injective).mpr hp0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    Subsingleton.elim ((algebraMap ℚ̄ 𝕂).comp (algebraMap ℚ ℚ̄)) (algebraMap ℚ 𝕂),
    ← Polynomial.aeval_def]
  exact hpx

theorem transcendental_single_three : Transcendental ℚ (HahnSeries.single (3 : ℚ) (1 : ℚ̄) : 𝕂) := by
  refine transcendental_rat_of_qbar _ (fun halg => ?_)
  refine transcendental_single_one (K := ℚ̄) (IsAlgebraic.of_pow (n := 3) (by norm_num) ?_)
  rw [HahnSeries.single_pow, one_pow]
  have h3 : (3 : ℕ) • (1 : ℚ) = 3 := by norm_num
  rwa [h3]

theorem transcendental_1728_add_single_two :
    Transcendental ℚ ((1728 : 𝕂) + HahnSeries.single (2 : ℚ) (1 : ℚ̄)) := by
  refine transcendental_rat_of_qbar _ (fun halg => ?_)
  have h1728 : IsAlgebraic ℚ̄ ((1728 : ℕ) : 𝕂) := isAlgebraic_nat 1728
  rw [Nat.cast_ofNat] at h1728
  have hsq : IsAlgebraic ℚ̄ (HahnSeries.single (2 : ℚ) (1 : ℚ̄) : 𝕂) := by
    have := (IsIntegral.sub halg.isIntegral h1728.isIntegral).isAlgebraic
    simpa using this
  refine transcendental_single_one (K := ℚ̄) (IsAlgebraic.of_pow (n := 2) (by norm_num) ?_)
  rw [HahnSeries.single_pow, one_pow]
  have h2 : (2 : ℕ) • (1 : ℚ) = 2 := by norm_num
  rwa [h2]

theorem j_eq_single_three_one (𝓔 : WeierstrassCurve (PowerSeries K)) (hΔ : IsUnit 𝓔.Δ)
    (hc4 : 𝓔.c₄ ^ 3 = 𝓔.Δ * PowerSeries.X ^ 3) :
    haveI : 𝓔.IsElliptic := ⟨hΔ⟩
    (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j = HahnSeries.single (3 : ℚ) (1 : K) := by
  haveI : 𝓔.IsElliptic := ⟨hΔ⟩
  have hWΔ : IsUnit (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  have hΔj : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ *
      (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mul]
  have hc4' : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ * HahnSeries.single (3 : ℚ) (1 : K) := by
    rw [WeierstrassCurve.map_c₄, ← map_pow, hc4, map_mul, map_pow, HahnSeries.ofPowerSeries_X,
      HahnSeries.single_pow, one_pow, WeierstrassCurve.map_Δ]
    congr 2
    simp [nsmul_eq_mul]
  exact hWΔ.mul_left_cancel (hΔj.trans hc4')

theorem j_eq_1728_add_single_two_one (𝓔 : WeierstrassCurve (PowerSeries K)) (hΔ : IsUnit 𝓔.Δ)
    (hc6 : 𝓔.c₆ ^ 2 = 𝓔.Δ * PowerSeries.X ^ 2) :
    haveI : 𝓔.IsElliptic := ⟨hΔ⟩
    (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j
      = (1728 : HahnSeries ℚ K) + HahnSeries.single (2 : ℚ) (1 : K) := by
  haveI : 𝓔.IsElliptic := ⟨hΔ⟩
  have hWΔ : IsUnit (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  have hΔj : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ *
      (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mul]
  have hc4c6 : 𝓔.c₄ ^ 3 - 𝓔.c₆ ^ 2 = 1728 * 𝓔.Δ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hc4' : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ
        * ((1728 : HahnSeries ℚ K) + HahnSeries.single (2 : ℚ) (1 : K)) := by
    have hc4'' : 𝓔.c₄ ^ 3 = 𝓔.Δ * (1728 + PowerSeries.X ^ 2) := by
      have := hc4c6; linear_combination this + hc6
    rw [WeierstrassCurve.map_c₄, ← map_pow, hc4'', map_mul, WeierstrassCurve.map_Δ,
      map_add, map_ofNat, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow]
    congr 3
    simp [nsmul_eq_mul]
  exact hWΔ.mul_left_cancel (hΔj.trans hc4')

end P2MWs13.Wire
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd.P2MWs13 P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd.P2MWs13.Wire"
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd.P2MWs13"

end
p2m_reactivate "P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd.P2MWs13 P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd.P2MWs13.Wire"

p2m_open "WeierstrassCurve~specialize" in open P2MWs13.Wire HahnSeries Polynomial  in

theorem solution
    {N : ℕ} [NeZero N] (hN : Odd N) (data : ModularCurve.ModularPolynomialData N)
    (a : AlgebraicClosure ℚ) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
      (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r) :
    HahnSeries.HasRamBound 1 r := by
  classical
  obtain ⟨𝓔, hΔ, hc⟩ := WeierstrassCurve.exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries (AlgebraicClosure ℚ) a ha0 ha1728
  haveI h𝓔E : 𝓔.IsElliptic := ⟨hΔ⟩

  have hjW : (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : ℚ̄) := by
    have hWΔ : IsUnit (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).Δ := by
      rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
    have hΔj : (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).Δ * (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j
        = (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).c₄ ^ 3 := by
      rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', ← mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, one_mul]
    have hc4' : (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).c₄ ^ 3
        = (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).Δ * (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : ℚ̄)) := by
      rw [WeierstrassCurve.map_c₄, ← map_pow, hc, map_mul, WeierstrassCurve.map_Δ, map_add,
        HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]
    exact hWΔ.mul_left_cancel (hΔj.trans hc4')
  have ht : Transcendental ℚ (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j := by
    rw [hjW]
    refine transcendental_rat_of_qbar _ (fun halg => ?_)
    apply transcendental_single_one (K := ℚ̄)
    have hCa : IsAlgebraic ℚ̄ (HahnSeries.C a : 𝕂) := by
      rw [← algebraMap_eq_C a]; exact isAlgebraic_algebraMap a
    have := (IsIntegral.sub halg.isIntegral hCa.isIntegral).isAlgebraic
    simpa using this
  have hroot' : (spec data.Φ (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j).IsRoot r := by
    rw [hjW]; exact hroot
  have hmemL : ∀ y : 𝕂, y ∈ HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos ↔ HasRamBound 1 y :=
    fun y => HahnSeries.mem_puiseuxRamSubfield_iff Nat.one_pos
  have hrL : r ∈ HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos := by
    refine ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd hN data
      (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)) ht (HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos)
      ?_ ?_ ?_ ?_ ?_ ?_ _ hroot'
    · rw [WeierstrassCurve.map_a₁, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₂, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₃, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₄, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₆, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · intro x y hns hd
      have h := WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries 𝓔 hΔ (Nat.pos_of_ne_zero (NeZero.ne N)) x y hns hd
      exact ⟨(hmemL x).mpr h.1, (hmemL y).mpr h.2⟩
  exact (hmemL _).mp hrL

end S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_hasRamBound_one_of_isRoot_off_zero_1728_of_odd (solution)
