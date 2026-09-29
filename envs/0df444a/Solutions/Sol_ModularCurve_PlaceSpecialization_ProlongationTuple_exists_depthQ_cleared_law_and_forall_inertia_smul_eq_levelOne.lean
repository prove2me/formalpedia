-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/890d924f-81f5-552f-9542-0d0b3d55d1ec

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed
import Theorems.Thm_ValuationSubring_exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open scoped Pointwise

namespace S12EL
namespace Depth

section ValueGroup
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem zpow_injective_of_lt_one {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) : Function.Injective fun n : ℤ => γ ^ n := by
  intro m n hmn
  simp only at hmn
  set u : Γˣ := Units.mk0 γ h0 with hu
  have hu1 : u < 1 := by
    rw [← Units.val_lt_val, hu, Units.val_mk0, Units.val_one]; exact h1
  have hum : ∀ k : ℤ, ((u ^ k : Γˣ) : Γ) = γ ^ k := fun k => by
    rw [Units.val_zpow_eq_zpow_val, hu, Units.val_mk0]
  have h' : u ^ m = u ^ n := Units.ext (by rw [hum, hum]; exact hmn)
  have hinv : 1 < u⁻¹ := one_lt_inv'.mpr hu1
  have hsm : StrictMono fun k : ℤ => (u⁻¹) ^ k := zpow_right_strictMono hinv
  have : (u⁻¹) ^ (-m) = (u⁻¹) ^ (-n) := by
    rw [inv_zpow', inv_zpow', neg_neg, neg_neg, h']
  have := hsm.injective this
  omega

theorem pow_injective_of_lt_one {γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) {m n : ℕ} (h : γ ^ m = γ ^ n) : m = n := by
  have := zpow_injective_of_lt_one h0 h1 (show γ ^ (m : ℤ) = γ ^ (n : ℤ) by rw [zpow_natCast, zpow_natCast, h])
  exact_mod_cast this

theorem pow_den_eq_pow_num {a γ : Γ} {m n : ℕ} (hm : m ≠ 0) (h : a ^ m = γ ^ n) :
    a ^ ((n : ℚ) / m).den = γ ^ ((n : ℚ) / m).num.toNat := by
  set x : ℚ := (n : ℚ) / m with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hnum : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
  have hden : x.den ≠ 0 := x.den_nz

  have hcross : (n : ℤ) * x.den = x.num * m := by
    have h1 : (x.num : ℚ) / x.den = (n : ℚ) / m := by rw [Rat.num_div_den, hx]
    rw [div_eq_div_iff (by exact_mod_cast hden) (by exact_mod_cast hm)] at h1
    exact_mod_cast h1.symm
  have hcross' : n * x.den = x.num.toNat * m := by
    have := hcross
    rw [← Int.toNat_of_nonneg hnum] at this
    exact_mod_cast this
  apply pow_left_injective hm
  simp only
  rw [← pow_mul, mul_comm, pow_mul, h, ← pow_mul, hcross', pow_mul]

theorem rat_eq_of_pow_laws {a γ : Γ} (h0 : γ ≠ 0) (h1 : γ < 1) {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxl : a ^ x.den = γ ^ x.num.toNat) (hyl : a ^ y.den = γ ^ y.num.toNat) : x = y := by
  have key : γ ^ (x.num.toNat * y.den) = γ ^ (y.num.toNat * x.den) := by
    rw [pow_mul, ← hxl, pow_mul, ← hyl, ← pow_mul, ← pow_mul, mul_comm]
  have hexp := pow_injective_of_lt_one h0 h1 key
  have hxn : ((x.num.toNat : ℕ) : ℤ) = x.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)
  have hyn : ((y.num.toNat : ℕ) : ℤ) = y.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hy)
  have hexp' : x.num * y.den = y.num * x.den := by
    have : ((x.num.toNat * y.den : ℕ) : ℤ) = ((y.num.toNat * x.den : ℕ) : ℤ) := by rw [hexp]
    push_cast at this
    rwa [hxn, hyn] at this
  rw [← Rat.num_div_den x, ← Rat.num_div_den y, div_eq_div_iff (by exact_mod_cast x.den_nz) (by exact_mod_cast y.den_nz)]
  exact_mod_cast hexp'

end ValueGroup

theorem natCast_mem_nonunits_of_ringHom_charP {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) :
    ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ : A)) := (A.valuation_eq_one_iff _).mpr h
    have h2 := hu.map red
    have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ = ((q : ℕ) : k) := by
      rw [← map_natCast red q]
      congr 1
    rw [h3, CharP.cast_eq_zero k q] at h2
    exact not_isUnit_zero h2

theorem apply_mem_of_mem_inertiaSubgroupIn {A : ValuationSubring (AlgebraicClosure ℚ)}
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {a : AlgebraicClosure ℚ} (ha : a ∈ A) : σ a ∈ A := by
  obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσ
  have hstab : ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) • A = A := MulAction.mem_stabilizer_iff.mp τ.2
  have := ValuationSubring.smul_mem_pointwise_smul (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a A ha
  rw [hstab] at this
  rwa [AlgEquiv.smul_def] at this

theorem valuation_eq_one_of_mem_of_inv_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {s : AlgebraicClosure ℚ} (h0 : s ≠ 0)
    (hs : s ∈ A) (hs' : s⁻¹ ∈ A) : A.valuation s = 1 := by
  apply le_antisymm ((A.valuation_le_one_iff _).mpr hs)
  have h1 : A.valuation s⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hs'
  by_contra hlt
  push_neg at hlt
  have hmul : A.valuation s * A.valuation s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  exact absurd hmul (mul_lt_one_of_lt_of_le hlt h1).ne

end S12EL.Depth

namespace S12EL
namespace Depth

theorem mem_and_inv_mem_of_valuation_eq_one {A : ValuationSubring (AlgebraicClosure ℚ)} {s : AlgebraicClosure ℚ}
    (h : A.valuation s = 1) : s ∈ A ∧ s⁻¹ ∈ A := by
  refine ⟨(A.valuation_le_one_iff _).mp h.le, (A.valuation_le_one_iff _).mp ?_⟩
  rw [map_inv₀, h, inv_one]

theorem valuation_pow_apply_eq {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {t : AlgebraicClosure ℚ} (ht : t ≠ 0)
    {d n : ℕ} (h : A.valuation t ^ d = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ n) (hq : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0) :
    A.valuation (σ t) ^ d = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ n := by
  set s : AlgebraicClosure ℚ := t ^ d / ((q : ℕ) : AlgebraicClosure ℚ) ^ n with hs
  have hs1 : A.valuation s = 1 := by
    rw [hs, map_div₀, map_pow, map_pow, h, div_self (pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hq))]
  obtain ⟨hsA, hsA'⟩ := mem_and_inv_mem_of_valuation_eq_one hs1
  have hs0 : s ≠ 0 := by rw [hs]; exact div_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ hq)
  have hσs : A.valuation (σ s) = 1 :=
    valuation_eq_one_of_mem_of_inv_mem (by rw [map_ne_zero]; exact hs0)
      (apply_mem_of_mem_inertiaSubgroupIn hσ hsA) (by rw [← map_inv₀]; exact apply_mem_of_mem_inertiaSubgroupIn hσ hsA')
  have htd : t ^ d = s * ((q : ℕ) : AlgebraicClosure ℚ) ^ n := by
    rw [hs, div_mul_cancel₀ _ (pow_ne_zero _ hq)]
  calc A.valuation (σ t) ^ d = A.valuation (σ (t ^ d)) := by rw [map_pow, map_pow]
    _ = A.valuation (σ s * ((q : ℕ) : AlgebraicClosure ℚ) ^ n) := by rw [htd, map_mul, map_pow, map_natCast]
    _ = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ n := by rw [map_mul, hσs, one_mul, map_pow]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem exists_depth {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (c : R.NodeCoordinates K w) (width : ℕ) (hwidth : 1 ≤ width)
    (ϖ ε : ↥(NodeLocalized.coeffSubring A K)) (eK : ℕ) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (width * eK) * u)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w) :
    ∃ δ : ℚ, 0 < δ ∧ δ < width ∧ c.yDepth V ^ δ.den = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ δ.num.toNat := by
  have hq1 : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h)
  obtain ⟨hx1, hy1, hprod⟩ :=
    ProlongationTuple.nodeDepths_lt_one_and_partition_of_nodeEquation_of_orderLawFixed R hq1 hR hO W hW hRL hNV K w hw
      hVI ϖ c (width * eK) u hu hxy V hV

  have hεA : A.valuation ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = 1 := by
    obtain ⟨eu, heu⟩ := hε
    have hinv : ((eu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)) * ε = 1 := by
      rw [← heu, Units.inv_mul]
    have hε0 : ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have : (ε : ↥(NodeLocalized.coeffSubring A K)) = 0 := Subtype.ext h0
      rw [this, mul_zero] at hinv
      exact zero_ne_one hinv
    refine valuation_eq_one_of_mem_of_inv_mem hε0 ε.2.1 ?_
    have hcoe : (((eu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)
        = ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← Subring.coe_mul, hinv, Subring.coe_one])
    rw [← hcoe]
    exact ((eu⁻¹ : (↥(NodeLocalized.coeffSubring A K))ˣ) : ↥(NodeLocalized.coeffSubring A K)).2.1
  have hqϖ' : ((q : ℕ) : AlgebraicClosure ℚ) = ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ eK
      * ((ε : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by
    have := congrArg (fun t : ↥(NodeLocalized.coeffSubring A K) => (t : AlgebraicClosure ℚ)) hqϖ
    simpa using this
  have hE : 1 ≤ width * eK := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨r, hr, p, hp, hpr, hlaw⟩ :=
    ValuationSubring.exists_valuation_pow_eq_valuation_pow_of_mul_eq_pow_of_lt_one A
      ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) eK heK _ hεA hqϖ' (width * eK) hE _ _ hy1 hx1
      (by rw [mul_comm]; exact hprod)

  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ eK := by
    rw [hqϖ', map_mul, map_pow, hεA, mul_one]
  have hlaw0 : c.yDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p := hlaw
  have hlaw' : c.yDepth V ^ (r * eK) = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ p := by
    rw [pow_mul, hlaw0, hvq, ← pow_mul, ← pow_mul, mul_comm]
  have hm : r * eK ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  refine ⟨(p : ℚ) / ((r * eK : ℕ) : ℚ), ?_, ?_, pow_den_eq_pow_num hm hlaw'⟩
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    have : p < r * (width * eK) := by omega
    calc (p : ℚ) < (r * (width * eK) : ℕ) := by exact_mod_cast this
      _ = (width : ℚ) * ((r * eK : ℕ) : ℚ) := by push_cast; ring

end S12EL.Depth

open S12EL.Depth in

theorem solution
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed) (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (K : Place k (modularFunctionFieldC k 1) → IntermediateField ℚ (AlgebraicClosure ℚ))
    [hK : ∀ w : Place k (modularFunctionFieldC k 1), FiniteDimensional ℚ ↥(K w)]
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K w, σ z = z)
    (coord : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), R.NodeCoordinates (K w) w)
    (width : Place k (modularFunctionFieldC k 1) → ℕ)
    (ϖ : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (K w)))
    (eK : Place k (modularFunctionFieldC k 1) → ℕ) (heK : ∀ w ∈ W, 1 ≤ eK w)
    (ε : ∀ w : Place k (modularFunctionFieldC k 1), ↥(NodeLocalized.coeffSubring A (K w)))
    (hε : ∀ w ∈ W, IsUnit (ε w))
    (hqϖ : ∀ w ∈ W, ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (K w))) = ϖ w ^ eK w * ε w)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw) ∧
        (coord w hw).x * (coord w hw).y = R.nodeConst (K w) w (ϖ w) ^ (width w * eK w) * u w hw) :
    ∃ depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℚ,
      (∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
        P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
          0 < depthQ V ∧ depthQ V < width w ∧ (coord w hw).yDepth V ^ (depthQ V).den =
            A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (depthQ V).num.toNat) ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        depthQ (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = depthQ V) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  have hW' : ∀ w ∈ W, w ∈ ssPlaces q 1 k := fun w hw => (hW w).mp hw
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := natCast_mem_nonunits_of_ringHom_charP red
  set γ : A.ValueGroup := A.valuation ((q : ℕ) : AlgebraicClosure ℚ) with hγ
  have hγ0 : γ ≠ 0 := by rw [hγ]; exact (Valuation.ne_zero_iff _).mpr hq0
  have hγ1 : γ < 1 := by rw [hγ]; exact (ValuationSubring.mem_nonunits_iff A).mp hA

  have exδ : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), P.reduceFst V = w →
      ∃ δ : ℚ, 0 < δ ∧ δ < width w ∧ (coord w hw).yDepth V ^ δ.den = γ ^ δ.num.toNat := by
    intro w hw V hV
    have hwidth : 1 ≤ width w := by

      by_contra h0
      push_neg at h0
      have hw0 : width w = 0 := by omega
      obtain ⟨huu, hxy⟩ := hu w hw
      rw [hw0, zero_mul, pow_zero, one_mul (u w hw)] at hxy

      have h1 := (coord w hw).nodeResidue₁_x_mul_y
      have hxyu : (⟨(coord w hw).x, (coord w hw).x.2.1⟩ * ⟨(coord w hw).y, (coord w hw).y.2.1⟩ : ↥(R.nodeIntegers w))
          = ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩ := by
        apply Subtype.ext
        show ((coord w hw).x : ↥(modularFunctionFieldBar (1 * q))) * ((coord w hw).y : ↥(modularFunctionFieldBar (1 * q)))
          = (u w hw : ↥(modularFunctionFieldBar (1 * q)))
        rw [← Subring.coe_mul, hxy]
      rw [hxyu] at h1
      obtain ⟨uu, huu'⟩ := huu
      have hunit : IsUnit ((⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩ : ↥(R.nodeIntegers w))) := by
        refine ⟨⟨_, ⟨((uu⁻¹ : (↥(R.nodeIntegersOver (K w) w))ˣ) : ↥(R.nodeIntegersOver (K w) w)),
          ((uu⁻¹ : (↥(R.nodeIntegersOver (K w) w))ˣ) : ↥(R.nodeIntegersOver (K w) w)).2.1⟩, ?_, ?_⟩, rfl⟩
        · apply Subtype.ext
          show (u w hw : ↥(modularFunctionFieldBar (1 * q)))
            * (((uu⁻¹ : (↥(R.nodeIntegersOver (K w) w))ˣ) : ↥(R.nodeIntegersOver (K w) w)) : ↥(modularFunctionFieldBar (1 * q))) = 1
          rw [← huu', ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
        · apply Subtype.ext
          show (((uu⁻¹ : (↥(R.nodeIntegersOver (K w) w))ˣ) : ↥(R.nodeIntegersOver (K w) w)) : ↥(modularFunctionFieldBar (1 * q)))
            * (u w hw : ↥(modularFunctionFieldBar (1 * q))) = 1
          rw [← huu', ← Subring.coe_mul, Units.inv_mul, Subring.coe_one]
      have := hunit.map (R.nodeResidue₁ w)
      rw [h1] at this
      exact not_isUnit_zero this
    exact exists_depth R hR hO W hW' hRL hNV (K w) w hw (hVI w hw) (coord w hw) (width w) hwidth (ϖ w) (ε w) (eK w)
      (heK w hw) (hε w hw) (hqϖ w hw) (u w hw) (hu w hw).1 (hu w hw).2 V hV
  choose dq hdq using exδ

  let depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℚ := fun V =>
    if h : P.reduceFst V ∈ W then dq (P.reduceFst V) h V rfl else 0
  have hdef : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : P.reduceFst V = w),
      depthQ V = dq w hw V hV := by
    intro w hw V hV
    subst hV
    show (if h : P.reduceFst V ∈ W then dq (P.reduceFst V) h V rfl else 0) = _
    rw [dif_pos hw]
  refine ⟨depthQ, fun w hw V hV _ _ => ?_, fun σ hσ V => ?_⟩
  · rw [hdef w hw V hV]
    exact hdq w hw V hV
  · by_cases h : P.reduceFst V ∈ W
    · have hVσ : P.reduceFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = P.reduceFst V := reduceFst_arithmeticGalois_smul P σ hσ V
      have e1 := hdef (P.reduceFst V) h V rfl
      have e2 := hdef (P.reduceFst V) h _ hVσ
      refine e2.trans (Eq.trans ?_ e1.symm)
      obtain ⟨h₁pos, -, h₁law⟩ := hdq (P.reduceFst V) h V rfl
      obtain ⟨h₂pos, -, h₂law⟩ := hdq (P.reduceFst V) h _ hVσ

      set y : ↥(modularFunctionFieldBar (1 * q)) :=
        (((coord (P.reduceFst V) h).y : ↥(R.nodeIntegersOver (K (P.reduceFst V)) (P.reduceFst V))) :
          ↥(modularFunctionFieldBar (1 * q))) with hy
      have hyO := ((coord (P.reduceFst V) h).y : ↥(R.nodeIntegersOver (K (P.reduceFst V)) (P.reduceFst V))).2
      have hVrat : V.IsRational := (Place.isRational_iff_deg_eq_one V).mpr (deg_eq_one_modularFunctionFieldBar (1 * q) V)
      have hval : (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V).evalAt y = σ (V.evalAt y) :=
        (ModularCurve.arithmeticGalois_smul_eq_self_and_evalAt_smul_of_coe_mem_fieldOver (1 * q) (K (P.reduceFst V)) σ
          (hKfix _ h σ hσ) y hyO.2).2 V hVrat
      have hyD : ∀ V', (coord (P.reduceFst V) h).yDepth V' = A.valuation (V'.evalAt y) := fun V' => rfl
      rw [hyD] at h₁law h₂law
      rw [hval] at h₂law

      have ht0 : V.evalAt y ≠ 0 := by
        intro h0
        rw [h0, map_zero, zero_pow (Rat.den_pos _).ne'] at h₁law
        exact (pow_ne_zero _ hγ0) h₁law.symm
      have h₁law' := valuation_pow_apply_eq hσ ht0 h₁law hq0
      exact rat_eq_of_pow_laws hγ0 hγ1 h₂pos.le h₁pos.le h₂law h₁law'
    · have hVσ : P.reduceFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) = P.reduceFst V := reduceFst_arithmeticGalois_smul P σ hσ V
      show (if h : P.reduceFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) ∈ W then _ else 0) = (if h : P.reduceFst V ∈ W then _ else 0)
      rw [dif_neg h, dif_neg (by rw [hVσ]; exact h)]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_depthQ_cleared_law_and_forall_inertia_smul_eq_levelOne (solution)
