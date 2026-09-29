-- Prove2me | solution 1 for ModularCurve.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/12170f76-8558-5431-80b0-519866f8e2a6

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_sharpUnitInvariant
import Theorems.Thm_ModularCurve_sharpUnitSeries_mem_modularFunctionField
import Theorems.Thm_ModularCurve_sharpUnitSeries_pow_sharpIndex
import Theorems.Thm_ModularCurve_smul_cuspidalDivisor_apply_eq_ord
import Theorems.Thm_ModularCurve_full_eq_of_prime
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isPrincipal_eisensteinNumerator_smul_cuspidalDivisor
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

namespace SharpDivisor

open ModularCurve AlgebraicCurve

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

local notation "ℚ̄" => AlgebraicClosure ℚ

local instance neZero_of_fact_prime : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

theorem sharp_mem_full : sharpUnitSeries ℓ ∈ modularFunctionFieldFull ℓ := by
  rw [full_eq_of_prime hℓ.out]
  exact sharpUnitSeries_mem_modularFunctionField ℓ (sharpUnitInvariant ℓ)

def Gb : modularFunctionFieldBar ℓ :=
  ⟨coeffEmb ℚ̄ (sharpUnitSeries ℓ), coeffEmb_mem_laurentBaseChange ℚ̄ (sharp_mem_full ℓ)⟩

def ub : modularFunctionFieldBar ℓ :=
  ⟨coeffEmb ℚ̄ (modularUnitSeries ℓ),
    coeffEmb_mem_laurentBaseChange ℚ̄ (modularUnitSeries_mem_modularFunctionFieldFull ℓ)⟩

theorem Gb_pow : Gb ℓ ^ sharpIndex ℓ = ub ℓ := by
  apply Subtype.ext
  show coeffEmb ℚ̄ (sharpUnitSeries ℓ) ^ sharpIndex ℓ = coeffEmb ℚ̄ (modularUnitSeries ℓ)
  rw [← map_pow, sharpUnitSeries_pow_sharpIndex]

theorem ub_ne_zero : ub ℓ ≠ 0 := by
  intro h
  have h1 : coeffEmb ℚ̄ (modularUnitSeries ℓ) = 0 := congrArg Subtype.val h
  apply modularUnitSeries_ne_zero ℓ
  ext m
  have := congrArg (fun s => HahnSeries.coeff s m) h1
  simp only [coeffEmb_coeff] at this
  simpa using this

theorem Gb_ne_zero : Gb ℓ ≠ 0 := fun h =>
  ub_ne_zero ℓ (by rw [← Gb_pow, h, zero_pow (sharpIndex_pos ℓ).ne'])

theorem isPrincipal_eisensteinNumerator_smul_cuspidalDivisor :
    Divisor.IsPrincipal ((eisensteinNumerator ℓ : ℤ) • cuspidalDivisor ℓ) := by
  refine ⟨Gb ℓ, Gb_ne_zero ℓ, fun v => ?_⟩
  have hDU : (((ℓ : ℤ) - 1) • cuspidalDivisor ℓ) v = v.ord (ub ℓ) :=
    smul_cuspidalDivisor_apply_eq_ord ℓ (modularUnitSeries_mem_modularFunctionFieldFull ℓ) v
  have hk0 : (sharpIndex ℓ : ℤ) ≠ 0 := by exact_mod_cast (sharpIndex_pos ℓ).ne'
  have hkn : ((ℓ : ℤ) - 1) = (sharpIndex ℓ : ℤ) * (eisensteinNumerator ℓ : ℤ) := by
    have h := sharpIndex_mul_eisensteinNumerator ℓ
    have h1 : ((sharpIndex ℓ * eisensteinNumerator ℓ : ℕ) : ℤ) = ((ℓ - 1 : ℕ) : ℤ) := by rw [h]
    push_cast [Nat.cast_sub hℓ.out.one_le] at h1
    linear_combination -h1
  have hpow : v.ord (ub ℓ) = (sharpIndex ℓ : ℤ) * v.ord (Gb ℓ) := by
    rw [← Gb_pow, ← zpow_natCast, v.ord_zpow]
  rw [Finsupp.smul_apply, smul_eq_mul] at hDU ⊢
  rw [hkn, hpow, mul_assoc] at hDU
  exact mul_left_cancel₀ hk0 hDU

end SharpDivisor

end

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : AlgebraicCurve.Divisor.IsPrincipal ((ModularCurve.eisensteinNumerator ℓ : ℤ) • ModularCurve.cuspidalDivisor ℓ) := by
  exact SharpDivisor.isPrincipal_eisensteinNumerator_smul_cuspidalDivisor ℓ

end S_ModularCurve_isPrincipal_eisensteinNumerator_smul_cuspidalDivisor
end P2MW
export P2MW.S_ModularCurve_isPrincipal_eisensteinNumerator_smul_cuspidalDivisor (solution)
