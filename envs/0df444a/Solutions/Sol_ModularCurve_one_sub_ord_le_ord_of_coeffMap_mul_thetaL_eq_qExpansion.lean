-- Prove2me | solution 1 for ModularCurve.one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/13492e4c-2c97-5737-8931-6f110c8eac11

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_intermediateField_mk
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap
import Theorems.Thm_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open UpperHalfPlane ModularCurve AlgebraicCurve

namespace Sol

theorem thetaL_coeff' {L : Type*} [Field L] (x : LaurentSeries L) (n : ℤ) :
    (thetaL L x).coeff n = (n : L) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem coeffMap_thetaL {L₁ L₂ : Type*} [Field L₁] [Field L₂] (σ : L₁ →+* L₂)
    (x : LaurentSeries L₁) :
    coeffMap σ (thetaL L₁ x) = thetaL L₂ (coeffMap σ x) := by
  ext n
  simp only [coeffMap_coeff, thetaL_coeff', map_mul, map_intCast]

theorem coeffMap_coeffEmb' {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂]
    (σ : L₁ →+* L₂) (x : LaurentSeries ℚ) :
    coeffMap σ (coeffEmb L₁ x) = coeffEmb L₂ x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap,
    Subsingleton.elim (σ.comp (algebraMap ℚ L₁)) (algebraMap ℚ L₂)]

theorem ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (f : F)
    (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

end Sol

open Sol in
theorem solution (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (y : modularFunctionFieldBar N) (hy0 : y ≠ 0)
    (hy : coeffMap σ ((y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) < 0) :
    1 - w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ≤ w.ord y := by

  set K := AlgebraicClosure ℚ with hK
  let F : IntermediateField K (LaurentSeries K) := modularFunctionFieldBar N
  let jb : F := ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩
  let c : F := algebraMap K F 1728
  change w.ord jb < 0 at hw
  change 1 - w.ord jb ≤ w.ord y

  have hj0 : jb ≠ 0 := fun h => by rw [h, Place.ord_zero] at hw; exact lt_irrefl _ hw
  have hc0 : c ≠ 0 := by
    show algebraMap K F 1728 ≠ 0
    rw [map_ne_zero_iff _ (algebraMap K F).injective]; norm_num
  have hjc0 : jb - c ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, Place.ord_algebraMap] at hw
    exact lt_irrefl _ hw

  have hjc : w.ord (jb - c) ≤ w.ord jb := by
    have h := Place.min_ord_le_ord_add w hjc0 hc0 (by rwa [sub_add_cancel])
    rw [sub_add_cancel, Place.ord_algebraMap] at h
    omega
  have ht : 0 ≤ w.ord jb⁻¹ := by rw [Place.ord_inv]; omega

  set u : F := y ^ (2 * N) * jb ^ (N + 1) * (jb - c) ^ N with hu
  have hI := isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion N f
    (coeffMap σ (y : LaurentSeries K)) (by
      rw [← coeffMap_coeffEmb' σ, ← coeffMap_thetaL, ← map_mul, hy])
  have hD : IsIntegral
      (Algebra.adjoin K ({((jb⁻¹ : F) : LaurentSeries K)} : Set (LaurentSeries K)))
      (u : LaurentSeries K) := by
    refine isIntegral_adjoin_of_isIntegral_adjoin_coeffMap σ _ _ ?_
    have hcoe : ((u : F) : LaurentSeries K) =
        (y : LaurentSeries K) ^ (2 * N) * coeffEmb K jq ^ (N + 1) * (coeffEmb K jq - 1728) ^ N := by
      show F.val u = _
      simp only [hu, c, map_mul, map_pow, map_sub, map_ofNat]
      rfl
    have hj : ((jb⁻¹ : F) : LaurentSeries K) = (coeffEmb K jq)⁻¹ := by
      show F.val jb⁻¹ = _
      rw [map_inv₀]
      rfl
    rw [hcoe, hj, map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, map_inv₀,
      coeffMap_coeffEmb', map_ofNat]
    exact hI
  have hu0 : 0 ≤ w.ord u :=
    Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg w
      (by first | exact isIntegral_adjoin_intermediateField_mk F (jb⁻¹).2 u.2 hD | simpa using isIntegral_adjoin_intermediateField_mk F (jb⁻¹).2 u.2 hD) ht

  have hA : y ^ (2 * N) * jb ^ (N + 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hy0) (pow_ne_zero _ hj0)
  have hB : (jb - c) ^ N ≠ 0 := pow_ne_zero _ hjc0
  rw [hu, w.ord_mul hA hB, w.ord_mul (pow_ne_zero _ hy0) (pow_ne_zero _ hj0), ord_pow',
    ord_pow', ord_pow'] at hu0
  push_cast at hu0
  have hN : (1 : ℤ) ≤ N := by exact_mod_cast NeZero.one_le
  by_contra hlt
  push Not at hlt
  have h1 : (N : ℤ) * w.ord y ≤ (N : ℤ) * (-w.ord jb) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  have h2 : (N : ℤ) * w.ord (jb - c) ≤ (N : ℤ) * w.ord jb :=
    mul_le_mul_of_nonneg_left hjc (by positivity)
  linarith

end S_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion (solution)
