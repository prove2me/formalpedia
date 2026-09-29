-- Prove2me | solution 1 for ModularCurve.coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8d376790-b883-51b8-bcf2-58d7778c4258

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Theorems.Thm_ModularCurve_finrankAlong_frobeniusModL
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_theta_qExpand
import Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq.ModularCurve AlgebraicCurve HahnSeries IntermediateField"

namespace ModularCurve
p2m_export "ModularCurve" "pow_char_eq_coeffMap_frobenius_qExpand charP_laurentSeriesC frobeniusModL coe_frobeniusModL exists_frobeniusModL_eq_pow frobeniusModL_isIntegral frobeniusDivPushforwardModL frobeniusPushforwardModL frobeniusPushforwardModL_mk modularFunctionFieldFullC jqModC_mem_full qExpand_injective coeffMap algebraMap_laurentSeries_eq_single coeffMap_qExpand thetaL thetaL_apply coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut qInftyPlaceMod deg_qInftyPlaceMod frobeniusInputsModL finrankAlong_frobeniusModL theta_mul theta_coeff theta_qExpand thetaL_coeffMap_eq_coeffMap_single_mul_derivative"
p2m_open "ModularCurve"

namespace FrobRationalDlog

section Series

variable {K : Type*} [Field K]

theorem dlog_mul {x y : LaurentSeries K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y)⁻¹ * thetaL K (x * y) = x⁻¹ * thetaL K x + y⁻¹ * thetaL K y := by
  rw [thetaL_apply, theta_mul, ← thetaL_apply, ← thetaL_apply, mul_add, add_comm]
  congr 1 <;> field_simp

theorem thetaL_C (c : K) : thetaL K (HahnSeries.C c) = 0 := by
  ext j
  rw [thetaL_apply, theta_coeff, C_apply, coeff_single, HahnSeries.coeff_zero]
  split_ifs with h
  · subst h; rw [zero_smul]
  · rw [smul_zero]

theorem dlog_C {c : K} (hc : c ≠ 0) : (HahnSeries.C c : LaurentSeries K)⁻¹ * thetaL K (HahnSeries.C c) = 0 := by
  rw [thetaL_C, mul_zero]

theorem thetaL_coeffMap (φ : K →+* K) (w : LaurentSeries K) :
    thetaL K (coeffMap φ w) = coeffMap φ (thetaL K w) := by
  rw [thetaL_coeffMap_eq_coeffMap_single_mul_derivative, ← thetaL_apply]

theorem dlog_coeffMap (φ : K →+* K) (w : LaurentSeries K) :
    (coeffMap φ w)⁻¹ * thetaL K (coeffMap φ w) = coeffMap φ (w⁻¹ * thetaL K w) := by
  rw [thetaL_coeffMap, map_mul, map_inv₀]

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP K ℓ]

theorem thetaL_pow_char (x : LaurentSeries K) : thetaL K (x ^ ℓ) = 0 := by
  haveI : CharP (LaurentSeries K) ℓ := charP_laurentSeriesC K ℓ
  rw [pow_char_eq_coeffMap_frobenius_qExpand ℓ x, thetaL_coeffMap, thetaL_apply, theta_qExpand,
    map_nsmul, ← thetaL_apply]
  rw [nsmul_eq_mul, show ((ℓ : ℕ) : LaurentSeries K) = 0 from CharP.cast_eq_zero _ ℓ, zero_mul]

theorem dlog_pow_char {x : LaurentSeries K} (hx : x ≠ 0) : (x ^ ℓ)⁻¹ * thetaL K (x ^ ℓ) = 0 := by
  rw [thetaL_pow_char, mul_zero]

end Series

section Norm

variable (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]

theorem frobeniusModL_norm (hfin : FiniteAlong K (frobeniusModL K N ℓ)) (f : modularFunctionFieldFullC K N) :
    frobeniusModL K N ℓ (letI := algebraAlong (frobeniusModL K N ℓ); Algebra.norm (modularFunctionFieldFullC K N) f) =
      f ^ ℓ := by
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI : @Module.Finite (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K N) _ _
    (algebraAlong (frobeniusModL K N ℓ)).toModule := hfin
  haveI : CharP (modularFunctionFieldFullC K N) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldFullC K N)).injective ℓ
  have hrank := finrankAlong_frobeniusModL K N (ℓ := ℓ)
  obtain ⟨y, hy⟩ := exists_frobeniusModL_eq_pow K N ℓ f

  have hN : (Algebra.norm (modularFunctionFieldFullC K N) f) ^ ℓ = y ^ ℓ := by
    rw [← map_pow, ← hy]
    change Algebra.norm (modularFunctionFieldFullC K N)
      (algebraMap (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K N) y) = y ^ ℓ
    rw [Algebra.norm_algebraMap]
    change y ^ finrankAlong K (frobeniusModL K N ℓ) = y ^ ℓ
    rw [hrank]
  have hNy : Algebra.norm (modularFunctionFieldFullC K N) f = y := frobenius_inj _ ℓ hN
  rw [hNy, hy]

theorem coe_norm_eq_coeffMap (hfin : FiniteAlong K (frobeniusModL K N ℓ)) (f : modularFunctionFieldFullC K N) :
    ((letI := algebraAlong (frobeniusModL K N ℓ); Algebra.norm (modularFunctionFieldFullC K N) f :
        modularFunctionFieldFullC K N) : LaurentSeries K) =
      coeffMap (frobenius K ℓ) (f : LaurentSeries K) := by
  haveI : CharP (LaurentSeries K) ℓ := charP_laurentSeriesC K ℓ
  have h := congrArg (fun z : modularFunctionFieldFullC K N => (z : LaurentSeries K)) (frobeniusModL_norm K ℓ N hfin f)
  simp only [coe_frobeniusModL] at h
  apply qExpand_injective ℓ
  rw [h]
  push_cast
  rw [pow_char_eq_coeffMap_frobenius_qExpand ℓ (f : LaurentSeries K), coeffSemilinearAut.coeffMap_qExpand]

end Norm

section Main

variable {K : Type*} [Field K] [IsAlgClosed K] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ] {N : ℕ} [NeZero N]

theorem main
    (D : Divisor K (modularFunctionFieldFullC K N))
    (hD0 : D ∈ Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N))
    (f : modularFunctionFieldFullC K N) (hf : f ≠ 0)
    (hD : ∀ v : Place K (modularFunctionFieldFullC K N), (ℓ : ℤ) * D v = v.ord f)
    (hFr : frobeniusPushforwardModL K N ℓ (Pic0.mk ⟨D, hD0⟩) = Pic0.mk ⟨D, hD0⟩) :
    coeffMap (frobenius K ℓ) ((f : LaurentSeries K)⁻¹ * thetaL K (f : LaurentSeries K)) =
      (f : LaurentSeries K)⁻¹ * thetaL K (f : LaurentSeries K) := by
  obtain ⟨hP, hfin, hFI, hN⟩ := frobeniusInputsModL K (ℓ := ℓ) N
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI := isScalarTower_along (frobeniusModL K N ℓ)
  haveI := isIntegral_along (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
  haveI : @Module.Finite (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K N) _ _
    (algebraAlong (frobeniusModL K N ℓ)).toModule := hfin
  set Nf : modularFunctionFieldFullC K N := Algebra.norm (modularFunctionFieldFullC K N) f with hNf

  have hpush : ∀ v : Place K (modularFunctionFieldFullC K N),
      (ℓ : ℤ) * frobeniusDivPushforwardModL K N ℓ D v = v.ord Nf := by
    intro v
    have hE' : ∀ w : Place K (modularFunctionFieldFullC K N), ((ℓ : ℤ) • D) w = w.ord f := fun w => by
      rw [Finsupp.smul_apply, smul_eq_mul, hD w]
    have h := hN f hf ((ℓ : ℤ) • D) hE' v
    rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
    exact h

  have hprin : Divisor.IsPrincipal (frobeniusDivPushforwardModL K N ℓ D - D) := by
    rw [frobeniusPushforwardModL_mk hfin hFI hN, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf] at hFr
    exact hFr
  obtain ⟨h, hh, hDh⟩ := hprin

  have hNf0 : Nf ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  set u : modularFunctionFieldFullC K N := Nf / (f * h ^ ℓ) with hu
  have hu0 : u ≠ 0 := div_ne_zero hNf0 (mul_ne_zero hf (pow_ne_zero _ hh))
  have hord : ∀ v : Place K (modularFunctionFieldFullC K N), v.ord u = 0 := by
    intro v
    rw [hu, div_eq_mul_inv, v.ord_mul hNf0 (inv_ne_zero (mul_ne_zero hf (pow_ne_zero _ hh))),
      v.ord_inv, v.ord_mul hf (pow_ne_zero _ hh), ← zpow_natCast, v.ord_zpow, ← hpush v, ← hD v]
    have := hDh v
    rw [Finsupp.sub_apply] at this
    rw [← this]
    ring
  have hC : ConstantsAreBase K (modularFunctionFieldFullC K N) :=
    constantsAreBase_of_deg_eq_one (qInftyPlaceMod K (jqModC_mem_full K N))
      (deg_qInftyPlaceMod K (jqModC_mem_full K N))
  have hmem : u ∈ LSpace (0 : Divisor K (modularFunctionFieldFullC K N)) := by
    rw [mem_lSpace_iff_ord]
    exact Or.inr fun v => by rw [hord v, Finsupp.zero_apply, neg_zero]
  rw [ConstantsAreBase] at hC
  rw [hC] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hu0
    rw [← hc]
    exact map_zero _
  have hNfeq : Nf = algebraMap K _ c * f * h ^ ℓ := by
    have : algebraMap K (modularFunctionFieldFullC K N) c = u := hc
    rw [this, hu, mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hf (pow_ne_zero _ hh))]

  have hf' : (f : LaurentSeries K) ≠ 0 := fun e => hf (Subtype.ext e)
  have hh' : (h : LaurentSeries K) ≠ 0 := fun e => hh (Subtype.ext e)
  have hσf : coeffMap (frobenius K ℓ) (f : LaurentSeries K) =
      HahnSeries.C c * (f : LaurentSeries K) * (h : LaurentSeries K) ^ ℓ := by
    rw [← coe_norm_eq_coeffMap K ℓ N hfin f]
    change ((Nf : modularFunctionFieldFullC K N) : LaurentSeries K) = _
    rw [hNfeq]
    push_cast
    congr 1
    congr 1
    change algebraMap K (LaurentSeries K) c = HahnSeries.C c
    rw [algebraMap_laurentSeries_eq_single, C_apply]

  have hCc : (HahnSeries.C c : LaurentSeries K) ≠ 0 := C_ne_zero hc0
  rw [← dlog_coeffMap, hσf, dlog_mul (mul_ne_zero hCc hf') (pow_ne_zero _ hh'), dlog_mul hCc hf',
    dlog_C hc0, zero_add, dlog_pow_char ℓ hh', add_zero]

end Main

end FrobRationalDlog

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq.ModularCurve AlgebraicCurve in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (D : Divisor K (modularFunctionFieldFullC K N))
    (hD0 : D ∈ Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N))
    (f : modularFunctionFieldFullC K N) (hf : f ≠ 0)
    (hD : ∀ v : Place K (modularFunctionFieldFullC K N), (ℓ : ℤ) * D v = v.ord f)
    (hFr : frobeniusPushforwardModL K N ℓ (Pic0.mk ⟨D, hD0⟩) = Pic0.mk ⟨D, hD0⟩) :
    coeffMap (frobenius K ℓ) ((f : LaurentSeries K)⁻¹ * thetaL K (f : LaurentSeries K)) =
      (f : LaurentSeries K)⁻¹ * thetaL K (f : LaurentSeries K) :=
  ModularCurve.FrobRationalDlog.main D hD0 f hf hD hFr

end S_ModularCurve_coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq
end P2MW
export P2MW.S_ModularCurve_coeffMap_frobenius_inv_mul_thetaL_eq_of_frobeniusPushforwardModL_eq (solution)
