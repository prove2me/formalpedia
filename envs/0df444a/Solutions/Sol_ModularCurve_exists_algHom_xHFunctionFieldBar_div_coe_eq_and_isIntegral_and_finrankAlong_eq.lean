-- Prove2me | solution 1 for ModularCurve.exists_algHom_xHFunctionFieldBar_div_coe_eq_and_isIntegral_and_finrankAlong_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4045e289-c678-5952-aab7-2c4ee4ee9f56

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_XHHeckeOperator
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algHom_xHFunctionFieldBar_div_coe_eq_and_isIntegral_and_finrankAlong_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve
open scoped MatrixGroups

namespace R1V4AlphaH

theorem gammaH_eq_inf (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * p) =
      CohCarrier.GammaH M H := by
  have hM : M / p * p = M := Nat.div_mul_cancel hpM
  rw [hM]

  have hval : ∀ (A : SL(2, ℤ)) (hA : A ∈ CongruenceSubgroup.Gamma0 M) (hA' : A ∈ CongruenceSubgroup.Gamma0 (M / p)),
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨A, hA⟩) =
        CohCarrier.gamma0Units (M / p) ⟨A, hA'⟩ := by
    intro A hA hA'
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
      CohCarrier.val_gamma0Units]
    simp [CongruenceSubgroup.Gamma0Map]
  have h0 : ∀ A : SL(2, ℤ), A ∈ CongruenceSubgroup.Gamma0 M → A ∈ CongruenceSubgroup.Gamma0 (M / p) := by
    intro A hA
    rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
    have := congrArg (ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p))) hA
    simpa using this
  ext A
  simp only [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨⟨hA', hH'⟩, hA⟩
    refine ⟨hA, ?_⟩
    rw [mem_infSubgroup_iff] at hH'
    obtain ⟨d, hd, hdeq⟩ := hH'
    rw [← hval A hA hA'] at hdeq
    have hmem : CohCarrier.gamma0Units M ⟨A, hA⟩ * d⁻¹ ∈ H := by
      apply hHp
      rw [map_mul, map_inv, hdeq, mul_inv_cancel]
    simpa using H.mul_mem hmem hd
  · rintro ⟨hA, hH⟩
    refine ⟨⟨h0 A hA, ?_⟩, hA⟩
    rw [mem_infSubgroup_iff]
    exact ⟨_, hH, hval A hA (h0 A hA)⟩

theorem fields_eq (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)) =
      xHFunctionFieldBar M H := by
  show laurentBaseChange (AlgebraicClosure ℚ)
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 (M / p * p))) =
    laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
  rw [gammaH_eq_inf p M H hpM hHp]

section Maps

variable (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)

attribute [local irreducible] ModularCurve.laurentBaseChange ModularCurve.qExpFunctionFieldC CohCarrier.GammaH

set_option quotPrecheck false
local notation "L" => AlgebraicClosure ℚ
local notation "FTop" => ↥(laurentBaseChange (AlgebraicClosure ℚ)
  (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
local notation "FM" => ↥(xHFunctionFieldBar M H)

noncomputable def φ : FMp →ₐ[L] FTop := heckeAlphaHBar L (M / p) (infSubgroup p M H hpM) p

noncomputable def E : FTop ≃ₐ[L] FM where
  toFun x := ⟨(x : LaurentSeries L), (fields_eq p M H hpM hHp).le x.2⟩
  invFun y := ⟨(y : LaurentSeries L), (fields_eq p M H hpM hHp).ge y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

noncomputable def α : FMp →ₐ[L] FM := (E p M H hpM hHp).toAlgHom.comp (φ p M H hpM)

theorem E_apply (x : FTop) :
    E p M H hpM hHp x = ⟨(x : LaurentSeries L), (fields_eq p M H hpM hHp).le x.2⟩ := rfl

theorem coe_E (x : FTop) : ((E p M H hpM hHp x : FM) : LaurentSeries L) = (x : LaurentSeries L) := by
  rw [E_apply]

theorem α_apply (u : FMp) : α p M H hpM hHp u = E p M H hpM hHp (φ p M H hpM u) := rfl

theorem coe_α (u : FMp) : ((α p M H hpM hHp u : FM) : LaurentSeries L) = (u : LaurentSeries L) := by
  rw [α_apply, coe_E]
  exact coe_heckeAlphaHBar (M / p) (infSubgroup p M H hpM) p u

include hpM in
theorem not_dvd_div (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := by
  intro h
  apply hpM2
  have : p * p ∣ M / p * p := Nat.mul_dvd_mul_right h p
  rw [Nat.div_mul_cancel hpM] at this
  simpa [pow_two] using this

variable [Fact p.Prime] [NeZero M]

theorem finrankAlong_φ (hpM2 : ¬ p ^ 2 ∣ M) : AlgebraicCurve.finrankAlong L (φ p M H hpM) = p + 1 := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  exact ModularCurve.finrankAlong_heckeAlphaHBar L (M / p) (infSubgroup p M H hpM) (not_dvd_div p M hpM hpM2)

theorem isIntegral_φ (hpM2 : ¬ p ^ 2 ∣ M) : (φ p M H hpM).toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong (φ p M H hpM)
  have hpos : 0 < Module.finrank FMp FTop := by
    show 0 < AlgebraicCurve.finrankAlong L (φ p M H hpM)
    rw [finrankAlong_φ p M H hpM hpM2]
    exact Nat.succ_pos p
  haveI := Module.finite_of_finrank_pos hpos
  haveI : Algebra.IsIntegral FMp FTop := inferInstance
  intro x
  exact Algebra.IsIntegral.isIntegral x

theorem isIntegral_α (hpM2 : ¬ p ^ 2 ∣ M) : (α p M H hpM hHp).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans (φ p M H hpM).toRingHom (E p M H hpM hHp).toAlgHom.toRingHom
    (isIntegral_φ p M H hpM hpM2) (RingHom.isIntegral_of_surjective _ (E p M H hpM hHp).surjective)

noncomputable def Elin :
    letI := AlgebraicCurve.algebraAlong (φ p M H hpM)
    letI := AlgebraicCurve.algebraAlong (α p M H hpM hHp)
    FTop ≃ₗ[FMp] FM :=
  letI := AlgebraicCurve.algebraAlong (φ p M H hpM)
  letI := AlgebraicCurve.algebraAlong (α p M H hpM hHp)
  { (E p M H hpM hHp).toRingEquiv.toAddEquiv with
    map_smul' := fun f x => by
      show E p M H hpM hHp (φ p M H hpM f * x) = α p M H hpM hHp f * E p M H hpM hHp x
      rw [map_mul]
      rfl }

theorem finrankAlong_α (hpM2 : ¬ p ^ 2 ∣ M) : AlgebraicCurve.finrankAlong L (α p M H hpM hHp) = p + 1 := by
  rw [← finrankAlong_φ p M H hpM hpM2]
  letI := AlgebraicCurve.algebraAlong (φ p M H hpM)
  letI := AlgebraicCurve.algebraAlong (α p M H hpM hHp)
  exact (LinearEquiv.finrank_eq (Elin p M H hpM hHp)).symm

end Maps

end R1V4AlphaH

open R1V4AlphaH in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ∃ α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H),
      (∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      α.IsIntegral ∧
      AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) α = p + 1 ∧
      ∀ θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H), (θ.toAlgHom.comp α).IsIntegral :=
  ⟨R1V4AlphaH.α p M H hpM hHp, coe_α p M H hpM hHp, isIntegral_α p M H hpM hHp hpM2,
    finrankAlong_α p M H hpM hHp hpM2, fun θ =>
      RingHom.IsIntegral.trans (R1V4AlphaH.α p M H hpM hHp).toRingHom θ.toAlgHom.toRingHom
        (isIntegral_α p M H hpM hHp hpM2) (RingHom.isIntegral_of_surjective _ θ.surjective)⟩

end S_ModularCurve_exists_algHom_xHFunctionFieldBar_div_coe_eq_and_isIntegral_and_finrankAlong_eq
end P2MW
export P2MW.S_ModularCurve_exists_algHom_xHFunctionFieldBar_div_coe_eq_and_isIntegral_and_finrankAlong_eq (solution)
