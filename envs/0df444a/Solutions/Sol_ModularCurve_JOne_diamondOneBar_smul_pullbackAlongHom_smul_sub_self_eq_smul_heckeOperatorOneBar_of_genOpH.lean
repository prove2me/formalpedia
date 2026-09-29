-- Prove2me | solution 1 for ModularCurve.JOne.diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b7dad723-8197-54f1-b73d-936e7f02c315

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_XHHeckeOperator
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Theorems.Thm_ModularCurve_coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq
import Theorems.Thm_ModularCurve_pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
open ModularCurve
open scoped MatrixGroups

open AlgebraicCurve in
theorem pullbackAlongHom_smul' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F) :
    Pic0.pullbackAlongHom φ hφ hFI (g • x) = g' • Pic0.pullbackAlongHom φ hφ hFI x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  show Divisor.pullbackAlong φ hφ (g • (D : Divisor K F)) =
    g' • Divisor.pullbackAlong φ hφ (D : Divisor K F)
  exact SemilinearAut.pullbackAlong_smul φ hφ hgg' D

open ModularCurve AlgebraicCurve in
theorem intertwines_arith (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (ι : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) →ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁))
    (hι : ∀ x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀),
      ((ι x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    SemilinearAut.IntertwinesAlong ι.toRingHom (arithmeticGalois F₀ τ) (arithmeticGalois F₁ τ) := by
  intro x
  apply Subtype.ext
  have h1 : ((arithmeticGalois F₁ τ • ι.toRingHom x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (τ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) ((ι.toRingHom x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    coe_arithmeticGalois_smul F₁ τ _
  have h2 : ((ι.toRingHom x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) := hι x
  have h3 : ((ι.toRingHom (arithmeticGalois F₀ τ • x) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₁)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((arithmeticGalois F₀ τ • x : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) := hι _
  rw [h1, h2, h3, coe_arithmeticGalois_smul]

namespace TransportAsm

open AlgebraicCurve

theorem gamma1_inf_gamma0_eq (M q : ℕ) [NeZero M] (hMq : Nat.Coprime M q) :
    CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 q =
      CohCarrier.GammaH M ⊥ ⊓ CongruenceSubgroup.Gamma0 (M * q) := by
  ext A
  simp only [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, CohCarrier.mem_GammaH_iff,
    Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h00, h11, h10⟩, hq⟩
    have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
    refine ⟨⟨hA0, ?_⟩, ?_⟩
    · apply Units.ext
      rw [CohCarrier.val_gamma0Units, Units.val_one]
      exact h11
    ·
      have hM : (M : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
      have hq' : (q : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hq
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul]
      exact (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using hMq)).mul_dvd hM hq'
  · rintro ⟨⟨hA0, hu⟩, hMq'⟩
    have h10 : ((A 1 0 : ℤ) : ZMod M) = 0 := CongruenceSubgroup.Gamma0_mem.mp hA0
    have h11 : ((A 1 1 : ℤ) : ZMod M) = 1 := by
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hu
      first
        | simpa [CohCarrier.val_gamma0Units] using this
        | (have h' := this; simp [CohCarrier.val_gamma0Units] at h'; exact h')
        | (simp [CohCarrier.val_gamma0Units]; exact this)
        | exact this
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have h00 : ((A 0 0 : ℤ) : ZMod M) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod M)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h10, h11, mul_one, mul_zero, sub_zero] at this
      exact this
    refine ⟨⟨h00, h11, h10⟩, ?_⟩
    have hc : ((M * q : ℕ) : ℤ) ∣ A 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hMq'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans ⟨M, by push_cast; ring⟩ hc

end TransportAsm

set_option maxHeartbeats 3200000 in
open AlgebraicCurve in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (M₀ q : ℕ) [NeZero M₀] (hq : q.Prime) (hqM₀ : ¬ q ∣ M₀)
    (hin : ModularCurve.HeckeDiamondInputsAll (M₀ * q))
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M₀ * q))]
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q))
        →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M₀ * q)))
    (hι : ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q),
      ((ι x : ModularCurve.x1FunctionFieldBar (M₀ * q)) : LaurentSeries (AlgebraicClosure ℚ))
        = (x : LaurentSeries (AlgebraicClosure ℚ)))
    (hint : ι.toRingHom.IsIntegral)
    (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hτ : P.IsFrobeniusAt τ q)
    (z : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M₀ q)))
    (n : ℕ) (hn : ¬ q ∣ n) (hz : (n : ℤ) • z = 0)
    (d₁ : ℕ) (hd₁ : Nat.Coprime d₁ (M₀ * q)) (hd₁q : d₁ ≡ q [MOD M₀])

    (S : Set ℕ)
    (hJH : ∀ (z' : JH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))))
        (n' : ℕ), ¬ q ∣ n' → (n' : ℤ) • z' = 0 →
      genOpH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) S
          (CohCarrier.Gen.dia (ZMod.unitOfCoprime d₁ hd₁)) (τ • (σ • z' - z')) =
        (q : ℤ) • genOpH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) S
          (CohCarrier.Gen.U q hq (Dvd.intro_left M₀ rfl)) (σ • z' - z')) :
    ModularCurve.diamondOneBar (M₀ * q) d₁
        (τ • AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • z - z)) =
      (q : ℤ) • ModularCurve.heckeOperatorOneBar (M₀ * q) ⟨q, hq⟩
        (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • z - z))
 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (M₀ * q) := ⟨mul_ne_zero (NeZero.ne M₀) hq.ne_zero⟩

  have hcop : Nat.Coprime M₀ q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqM₀ |>.symm
  have hgrp : CongruenceSubgroup.Gamma1 M₀ ⊓ CongruenceSubgroup.Gamma0 q =
      CohCarrier.GammaH (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) := by
    rw [TransportAsm.gamma1_inf_gamma0_eq M₀ q hcop]
    exact CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap M₀ q ⊥
  have hfield : ModularCurve.x1x0FunctionFieldC ℚ M₀ q = xHFunctionField (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) := by
    show qExpFunctionFieldC ℚ _ = qExpFunctionFieldC ℚ _
    rw [hgrp]

  revert ι z
  rw [hfield]
  intro ι hι hint hFI z hz

  have key := hJH z n hn hz
  rw [genOpH_dia, genOpH_U, diamondHBar_apply] at key
  have key2 := congrArg (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI) key
  rw [map_zsmul] at key2

  rw [ModularCurve.pullbackAlongHom_heckeOperatorHAlong_eq_heckeOperatorOneBar_pullbackAlongHom (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) hin
    ι hι hint hFI q hq (Dvd.intro_left M₀ rfl)] at key2

  have hdia : AlgebraicCurve.SemilinearAut.IntertwinesAlong ι.toRingHom
      (SemilinearAut.ofAlgAut (diamondAutHBar (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) (ZMod.unitOfCoprime d₁ hd₁)))
      (SemilinearAut.ofAlgAut (diamondAutBar (M₀ * q) d₁)) := by
    intro x
    rw [AlgebraicCurve.SemilinearAut.ofAlgAut_smul, AlgebraicCurve.SemilinearAut.ofAlgAut_smul]
    exact (ModularCurve.coe_diamondAutHBar_eq_diamondAutBar_of_coe_eq (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q))) hin ι hι d₁ hd₁ x).symm
  rw [pullbackAlongHom_smul' ι hint hFI hdia] at key2

  have hgal := intertwines_arith (xHFunctionField (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q)))) (x1FunctionField (M₀ * q)) ι hι τ
  have hτ' : AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (τ • (σ • z - z)) =
      τ • AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • z - z) := by
    rw [galois_smul_pic0_def (xHFunctionField (M₀ * q) ((⊥ : Subgroup (ZMod M₀)ˣ).comap (ZMod.unitsMap (Dvd.intro q rfl : M₀ ∣ M₀ * q)))) τ (σ • z - z),
      galois_smul_pic0_def (x1FunctionField (M₀ * q)) τ (AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI (σ • z - z))]
    exact pullbackAlongHom_smul' ι hint hFI hgal _
  rw [hτ'] at key2
  rw [diamondOneBar_apply]
  exact key2

end S_ModularCurve_JOne_diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH
end P2MW
export P2MW.S_ModularCurve_JOne_diamondOneBar_smul_pullbackAlongHom_smul_sub_self_eq_smul_heckeOperatorOneBar_of_genOpH (solution)
