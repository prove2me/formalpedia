-- Prove2me | solution 1 for ModularCurve.exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aaca695a-7b97-55a8-879c-741ad509ea6c

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_atkinLehner_qExpand_pin_of_pin
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar_pos_and_le_relIndex
import Theorems.Thm_ModularCurve_Gamma0_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine"
p2m_attr_erase "instance" "ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve AlgebraicCurve Polynomial

namespace WNormSwapSol

local notation "Qb" => AlgebraicClosure ℚ

scoped instance (priority := low) neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p :=
  ⟨hp.out.ne_zero⟩

section TestElement

open ModularForm UpperHalfPlane EisensteinSeries
open scoped MatrixGroups ModularForm

def P4 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℤ)

def P6 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℤ)

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) P4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, P4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) P6 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, P6, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel]
    push_cast
    ring

variable (Γ : Subgroup SL(2, ℤ))

def A12 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((E₄.pow 3).mcast (by norm_num))

def B12 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) ((E₆.pow 2).mcast (by norm_num))

theorem isIntegralQExp_A12 : IsIntegralQExp (A12 Γ : ℍ → ℂ) (P4 ^ 3) := by
  rw [IsIntegralQExp, A12, coe_restrictForm, map_pow, isIntegralQExp_E4]
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem isIntegralQExp_B12 : IsIntegralQExp (B12 Γ : ℍ → ℂ) (P6 ^ 2) := by
  rw [IsIntegralQExp, B12, coe_restrictForm, map_pow, isIntegralQExp_E6]
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem constantCoeff_P4 : PowerSeries.constantCoeff P4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P4, PowerSeries.coeff_mk]; simp

theorem constantCoeff_P6 : PowerSeries.constantCoeff P6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P6, PowerSeries.coeff_mk]; simp

theorem coeff_one_P4 : PowerSeries.coeff 1 P4 = 240 := by
  rw [P4, PowerSeries.coeff_mk]; simp [ArithmeticFunction.sigma_one]

theorem coeff_one_P6 : PowerSeries.coeff 1 P6 = -504 := by
  rw [P6, PowerSeries.coeff_mk]; simp [ArithmeticFunction.sigma_one]

def A4Q : PowerSeries ℚ := (P4 ^ 3).map (Int.castRingHom ℚ)

def B6Q : PowerSeries ℚ := (P6 ^ 2).map (Int.castRingHom ℚ)

theorem constantCoeff_A4Q : PowerSeries.constantCoeff A4Q = 1 := by
  rw [A4Q, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P4, one_pow, map_one]

theorem constantCoeff_B6Q : PowerSeries.constantCoeff B6Q = 1 := by
  rw [B6Q, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P6, one_pow, map_one]

theorem coeff_one_A4Q : PowerSeries.coeff 1 A4Q = 720 := by
  rw [A4Q, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P4, constantCoeff_P4]
  norm_num

theorem coeff_one_B6Q : PowerSeries.coeff 1 B6Q = -1008 := by
  rw [B6Q, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P6, constantCoeff_P6]
  norm_num

theorem isUnit_A4Q : IsUnit A4Q :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_A4Q]; exact isUnit_one)

def XQ : PowerSeries ℚ := B6Q * ↑(isUnit_A4Q.unit⁻¹)

theorem XQ_mul_A : XQ * A4Q = B6Q := by
  rw [XQ, mul_assoc, IsUnit.val_inv_mul, mul_one]

theorem coeff_one_XQ : PowerSeries.coeff 1 XQ = -1728 := by
  have h0 : PowerSeries.constantCoeff XQ = 1 := by
    have h := congrArg PowerSeries.constantCoeff XQ_mul_A
    rw [map_mul, constantCoeff_A4Q, mul_one, constantCoeff_B6Q] at h
    exact h
  have h1 := congrArg (PowerSeries.coeff 1) XQ_mul_A
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton] at h1
  simp only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, one_mul, coeff_one_A4Q,
    constantCoeff_A4Q, mul_one, coeff_one_B6Q] at h1
  linarith

def xq : LaurentSeries ℚ := intSeriesC ℚ (P6 ^ 2) / intSeriesC ℚ (P4 ^ 3)

theorem intSeriesC_ne_zero_of_constantCoeff {K : Type*} [Field K] [CharZero K] {p : PowerSeries ℤ}
    (hp : PowerSeries.constantCoeff p = 1) : intSeriesC K p ≠ 0 := by
  intro h
  have := congrArg (fun z : LaurentSeries K => z.coeff 0) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at this
  rw [PowerSeries.coeff_coe] at this
  simp only [lt_self_iff_false, ↓reduceIte, Int.natAbs_zero, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, map_one, one_ne_zero] at this

theorem intSeriesC_P4_cube_ne_zero : intSeriesC ℚ (P4 ^ 3) ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff (by rw [map_pow, constantCoeff_P4, one_pow])

theorem xq_mem : xq ∈ qExpFunctionFieldC ℚ Γ :=
  div_mem_qExpFunctionFieldC (B12 Γ) (A12 Γ) (isIntegralQExp_B12 Γ) (isIntegralQExp_A12 Γ)
    intSeriesC_P4_cube_ne_zero

theorem xq_eq : xq = HahnSeries.ofPowerSeries ℤ ℚ XQ := by
  rw [xq, div_eq_iff intSeriesC_P4_cube_ne_zero, intSeriesC, intSeriesC, ← map_mul]
  change _ = HahnSeries.ofPowerSeries ℤ ℚ (XQ * A4Q)
  rw [XQ_mul_A]
  rfl

theorem xq_coeff_one : xq.coeff 1 = -1728 := by
  rw [xq_eq, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, coeff_one_XQ]

end TestElement

section Groups

open CongruenceSubgroup

theorem gamma0_le_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma0 B ≤ Gamma0 A := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have : ZMod.castHom h (ZMod A) (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod B)
      = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod A) := map_intCast _ _
  rw [← this, hγ, map_zero]

theorem GammaH_le_GammaH_div (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hA0' : A ∈ Gamma0 (M / p) := gamma0_le_of_dvd (Nat.div_dvd_of_dvd hpM) hA0
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hA0', ?_⟩
  rw [mem_infSubgroup_iff]
  refine ⟨CohCarrier.gamma0Units M ⟨A, hA0⟩, hAH, ?_⟩
  ext
  rw [ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  show ((((A 1 1 : ℤ) : ZMod M)).cast : ZMod (M / p)) = ((A 1 1 : ℤ) : ZMod (M / p))
  rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]

theorem dedekindPsi_mul_of_dvd {M p : ℕ} (hM : M ≠ 0) (hp : p ≠ 0) (hpM : p ∣ M) :
    dedekindPsi (M * p) = p * dedekindPsi M := by
  unfold dedekindPsi
  have hset : (M * p).divisors.filter Squarefree = M.divisors.filter Squarefree := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hsq⟩
      refine ⟨⟨?_, hM⟩, hsq⟩
      have h2 : d ∣ M ^ 2 := hd.trans (by rw [sq]; exact mul_dvd_mul_left M hpM)
      exact (hsq.dvd_pow_iff_dvd two_ne_zero).mp h2
    · rintro ⟨⟨hd, -⟩, hsq⟩
      exact ⟨⟨hd.mul_right p, mul_ne_zero hM hp⟩, hsq⟩
  rw [hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdM : d ∣ M := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  rw [mul_comm M p, Nat.mul_div_assoc p hdM]

theorem relIndex_le (p M : ℕ) [NeZero M] [NeZero p] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    (CohCarrier.GammaH M H ⊓ Gamma0 (M * p)).relIndex (CohCarrier.GammaH M H) ≤ p := by
  rw [Subgroup.inf_relIndex_left]
  have hle : Gamma0 (M * p) ≤ Gamma0 M := gamma0_le_of_dvd (dvd_mul_right M p)
  haveI : NeZero (M * p) := NeZero.mul
  haveI : (Gamma0 M).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_in_Gamma0 M)
  haveI : (Gamma0 (M * p)).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_in_Gamma0 (M * p))
  have hmul := Subgroup.relIndex_mul_index hle
  rw [ModularCurve.Gamma0_index, ModularCurve.Gamma0_index,
    dedekindPsi_mul_of_dvd (NeZero.ne M) (NeZero.ne p) hpM] at hmul
  have hpsi : dedekindPsi M ≠ 0 := by
    rw [← ModularCurve.Gamma0_index]; exact Subgroup.FiniteIndex.index_ne_zero
  have hidx : (Gamma0 (M * p)).relIndex (Gamma0 M) = p := Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero hpsi) hmul
  have hne : (Gamma0 (M * p)).relIndex (Gamma0 M) ≠ 0 := by rw [hidx]; exact NeZero.ne p
  calc (Gamma0 (M * p)).relIndex (CohCarrier.GammaH M H)
      ≤ (Gamma0 (M * p)).relIndex (Gamma0 M) :=
        Subgroup.relIndex_le_of_le_right (CohCarrier.GammaH_le_Gamma0 H) hne
    _ = p := hidx

end Groups

section Frame

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

abbrev FH : IntermediateField Qb (LaurentSeries Qb) := xHFunctionFieldBar M H

abbrev FH' : IntermediateField Qb (LaurentSeries Qb) :=
  xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)

abbrev Etop : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * p))

theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange Qb F₀ ≤ laurentBaseChange Qb F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange Qb (h hy)

theorem FH'_le : FH' p M H hpM ≤ FH M H :=
  laurentBaseChange_mono' (qExpFunctionFieldC_mono ℚ (GammaH_le_GammaH_div p M H hpM))

def incl : FH' p M H hpM →ₐ[Qb] FH M H := IntermediateField.inclusion (FH'_le p M H hpM)

@[scoped simp]
theorem coe_incl (u : FH' p M H hpM) : ((incl p M H hpM u : FH M H) : LaurentSeries Qb) = u :=
  IntermediateField.coe_inclusion _ u

variable {p M H hpM}

def Pin (θ : FH M H ≃ₐ[Qb] FH M H) : Prop :=
  ∀ (f : FH M H) (u : FH' p M H hpM), (f : LaurentSeries Qb) = (u : LaurentSeries Qb) →
    ((θ f : FH M H) : LaurentSeries Qb) = qExpand Qb p (u : LaurentSeries Qb)

variable (p M H hpM) in

def βincl (θ : FH M H ≃ₐ[Qb] FH M H) : FH' p M H hpM →ₐ[Qb] FH M H :=
  (θ : FH M H →ₐ[Qb] FH M H).comp (incl p M H hpM)

theorem βincl_apply (θ : FH M H ≃ₐ[Qb] FH M H) (u : FH' p M H hpM) :
    βincl p M H hpM θ u = θ (incl p M H hpM u) := rfl

theorem coe_βincl {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ) (u : FH' p M H hpM) :
    ((βincl p M H hpM θ u : FH M H) : LaurentSeries Qb) = qExpand Qb p (u : LaurentSeries Qb) :=
  hθ _ u (coe_incl p M H hpM u)

theorem coe_θ_incl {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ) (u : FH' p M H hpM) :
    ((θ (incl p M H hpM u) : FH M H) : LaurentSeries Qb) = qExpand Qb p (u : LaurentSeries Qb) :=
  coe_βincl hθ u

end Frame

section DegreeBottom

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

variable (p M H hpM) in

@[reducible] def algIncl : Algebra (FH' p M H hpM) (FH M H) := algebraAlong (incl p M H hpM)

attribute [local instance] algIncl

theorem algebraMap_incl_apply (u : FH' p M H hpM) :
    algebraMap (FH' p M H hpM) (FH M H) u = incl p M H hpM u := rfl

theorem finrank_bottom (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ) :
    Module.finrank (FH' p M H hpM) (FH M H) = p + 1 := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  have h := (ModularCurve.finrankAlong_eq_add_one_and_finrankAlong_eq_add_one_of_coe_eq_qExpand p M H hpM
    hpM2 hHp θ hθ (incl p M H hpM) (βincl p M H hpM θ) (coe_incl p M H hpM) (coe_βincl hθ)).1
  exact h

theorem finiteDimensional_bottom (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ) :
    FiniteDimensional (FH' p M H hpM) (FH M H) :=
  Module.finite_of_finrank_pos (by rw [finrank_bottom hpM2 hHp hθ]; exact Nat.succ_pos p)

end DegreeBottom

section Bottom

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

attribute [local instance] algIncl

variable (M H) in

def x1 : FH M H :=
  ⟨coeffEmb Qb xq, coeffEmb_mem_laurentBaseChange Qb (xq_mem (CohCarrier.GammaH M H))⟩

theorem coe_x1_coeff_one : ((x1 M H : FH M H) : LaurentSeries Qb).coeff 1 = -1728 := by
  show (coeffEmb Qb xq).coeff 1 = -1728
  rw [coeffEmb_coeff, xq_coeff_one, map_neg]
  norm_num

def γel (θ : FH M H ≃ₐ[Qb] FH M H) : FH M H := θ.symm (x1 M H)

theorem θ_γel (θ : FH M H ≃ₐ[Qb] FH M H) : θ (γel θ) = x1 M H := AlgEquiv.apply_symm_apply θ _

def valHom (S : IntermediateField Qb (LaurentSeries Qb)) : S →+* LaurentSeries Qb where
  toFun v := (v : LaurentSeries Qb)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem valHom_apply (S : IntermediateField Qb (LaurentSeries Qb)) (v : S) :
    valHom S v = (v : LaurentSeries Qb) := rfl

variable (p M H hpM) in

def e0 : FH' p M H hpM →+* LaurentSeries Qb := (qExpand Qb p).comp (valHom (FH' p M H hpM))

theorem e0_apply (u : FH' p M H hpM) : e0 p M H hpM u = qExpand Qb p (u : LaurentSeries Qb) := rfl

variable (p) in

def ψinf : FH M H →+* LaurentSeries Qb := (qExpand Qb p).comp (valHom (FH M H))

theorem ψinf_apply (v : FH M H) : ψinf p v = qExpand Qb p (v : LaurentSeries Qb) := rfl

def ψtw (θ : FH M H ≃ₐ[Qb] FH M H) (c : Qbˣ) : FH M H →+* LaurentSeries Qb :=
  (qTwist c).comp ((valHom (FH M H)).comp (θ : FH M H →+* FH M H))

theorem ψtw_apply (θ : FH M H ≃ₐ[Qb] FH M H) (c : Qbˣ) (v : FH M H) :
    ψtw θ c v = qTwist c ((θ v : FH M H) : LaurentSeries Qb) := rfl

theorem qTwist_qExpand_of_pow {c : Qbˣ} (hc : c ^ p = 1) (x : LaurentSeries Qb) :
    qTwist c (qExpand Qb p x) = qExpand Qb p x := by
  rw [qTwist_qExpand, zpow_natCast, hc, qTwist_one_apply]

theorem zeta_pow_pow {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ p) (j : ℕ) : (ζ ^ j) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem ψinf_comp_incl : (ψinf p).comp (incl p M H hpM : FH' p M H hpM →+* FH M H) = e0 p M H hpM := by
  refine RingHom.ext fun u => ?_
  rw [RingHom.comp_apply, e0_apply, AlgHom.coe_toRingHom, ψinf_apply, coe_incl]

theorem ψtw_comp_incl {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ) {c : Qbˣ}
    (hc : c ^ p = 1) : (ψtw θ c).comp (incl p M H hpM : FH' p M H hpM →+* FH M H) = e0 p M H hpM := by
  refine RingHom.ext fun u => ?_
  rw [RingHom.comp_apply, e0_apply, AlgHom.coe_toRingHom, ψtw_apply, coe_θ_incl hθ,
    qTwist_qExpand_of_pow hc]

variable (hpM) in

def μ (θ : FH M H ≃ₐ[Qb] FH M H) : Polynomial (FH' p M H hpM) := minpoly (FH' p M H hpM) (γel θ)

theorem algebraMap_FH'_eq : algebraMap (FH' p M H hpM) (FH M H) = (incl p M H hpM : FH' p M H hpM →+* FH M H) := rfl

theorem isRoot_map_μ (θ : FH M H ≃ₐ[Qb] FH M H) {ψ : FH M H →+* LaurentSeries Qb}
    (hψ : ψ.comp (incl p M H hpM : FH' p M H hpM →+* FH M H) = e0 p M H hpM) :
    ((μ hpM θ).map (e0 p M H hpM)).IsRoot (ψ (γel θ)) := by
  have h0 : Polynomial.aeval (γel θ) (μ hpM θ) = 0 := minpoly.aeval _ _
  rw [Polynomial.aeval_def, algebraMap_FH'_eq] at h0
  have h1 := congrArg ψ h0
  rw [map_zero, Polynomial.hom_eval₂, hψ] at h1
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact h1

section WithPin

variable (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ)
  {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ p)

variable (p) in

def sv (θ : FH M H ≃ₐ[Qb] FH M H) (ζ : Qbˣ) : Option (Fin p) → LaurentSeries Qb
  | none => qExpand Qb p ((γel θ : FH M H) : LaurentSeries Qb)
  | some b => qTwist (ζ ^ (b : ℕ)) ((x1 M H : FH M H) : LaurentSeries Qb)

theorem sv_none : sv p θ ζ none = qExpand Qb p ((γel θ : FH M H) : LaurentSeries Qb) := rfl

theorem sv_some (b : Fin p) :
    sv p θ ζ (some b) = qTwist (ζ ^ (b : ℕ)) ((x1 M H : FH M H) : LaurentSeries Qb) := rfl

theorem sv_none_coeff_one : (sv p θ ζ none).coeff 1 = 0 := by
  have hprime : p.Prime := Fact.out
  rw [sv_none]
  refine qExpand_coeff_of_not_dvd p _ fun h => ?_
  have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
  exact hprime.one_lt.ne' (by exact_mod_cast h2)

theorem qExpand_coeff_one (x : LaurentSeries Qb) : (qExpand Qb p x).coeff 1 = 0 := by
  have hprime : p.Prime := Fact.out
  refine qExpand_coeff_of_not_dvd p _ fun h => ?_
  have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
  exact hprime.one_lt.ne' (by exact_mod_cast h2)

theorem sv_some_coeff_one (b : Fin p) :
    (sv p θ ζ (some b)).coeff 1 = ((ζ : Qb) ^ (b : ℕ)) * (-1728) := by
  rw [sv_some, qTwist_coeff, coe_x1_coeff_one, zpow_one, Units.val_pow_eq_pow_val]

include hζ in
theorem sv_injective : Function.Injective (sv p θ ζ) := by
  have hζ' : IsPrimitiveRoot (ζ : Qb) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hz : ∀ j : ℕ, (ζ : Qb) ^ j * (-1728) ≠ 0 := fun j =>
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero ζ)) (by norm_num)
  intro o₁ o₂ h
  have hc := congrArg (fun s : LaurentSeries Qb => s.coeff 1) h
  rcases o₁ with _ | j₁ <;> rcases o₂ with _ | j₂
  · rfl
  · rw [sv_none_coeff_one, sv_some_coeff_one] at hc; exact absurd hc.symm (hz _)
  · rw [sv_none_coeff_one, sv_some_coeff_one] at hc; exact absurd hc (hz _)
  · rw [sv_some_coeff_one, sv_some_coeff_one] at hc
    have hv : (ζ : Qb) ^ (j₁ : ℕ) = (ζ : Qb) ^ (j₂ : ℕ) :=
      mul_right_cancel₀ (by norm_num : (-1728 : Qb) ≠ 0) hc
    exact congrArg some (Fin.ext (hζ'.pow_inj j₁.2 j₂.2 hv))

include hθ hζ in

theorem isRoot_sv (o : Option (Fin p)) : ((μ hpM θ).map (e0 p M H hpM)).IsRoot (sv p θ ζ o) := by
  rcases o with _ | b
  · exact isRoot_map_μ θ ψinf_comp_incl
  · have h := isRoot_map_μ (hpM := hpM) θ (ψtw_comp_incl hθ (zeta_pow_pow hζ b))
    rw [ψtw_apply, θ_γel] at h
    exact h

variable (p) in

def PiPoly (θ : FH M H ≃ₐ[Qb] FH M H) (ζ : Qbˣ) : Polynomial (LaurentSeries Qb) :=
  ∏ o : Option (Fin p), (X - Polynomial.C (sv p θ ζ o))

theorem PiPoly_monic : (PiPoly p θ ζ).Monic :=
  monic_prod_of_monic _ _ fun o _ => monic_X_sub_C _

theorem PiPoly_natDegree : (PiPoly p θ ζ).natDegree = p + 1 := by
  rw [PiPoly, natDegree_prod_of_monic _ _ fun o _ => monic_X_sub_C _]
  simp

include hpM2 hHp hθ in
theorem isIntegral_γel : IsIntegral (FH' p M H hpM) (γel θ) := by
  haveI := finiteDimensional_bottom hpM2 hHp hθ
  exact IsIntegral.of_finite _ _

include hpM2 hHp hθ hζ in

theorem map_μ_eq : (μ hpM θ).map (e0 p M H hpM) = PiPoly p θ ζ ∧
    (μ hpM θ).natDegree = p + 1 := by
  haveI := finiteDimensional_bottom hpM2 hHp hθ
  have hmonic : (μ hpM θ).Monic := minpoly.monic (isIntegral_γel hpM2 hHp hθ)
  have hmonic' : ((μ hpM θ).map (e0 p M H hpM)).Monic := hmonic.map _
  have hdeg : ((μ hpM θ).map (e0 p M H hpM)).natDegree ≤ p + 1 := by
    rw [hmonic.natDegree_map]
    exact (minpoly.natDegree_le (γel θ)).trans (finrank_bottom hpM2 hHp hθ).le
  have hdvd : PiPoly p θ ζ ∣ (μ hpM θ).map (e0 p M H hpM) := by
    refine Finset.prod_dvd_of_coprime ?_ fun o _ => ?_
    · exact (pairwise_coprime_X_sub_C (sv_injective (θ := θ) hζ)).set_pairwise _
    · exact dvd_iff_isRoot.mpr (isRoot_sv hθ hζ o)
  have heq := eq_of_monic_of_dvd_of_natDegree_le (PiPoly_monic (θ := θ) (ζ := ζ)) hmonic' hdvd
    (hdeg.trans (PiPoly_natDegree (θ := θ) (ζ := ζ)).ge)
  refine ⟨heq, ?_⟩
  rw [← hmonic.natDegree_map (e0 p M H hpM), heq, PiPoly_natDegree]

include hpM2 hHp hθ hζ in

theorem adjoin_γel_eq_top : IntermediateField.adjoin (FH' p M H hpM) {γel θ} = ⊤ := by
  haveI := finiteDimensional_bottom hpM2 hHp hθ
  rw [Field.primitive_element_iff_minpoly_natDegree_eq, finrank_bottom hpM2 hHp hθ]
  exact (map_μ_eq hpM2 hHp hθ hζ).2

theorem ringHom_ext_of_incl_γel {R : Type*} [DivisionRing R]
    (htop : IntermediateField.adjoin (FH' p M H hpM) {γel θ} = ⊤)
    (φ ψ : FH M H →+* R) (hincl : ∀ u : FH' p M H hpM, φ (incl p M H hpM u) = ψ (incl p M H hpM u))
    (hγ : φ (γel θ) = ψ (γel θ)) : φ = ψ := by
  refine RingHom.ext fun x => ?_
  have hx : x ∈ IntermediateField.adjoin (FH' p M H hpM) {γel θ} := by rw [htop]; trivial
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hγ
  | algebraMap u => exact hincl u
  | add y z _ _ ihy ihz => rw [map_add, map_add, ihy, ihz]
  | inv y _ ihy => rw [map_inv₀, map_inv₀, ihy]
  | mul y z _ _ ihy ihz => rw [map_mul, map_mul, ihy, ihz]

end WithPin

end Bottom

section Top

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

attribute [local instance] algIncl

variable (M H p) in

@[reducible] def algAlpha : Algebra (FH M H) (Etop p M H) := algebraAlong (heckeAlphaHBar Qb M H p)

attribute [local instance] algAlpha

theorem algebraMap_alpha_apply (f : FH M H) :
    algebraMap (FH M H) (Etop p M H) f = heckeAlphaHBar Qb M H p f := rfl

theorem algebraMap_FH_Etop_eq :
    algebraMap (FH M H) (Etop p M H) = (heckeAlphaHBar Qb M H p : FH M H →+* Etop p M H) := rfl

theorem finrank_top_pos_and_le (hpM : p ∣ M) : 0 < Module.finrank (FH M H) (Etop p M H) ∧
    Module.finrank (FH M H) (Etop p M H) ≤ p := by
  have h := ModularCurve.finrankAlong_heckeAlphaHBar_pos_and_le_relIndex Qb M H p
  exact ⟨h.1, h.2.trans (relIndex_le p M H hpM)⟩

scoped instance finiteDimensional_top : FiniteDimensional (FH M H) (Etop p M H) := by
  have hpM' : p ∣ M * p := dvd_mul_left p M
  exact Module.finite_of_finrank_pos
    (ModularCurve.finrankAlong_heckeAlphaHBar_pos_and_le_relIndex Qb M H p).1

variable (p) in

def κ (θ : FH M H ≃ₐ[Qb] FH M H) : FH M H →+* LaurentSeries Qb :=
  (qExpand Qb p).comp ((valHom (FH M H)).comp (θ.symm : FH M H →+* FH M H))

theorem κ_apply (θ : FH M H ≃ₐ[Qb] FH M H) (f : FH M H) :
    κ p θ f = qExpand Qb p ((θ.symm f : FH M H) : LaurentSeries Qb) := rfl

theorem κ_comp_βincl (θ : FH M H ≃ₐ[Qb] FH M H) :
    (κ p θ).comp (βincl p M H hpM θ : FH' p M H hpM →+* FH M H) = e0 p M H hpM := by
  refine RingHom.ext fun u => ?_
  rw [RingHom.comp_apply, e0_apply, AlgHom.coe_toRingHom, κ_apply, βincl_apply,
    AlgEquiv.symm_apply_apply, coe_incl]

theorem qTwist_comp_κ (θ : FH M H ≃ₐ[Qb] FH M H) {c : Qbˣ} (hc : c ^ p = 1) :
    (qTwist c).comp (κ p θ) = κ p θ := by
  refine RingHom.ext fun f => ?_
  rw [RingHom.comp_apply, κ_apply, qTwist_qExpand_of_pow hc]

variable (p) in

def bg (θ : FH M H ≃ₐ[Qb] FH M H) : Etop p M H := heckeBetaHBar Qb M H p (γel θ)

variable (p) in

def μ1 (θ : FH M H ≃ₐ[Qb] FH M H) : Polynomial (FH M H) := minpoly (FH M H) (bg p θ)

variable (p) in

def ρ (θ : FH M H ≃ₐ[Qb] FH M H) : Polynomial (LaurentSeries Qb) := (μ1 p θ).map (κ p θ)

theorem isIntegral_bg (θ : FH M H ≃ₐ[Qb] FH M H) : IsIntegral (FH M H) (bg p θ) :=
  IsIntegral.of_finite _ _

theorem μ1_monic (θ : FH M H ≃ₐ[Qb] FH M H) : (μ1 p θ).Monic := minpoly.monic (isIntegral_bg (p := p) θ)

theorem ρ_monic (θ : FH M H ≃ₐ[Qb] FH M H) : (ρ p θ).Monic := (μ1_monic (p := p) θ).map _

theorem ρ_natDegree (θ : FH M H ≃ₐ[Qb] FH M H) : (ρ p θ).natDegree = (μ1 p θ).natDegree :=
  (μ1_monic (p := p) θ).natDegree_map _

theorem μ1_natDegree_le (θ : FH M H ≃ₐ[Qb] FH M H) :
    (μ1 p θ).natDegree ≤ Module.finrank (FH M H) (Etop p M H) :=
  minpoly.natDegree_le _

theorem μ1_natDegree_pos (θ : FH M H ≃ₐ[Qb] FH M H) : 0 < (μ1 p θ).natDegree :=
  minpoly.natDegree_pos (isIntegral_bg (p := p) θ)

theorem ρ_map_qTwist (θ : FH M H ≃ₐ[Qb] FH M H) {c : Qbˣ} (hc : c ^ p = 1) :
    (ρ p θ).map (qTwist c) = ρ p θ := by
  rw [ρ, Polynomial.map_map, qTwist_comp_κ (p := p) θ hc]

theorem isRoot_ρ_qTwist (θ : FH M H ≃ₐ[Qb] FH M H) {c : Qbˣ} (hc : c ^ p = 1) {r : LaurentSeries Qb}
    (hr : (ρ p θ).IsRoot r) : (ρ p θ).IsRoot (qTwist c r) := by
  rw [IsRoot, ← ρ_map_qTwist (p := p) θ hc, eval_map, eval₂_hom, hr.eq_zero, map_zero]

section WithPin

variable (hin : HeckeDiamondInputsHAll M H) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ)
  {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ p)

private theorem _root_.WNormSwapSol.betaHDefined (hin : HeckeDiamondInputsHAll M H) : HeckeBetaHDefined M H p :=
  (hin.heckeInputsHAlong p Fact.out).betaHDefined

p2m_export "WNormSwapSol" "betaHDefined"
include hin in
theorem coe_bg : ((bg p θ : Etop p M H) : LaurentSeries Qb) =
    qExpand Qb p ((γel θ : FH M H) : LaurentSeries Qb) :=
  coe_heckeBetaHBar M H p (betaHDefined hin) _

include hin hθ in

theorem alpha_comp_βincl :
    (heckeAlphaHBar Qb M H p : FH M H →+* Etop p M H).comp (βincl p M H hpM θ : FH' p M H hpM →+* FH M H) =
      (heckeBetaHBar Qb M H p : FH M H →+* Etop p M H).comp (incl p M H hpM : FH' p M H hpM →+* FH M H) := by
  refine RingHom.ext fun u => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.coe_toRingHom,
    AlgHom.coe_toRingHom, AlgHom.coe_toRingHom,
    coe_heckeAlphaHBar, coe_βincl hθ, coe_heckeBetaHBar M H p (betaHDefined hin), coe_incl]

include hin hθ in

theorem μ1_dvd : μ1 p θ ∣ (μ hpM θ).map (βincl p M H hpM θ : FH' p M H hpM →+* FH M H) := by
  refine minpoly.dvd _ _ ?_
  have h0 : Polynomial.aeval (γel θ) (μ hpM θ) = 0 := minpoly.aeval _ _
  have h1 : (heckeBetaHBar Qb M H p : FH M H →+* Etop p M H) (Polynomial.aeval (γel θ) (μ hpM θ)) = 0 := by
    rw [h0, map_zero]
  rw [aeval_def, algebraMap_FH'_eq, hom_eval₂, ← alpha_comp_βincl hin hθ, ← eval₂_map,
    ← algebraMap_FH_Etop_eq] at h1
  rw [aeval_def]
  exact h1

include hin hpM2 hHp hθ hζ in

theorem ρ_dvd_PiPoly : ρ p θ ∣ PiPoly p θ ζ := by
  rw [← (map_μ_eq hpM2 hHp hθ hζ).1, ← κ_comp_βincl (hpM := hpM) (p := p) θ, ← Polynomial.map_map]
  exact Polynomial.map_dvd _ (μ1_dvd hin hθ)

include hin hpM2 hHp hθ hζ in

theorem exists_isRoot_some : ∃ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)) := by
  by_contra hno
  push Not at hno
  have hPi0 : PiPoly p θ ζ ≠ 0 := (PiPoly_monic (θ := θ) (ζ := ζ)).ne_zero
  have hρ0 : ρ p θ ≠ 0 := (ρ_monic (p := p) θ).ne_zero
  have hPi0' : (Finset.univ.prod fun o : Option (Fin p) => (X - Polynomial.C (sv p θ ζ o))) ≠ 0 := hPi0

  have hroots : ∀ r ∈ (ρ p θ).roots, r = sv p θ ζ none := by
    intro r hr
    have hr' : r ∈ (PiPoly p θ ζ).roots :=
      Multiset.mem_of_le (roots.le_of_dvd hPi0 (ρ_dvd_PiPoly hin hpM2 hHp hθ hζ)) hr
    rw [PiPoly, roots_prod _ _ hPi0'] at hr'
    obtain ⟨o, -, ho⟩ := Multiset.mem_bind.mp hr'
    rw [roots_X_sub_C, Multiset.mem_singleton] at ho
    rcases o with _ | b
    · exact ho
    · exact absurd ((mem_roots hρ0).mp hr) (ho ▸ hno b)

  have hnodup : (ρ p θ).roots.Nodup := by
    refine Multiset.nodup_of_le (roots.le_of_dvd hPi0 (ρ_dvd_PiPoly hin hpM2 hHp hθ hζ)) ?_
    rw [PiPoly, roots_prod _ _ hPi0']
    have : (Finset.univ.val.bind fun o : Option (Fin p) => (X - Polynomial.C (sv p θ ζ o)).roots) =
        Finset.univ.val.map (sv p θ ζ) := by
      simp only [roots_X_sub_C]
      rw [Multiset.bind_singleton]
    rw [this]
    exact Finset.univ.nodup.map (sv_injective hζ)
  have hcard_le : (ρ p θ).roots.card ≤ 1 := by
    classical
    rw [← Multiset.toFinset_card_of_nodup hnodup]
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [Multiset.mem_toFinset] at ha hb
    rw [hroots a ha, hroots b hb]

  obtain ⟨R, hR⟩ := ρ_dvd_PiPoly hin hpM2 hHp hθ hζ
  have hR0 : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hPi0 hR
  have hcardPi : (PiPoly p θ ζ).roots.card = p + 1 := by
    have h1 : (PiPoly p θ ζ).roots.card ≤ p + 1 :=
      (card_roots' _).trans (PiPoly_natDegree (θ := θ) (ζ := ζ)).le
    have h2 : p + 1 ≤ (PiPoly p θ ζ).roots.card := by
      have hsub : Finset.univ.val.map (sv p θ ζ) ≤ (PiPoly p θ ζ).roots := by
        rw [← Multiset.prod_X_sub_C_dvd_iff_le_roots hPi0, Multiset.map_map]
        exact dvd_of_eq (by rw [PiPoly, Finset.prod_eq_multiset_prod]; rfl)
      have := Multiset.card_le_card hsub
      simpa using this
    omega
  have hsum : (ρ p θ).roots.card + R.roots.card = p + 1 := by
    rw [← hcardPi, hR, roots_mul (hR ▸ hPi0), Multiset.card_add]
  have hdegsum : (ρ p θ).natDegree + R.natDegree = p + 1 := by
    rw [← PiPoly_natDegree (θ := θ) (ζ := ζ), hR, natDegree_mul hρ0 hR0]
  have hcρ := card_roots' (ρ p θ)
  have hcR := card_roots' R
  have hdeg1 : (μ1 p θ).natDegree = 1 := by
    have := μ1_natDegree_pos (p := p) θ
    rw [← ρ_natDegree (p := p) θ] at this ⊢
    omega

  have hμ1 : μ1 p θ = X + Polynomial.C ((μ1 p θ).coeff 0) := (μ1_monic (p := p) θ).eq_X_add_C hdeg1
  set a₀ := (μ1 p θ).coeff 0 with ha₀
  have hbg : bg p θ = heckeAlphaHBar Qb M H p (-a₀) := by
    have h0 : Polynomial.aeval (bg p θ) (μ1 p θ) = 0 := minpoly.aeval _ _
    rw [hμ1, map_add, aeval_X, aeval_C, algebraMap_alpha_apply, add_eq_zero_iff_eq_neg] at h0
    rw [h0, map_neg]
  have hρeq : ρ p θ = X - Polynomial.C (κ p θ (-a₀)) := by
    rw [ρ, hμ1, Polynomial.map_add, map_X, map_C, map_neg, map_neg, sub_neg_eq_add]
  have hroot : (ρ p θ).IsRoot (κ p θ (-a₀)) := by rw [hρeq]; simp
  have hκ : κ p θ (-a₀) = sv p θ ζ none := hroots _ ((mem_roots hρ0).mpr hroot)

  rw [κ_apply, sv_none] at hκ
  have h1 : θ.symm (-a₀) = γel θ := Subtype.ext (qExpand_injective p hκ)
  have h2 : -a₀ = x1 M H := by
    have := congrArg θ h1
    rwa [AlgEquiv.apply_symm_apply, θ_γel] at this

  have h3 := congrArg (fun z : Etop p M H => (z : LaurentSeries Qb).coeff 1) hbg
  rw [coe_bg hin, h2, coe_heckeAlphaHBar, coe_x1_coeff_one, qExpand_coeff_one] at h3
  norm_num at h3

include hin hpM2 hHp hθ hζ in

theorem isRoot_some (b : Fin p) : (ρ p θ).IsRoot (sv p θ ζ (some b)) := by
  obtain ⟨b₀, hb₀⟩ := exists_isRoot_some hin hpM2 hHp hθ hζ
  have hp0 : (b₀ : ℕ) ≤ p := b₀.2.le
  have h := isRoot_ρ_qTwist (p := p) θ (zeta_pow_pow hζ ((b : ℕ) + (p - b₀))) hb₀
  rw [sv_some, qTwist_qTwist, ← pow_add] at h
  have hexp : ζ ^ ((b : ℕ) + (p - b₀) + b₀) = ζ ^ (b : ℕ) := by
    rw [show (b : ℕ) + (p - b₀) + b₀ = b + p by omega, pow_add, hζ.pow_eq_one, mul_one]
  rw [hexp] at h
  exact h

variable (p) in

def PiSome (θ : FH M H ≃ₐ[Qb] FH M H) (ζ : Qbˣ) : Polynomial (LaurentSeries Qb) :=
  ∏ b : Fin p, (X - Polynomial.C (sv p θ ζ (some b)))

theorem PiSome_monic : (PiSome p θ ζ).Monic :=
  monic_prod_of_monic _ _ fun b _ => monic_X_sub_C _

theorem PiSome_natDegree : (PiSome p θ ζ).natDegree = p := by
  rw [PiSome, natDegree_prod_of_monic _ _ fun b _ => monic_X_sub_C _]
  simp

include hin hpM2 hHp hθ hζ in

theorem finrank_top_and_ρ_eq :
    Module.finrank (FH M H) (Etop p M H) = p ∧ (μ1 p θ).natDegree = p ∧
      ρ p θ = PiSome p θ ζ := by
  have hdvd : PiSome p θ ζ ∣ ρ p θ := by
    refine Finset.prod_dvd_of_coprime ?_ fun b _ => ?_
    · have hinj : Function.Injective (fun b : Fin p => sv p θ ζ (some b)) :=
        fun b₁ b₂ h => Option.some_injective _ (sv_injective hζ h)
      exact (pairwise_coprime_X_sub_C hinj).set_pairwise _
    · exact dvd_iff_isRoot.mpr (isRoot_some hin hpM2 hHp hθ hζ b)
  have hle1 : p ≤ (ρ p θ).natDegree := by
    have h := natDegree_le_of_dvd hdvd (ρ_monic (p := p) θ).ne_zero
    rw [PiSome_natDegree] at h
    exact h
  rw [ρ_natDegree] at hle1
  have hle2 := μ1_natDegree_le (p := p) θ
  have hle3 := (finrank_top_pos_and_le (p := p) (M := M) (H := H) hpM).2
  refine ⟨by omega, by omega, ?_⟩
  exact (eq_of_monic_of_dvd_of_natDegree_le (PiSome_monic (θ := θ) (ζ := ζ)) (ρ_monic (p := p) θ) hdvd
    (by rw [ρ_natDegree, PiSome_natDegree]; omega))

include hin hpM2 hHp hθ hζ in

theorem adjoin_bg_eq_top : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤ := by
  rw [Field.primitive_element_iff_minpoly_natDegree_eq]
  have h := finrank_top_and_ρ_eq hin hpM2 hHp hθ hζ
  rw [h.1]; exact h.2.1

end WithPin

end Top

section Norm

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

attribute [local instance] algIncl algAlpha

def Om (_p : ℕ) (_θ : FH M H ≃ₐ[Qb] FH M H) : Type := AlgebraicClosure (LaurentSeries Qb)

variable (θ : FH M H ≃ₐ[Qb] FH M H)

scoped instance : Field (Om p θ) := inferInstanceAs (Field (AlgebraicClosure (LaurentSeries Qb)))

scoped instance : IsAlgClosed (Om p θ) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries Qb)))

variable (p) in

def ιE : LaurentSeries Qb →+* Om p θ :=
  algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))

theorem ιE_injective : Function.Injective (ιE p θ) :=
  (algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))).injective

scoped instance algKOm : Algebra (FH M H) (Om p θ) := ((ιE p θ).comp (κ p θ)).toAlgebra

theorem algebraMap_KOm_apply (f : FH M H) :
    algebraMap (FH M H) (Om p θ) f = ιE p θ (κ p θ f) := rfl

theorem algebraMap_KOm_eq : algebraMap (FH M H) (Om p θ) = (ιE p θ).comp (κ p θ) := rfl

variable {θ}

section WithPin

variable (hin : HeckeDiamondInputsHAll M H) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (hθ : Pin (p := p) (hpM := hpM) θ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ p)

def pbTop (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) : PowerBasis (FH M H) (Etop p M H) :=
  (IntermediateField.adjoin.powerBasis (isIntegral_bg (p := p) θ)).map
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

theorem pbTop_gen (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) :
    (pbTop htop).gen = bg p θ := by
  rw [pbTop, PowerBasis.map_gen, IntermediateField.adjoin.powerBasis_gen]
  rfl

theorem minpoly_pbTop_gen (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) :
    minpoly (FH M H) (pbTop htop).gen = μ1 p θ := by
  rw [pbTop_gen]; rfl

theorem aeval_ιE_eq_zero (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤)
    {s : LaurentSeries Qb} (hs : (ρ p θ).IsRoot s) :
    Polynomial.aeval (ιE p θ s) (minpoly (FH M H) (pbTop htop).gen) = 0 := by
  rw [minpoly_pbTop_gen, aeval_def, algebraMap_KOm_eq, ← eval₂_map, eval₂_hom]
  show ιE p θ ((ρ p θ).eval s) = 0
  rw [hs.eq_zero, map_zero]

def σt (hρ : ∀ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)))
    (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) (b : Fin p) :
    Etop p M H →ₐ[FH M H] Om p θ :=
  (pbTop htop).lift (ιE p θ (sv p θ ζ (some b))) (aeval_ιE_eq_zero htop (hρ b))

theorem σt_bg (hρ : ∀ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)))
    (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) (b : Fin p) :
    σt hρ htop b (bg p θ) = ιE p θ (sv p θ ζ (some b)) := by
  have h := PowerBasis.lift_gen (pbTop htop) (ιE p θ (sv p θ ζ (some b))) (aeval_ιE_eq_zero htop (hρ b))
  rw [pbTop_gen] at h
  exact h

include hζ in
theorem σt_injective (hρ : ∀ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)))
    (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) :
    Function.Injective (σt hρ htop) := by
  intro b₁ b₂ h
  have h' := congrArg (fun σ : Etop p M H →ₐ[FH M H] Om p θ => σ (bg p θ)) h
  simp only [σt_bg] at h'
  exact Option.some_injective _ (sv_injective hζ (ιE_injective (p := p) θ h'))

include hin hpM2 hHp hθ hζ in

theorem norm_eq_prod (hρ : ∀ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)))
    (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤) (x : Etop p M H) :
    ιE p θ (κ p θ (Algebra.norm (FH M H) x)) = ∏ b : Fin p, σt hρ htop b x := by
  have hbij : Function.Bijective (σt hρ htop) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨σt_injective hζ hρ htop, ?_⟩
    rw [Fintype.card_fin, AlgHom.card, (finrank_top_and_ρ_eq hin hpM2 hHp hθ hζ).1]
  rw [← algebraMap_KOm_apply, Algebra.norm_eq_prod_embeddings (FH M H) (Om p θ) x,
    ← hbij.prod_comp fun σ => σ x]

include hin hθ hζ in

theorem σt_beta (hρ : ∀ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)))
    (htop : IntermediateField.adjoin (FH M H) {bg p θ} = ⊤)
    (htop' : IntermediateField.adjoin (FH' p M H hpM) {γel θ} = ⊤) (b : Fin p) (g : FH M H) :
    σt hρ htop b (heckeBetaHBar Qb M H p g) =
      ιE p θ (qTwist (ζ ^ (b : ℕ)) ((θ g : FH M H) : LaurentSeries Qb)) := by
  have key := ringHom_ext_of_incl_γel htop'
    ((σt hρ htop b : Etop p M H →+* Om p θ).comp (heckeBetaHBar Qb M H p : FH M H →+* Etop p M H))
    ((ιE p θ).comp (ψtw θ (ζ ^ (b : ℕ)))) (fun u => ?_) ?_
  · exact RingHom.congr_fun key g
  ·
    show σt hρ htop b (heckeBetaHBar Qb M H p (incl p M H hpM u)) =
      ιE p θ (qTwist (ζ ^ (b : ℕ)) ((θ (incl p M H hpM u) : FH M H) : LaurentSeries Qb))
    have h1 : heckeBetaHBar Qb M H p (incl p M H hpM u) =
        algebraMap (FH M H) (Etop p M H) (βincl p M H hpM θ u) := by
      rw [algebraMap_alpha_apply]
      exact (RingHom.congr_fun (alpha_comp_βincl hin hθ) u).symm
    rw [h1, AlgHom.commutes, algebraMap_KOm_apply, coe_θ_incl hθ,
      qTwist_qExpand_of_pow (zeta_pow_pow hζ b)]
    congr 1
    exact RingHom.congr_fun (κ_comp_βincl (hpM := hpM) θ) u
  ·
    show σt hρ htop b (heckeBetaHBar Qb M H p (γel θ)) =
      ιE p θ (qTwist (ζ ^ (b : ℕ)) ((θ (γel θ) : FH M H) : LaurentSeries Qb))
    rw [θ_γel]
    exact σt_bg hρ htop b

include hin hpM2 hHp hθ hζ in

theorem qExpand_symm_norm_beta (g : FH M H) :
    qExpand Qb p ((θ.symm (Algebra.norm (FH M H) (heckeBetaHBar Qb M H p g)) : FH M H) : LaurentSeries Qb) =
      ∏ b ∈ Finset.range p, qTwist (ζ ^ b) ((θ g : FH M H) : LaurentSeries Qb) := by
  have hρ : ∀ b : Fin p, (ρ p θ).IsRoot (sv p θ ζ (some b)) :=
    isRoot_some hin hpM2 hHp hθ hζ
  have htop := adjoin_bg_eq_top hin hpM2 hHp hθ hζ
  have htop' := adjoin_γel_eq_top hpM2 hHp hθ hζ
  apply ιE_injective (p := p) θ
  have h := norm_eq_prod hin hpM2 hHp hθ hζ hρ htop (heckeBetaHBar Qb M H p g)
  rw [κ_apply] at h
  rw [h, map_prod, Finset.prod_range]
  exact Finset.prod_congr rfl fun b _ => σt_beta hin hθ hζ hρ htop htop' b g

end WithPin

end Norm

section Square

variable {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

attribute [local instance] algIncl

variable (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  {θ : FH M H ≃ₐ[Qb] FH M H} (hθ : Pin (p := p) (hpM := hpM) θ)
  {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ p)
  (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) =
    (p : ZMod (M / p)))
  (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM ∨
    -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM)

include hpM2 hHp hθ hd hdH in

theorem θ_θ_incl (u : FH' p M H hpM) : θ (θ (incl p M H hpM u)) = incl p M H hpM u := by
  haveI : NeZero (M / p) := neZero_div p M hpM
  have hin' : HeckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM) :=
    ModularCurve.heckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM)
  have pin2 := ModularCurve.atkinLehner_qExpand_pin_of_pin p M H hpM hpM2 hHp hin' θ hθ
    (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) hd (θ (incl p M H hpM u)) u (coe_θ_incl hθ u)
  rw [ModularCurve.diamondAutHBar_eq_refl_of_mem_or_neg_mem (M / p) (infSubgroup p M H hpM) _ hdH]
    at pin2
  apply Subtype.ext
  rw [pin2, coe_incl]
  rfl

include hpM2 hHp hθ hζ hd hdH in

theorem θ_θ_γel : θ (θ (γel θ)) = γel θ := by

  have hψ : ((ψinf p).comp (θ.trans θ : FH M H →+* FH M H)).comp
      (incl p M H hpM : FH' p M H hpM →+* FH M H) = e0 p M H hpM := by
    refine RingHom.ext fun u => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, e0_apply, ψinf_apply, AlgHom.coe_toRingHom]
    change qExpand Qb p (((θ.trans θ) (incl p M H hpM u) : FH M H) : LaurentSeries Qb) = _
    rw [AlgEquiv.trans_apply, θ_θ_incl hpM2 hHp hθ d hd hdH, coe_incl]
  have hroot := isRoot_map_μ (hpM := hpM) θ hψ
  rw [(map_μ_eq hpM2 hHp hθ hζ).1, PiPoly, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hroot
  obtain ⟨o, -, ho⟩ := hroot
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at ho
  change qExpand Qb p ((θ (θ (γel θ)) : FH M H) : LaurentSeries Qb) = sv p θ ζ o at ho
  rcases o with _ | b
  · rw [sv_none] at ho
    exact Subtype.ext (qExpand_injective p ho)
  ·
    have h1 := congrArg (fun s : LaurentSeries Qb => s.coeff 1) ho
    rw [qExpand_coeff_one, sv_some_coeff_one] at h1
    exact absurd h1.symm (mul_ne_zero (pow_ne_zero _ (Units.ne_zero ζ)) (by norm_num))

include hpM2 hHp hθ hζ hd hdH in

theorem θ_symm_eq : θ.symm = θ := by
  have htop' := adjoin_γel_eq_top hpM2 hHp hθ hζ
  have key := ringHom_ext_of_incl_γel htop' ((θ.trans θ : FH M H ≃ₐ[Qb] FH M H) : FH M H →+* FH M H)
    (RingHom.id _) (fun u => θ_θ_incl hpM2 hHp hθ d hd hdH u) (θ_θ_γel hpM2 hHp hθ hζ d hd hdH)
  apply AlgEquiv.ext
  intro x
  have hx : θ (θ x) = x := RingHom.congr_fun key x
  apply θ.injective
  rw [AlgEquiv.apply_symm_apply, hx]

end Square

end WNormSwapSol
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol"

open WNormSwapSol ModularCurve AlgebraicCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ p)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ c₀ : AlgebraicClosure ℚ, c₀ ≠ 0 ∧
      qExpand (AlgebraicClosure ℚ) p
          (((letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
             wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H)
               (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) :
              ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        HahnSeries.C c₀ *
          ∏ j ∈ Finset.range p, ModularCurve.qTwist (ζ ^ j) ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
  subst hwθ
  refine ⟨1, one_ne_zero, ?_⟩
  letI : Algebra (FH M H) (Etop p M H) := algAlpha p M H
  have hθ' : Pin (p := p) (M := M) (H := H) (hpM := hpM) θ := hθ
  have hsymm : θ.symm = θ := θ_symm_eq hpM2 hHp hθ' hζ d hd hdH
  have key := qExpand_symm_norm_beta (p := p) (hpM := hpM) hin hpM2 hHp hθ' hζ (θ.symm f)
  rw [AlgEquiv.apply_symm_apply] at key
  have e1 : θ (Algebra.norm (FH M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (θ.symm f))) =
      θ.symm (Algebra.norm (FH M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (θ.symm f))) := by
    rw [hsymm]
  have hinv : (SemilinearAut.ofAlgAut θ)⁻¹ • f = θ.symm f := rfl
  rw [HahnSeries.C_one, one_mul, hinv, SemilinearAut.ofAlgAut_smul, e1]
  exact key

end S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist
end P2MW
export P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist (solution)
