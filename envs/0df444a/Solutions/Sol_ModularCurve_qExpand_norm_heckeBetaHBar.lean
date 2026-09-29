-- Prove2me | solution 1 for ModularCurve.qExpand_norm_heckeBetaHBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2680f20e-0cf5-56d7-9c89-6d28261c5fe9

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_norm_heckeBetaHBar
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries AlgebraicCurve

namespace KroneckerNormHSol

local notation "Qb" => AlgebraicClosure ℚ

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

section Bar

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

abbrev KK : Type _ := xHFunctionFieldBar M H

abbrev EEt : Type _ := laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ))

variable {M ℓ} in

def uℓ (hℓM : ¬ ℓ ∣ M) : (ZMod M)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)

variable {M ℓ} in

abbrev σℓ (hℓM : ¬ ℓ ∣ M) : KK M H ≃ₐ[Qb] KK M H := diamondAutHBar M H (uℓ hℓM)

variable {M H ℓ}

def ALSpec (hℓM : ¬ ℓ ∣ M) (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) : Prop :=
  (∀ x : KK M H, w (heckeAlphaHBar Qb M H ℓ x) = heckeBetaHBar Qb M H ℓ x) ∧
    (∀ x : KK M H, w (heckeBetaHBar Qb M H ℓ x) = heckeAlphaHBar Qb M H ℓ (σℓ H hℓM x))

theorem exists_AL (hℓM : ¬ ℓ ∣ M) (hin : HeckeDiamondInputsHAll M H) :
    ∃ w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ, ALSpec hℓM w := by
  obtain ⟨w, h1, h2⟩ := ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar M H hℓM hin
  exact ⟨w, h1, h2⟩

end Bar

section Norm

def Om (_ℓ : ℕ) : Type := AlgebraicClosure (LaurentSeries Qb)

variable (ℓ : ℕ) in
scoped instance : Field (Om ℓ) := inferInstanceAs (Field (AlgebraicClosure (LaurentSeries Qb)))

variable (ℓ : ℕ) in
scoped instance : IsAlgClosed (Om ℓ) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries Qb)))

def ιE (ℓ : ℕ) : LaurentSeries Qb →+* Om ℓ :=
  algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))

theorem ιE_injective (ℓ : ℕ) : Function.Injective (ιE ℓ) :=
  (algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))).injective

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

@[reducible] def algAlongAlpha : Algebra (KK M H) (EEt M H ℓ) :=
  algebraAlong (heckeAlphaHBar Qb M H ℓ)

@[reducible] def algAlphaOm : Algebra (KK M H) (Om ℓ) :=
  (((ιE ℓ).comp (algebraMap (EEt M H ℓ) (LaurentSeries Qb))).comp
    (heckeBetaHBar Qb M H ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongAlpha algAlphaOm

theorem finrank_alpha (hℓM : ¬ ℓ ∣ M) : Module.finrank (KK M H) (EEt M H ℓ) = ℓ + 1 :=
  ModularCurve.finrankAlong_heckeAlphaHBar Qb M H hℓM

theorem finiteDimensional_alpha (hℓM : ¬ ℓ ∣ M) : FiniteDimensional (KK M H) (EEt M H ℓ) :=
  Module.finite_of_finrank_pos (by rw [finrank_alpha M H ℓ hℓM]; exact Nat.succ_pos ℓ)

theorem algebraMap_KE_apply (f : KK M H) :
    algebraMap (KK M H) (EEt M H ℓ) f = heckeAlphaHBar Qb M H ℓ f := rfl

omit [NeZero M] [Fact ℓ.Prime] in
theorem algebraMap_ELS_apply (x : EEt M H ℓ) :
    algebraMap (EEt M H ℓ) (LaurentSeries Qb) x = ↑x := rfl

theorem algebraMap_KOm_apply (f : KK M H) :
    algebraMap (KK M H) (Om ℓ) f = ιE ℓ ((heckeBetaHBar Qb M H ℓ f : EEt M H ℓ) : LaurentSeries Qb) := rfl

theorem sigmaLast_comm (h0 : HeckeBetaHDefined M H ℓ) (f : KK M H) :
    ((ιE ℓ).comp ((qExpand Qb ℓ).comp (algebraMap (EEt M H ℓ) (LaurentSeries Qb))))
      (algebraMap (KK M H) (EEt M H ℓ) f) = algebraMap (KK M H) (Om ℓ) f := by
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_KE_apply, algebraMap_ELS_apply,
    algebraMap_KOm_apply, coe_heckeAlphaHBar, coe_heckeBetaHBar M H ℓ h0]

variable {M H ℓ}

def sigmaTwist (h0 : HeckeBetaHDefined M H ℓ) {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ)
    (hw : ALSpec hℓM w) (c : Qbˣ) (hc : c ^ ℓ = 1) : EEt M H ℓ →ₐ[KK M H] Om ℓ where
  toRingHom := (ιE ℓ).comp ((qTwist c).comp
    ((algebraMap (EEt M H ℓ) (LaurentSeries Qb)).comp w.toAlgHom.toRingHom))
  commutes' f := by
    show ιE ℓ (qTwist c ((w (heckeAlphaHBar Qb M H ℓ f) : EEt M H ℓ) : LaurentSeries Qb)) =
      ιE ℓ ((heckeBetaHBar Qb M H ℓ f : EEt M H ℓ) : LaurentSeries Qb)
    rw [hw.1, coe_heckeBetaHBar M H ℓ h0, qTwist_qExpand, zpow_natCast, hc, qTwist_one_apply]

theorem sigmaTwist_apply (h0 : HeckeBetaHDefined M H ℓ) {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ)
    (hw : ALSpec hℓM w) (c : Qbˣ) (hc : c ^ ℓ = 1) (v : EEt M H ℓ) :
    sigmaTwist h0 w hw c hc v = ιE ℓ (qTwist c ((w v : EEt M H ℓ) : LaurentSeries Qb)) := rfl

variable (M H ℓ) in

def sigmaLast (h0 : HeckeBetaHDefined M H ℓ) : EEt M H ℓ →ₐ[KK M H] Om ℓ where
  toRingHom := (ιE ℓ).comp ((qExpand Qb ℓ).comp (algebraMap (EEt M H ℓ) (LaurentSeries Qb)))
  commutes' := sigmaLast_comm M H ℓ h0

theorem sigmaLast_apply (h0 : HeckeBetaHDefined M H ℓ) (v : EEt M H ℓ) :
    sigmaLast M H ℓ h0 v = ιE ℓ (qExpand Qb ℓ (v : LaurentSeries Qb)) := by
  show ((ιE ℓ).comp ((qExpand Qb ℓ).comp (algebraMap (EEt M H ℓ) (LaurentSeries Qb)))) v = _
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_ELS_apply]

theorem zeta_pow_pow {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (ζ ^ j) ^ ℓ = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

def emb (h0 : HeckeBetaHDefined M H ℓ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ) {hℓM : ¬ ℓ ∣ M}
    (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) (hw : ALSpec hℓM w) :
    Option (Fin ℓ) → (EEt M H ℓ →ₐ[KK M H] Om ℓ)
  | none => sigmaLast M H ℓ h0
  | some j => sigmaTwist h0 w hw (ζ ^ (j : ℕ)) (zeta_pow_pow hζ j)

theorem emb_none_apply (h0 : HeckeBetaHDefined M H ℓ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) (hw : ALSpec hℓM w) (v : EEt M H ℓ) :
    emb h0 hζ w hw none v = ιE ℓ (qExpand Qb ℓ (v : LaurentSeries Qb)) :=
  sigmaLast_apply h0 v

theorem emb_some_apply (h0 : HeckeBetaHDefined M H ℓ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) (hw : ALSpec hℓM w) (j : Fin ℓ) (v : EEt M H ℓ) :
    emb h0 hζ w hw (some j) v = ιE ℓ (qTwist (ζ ^ (j : ℕ)) ((w v : EEt M H ℓ) : LaurentSeries Qb)) :=
  rfl

variable (M H) in

def x1 : KK M H :=
  ⟨coeffEmb Qb xq, coeffEmb_mem_laurentBaseChange Qb (xq_mem (CohCarrier.GammaH M H))⟩

omit [Fact ℓ.Prime] in
theorem coe_x1_coeff_one : ((x1 M H : KK M H) : LaurentSeries Qb).coeff 1 = -1728 := by
  show (coeffEmb Qb xq).coeff 1 = -1728
  rw [coeffEmb_coeff, xq_coeff_one, map_neg]
  norm_num

def x0 (hℓM : ¬ ℓ ∣ M) : KK M H := (σℓ H hℓM).symm (x1 M H)

theorem w_beta_x0 {hℓM : ¬ ℓ ∣ M} {w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ} (hw : ALSpec hℓM w) :
    ((w (heckeBetaHBar Qb M H ℓ (x0 hℓM)) : EEt M H ℓ) : LaurentSeries Qb) =
      ((x1 M H : KK M H) : LaurentSeries Qb) := by
  rw [hw.2, coe_heckeAlphaHBar, x0, AlgEquiv.apply_symm_apply]

theorem emb_injective (h0 : HeckeBetaHDefined M H ℓ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) (hw : ALSpec hℓM w) :
    Function.Injective (emb h0 hζ w hw) := by
  have hprime : ℓ.Prime := Fact.out
  have hζ' : IsPrimitiveRoot (ζ : Qb) ℓ := IsPrimitiveRoot.coe_units_iff.mpr hζ

  let cf : Option (Fin ℓ) → Qb := fun o => Option.elim o (0 : Qb) (fun j => ((ζ : Qb) ^ (j : ℕ)) * (-1728))
  have key : ∀ o : Option (Fin ℓ), ∃ s : LaurentSeries Qb,
      emb h0 hζ w hw o (heckeBetaHBar Qb M H ℓ (x0 hℓM)) = ιE ℓ s ∧ s.coeff 1 = cf o := by
    rintro (_ | j)
    · refine ⟨qExpand Qb ℓ (qExpand Qb ℓ ((x0 hℓM : KK M H) : LaurentSeries Qb)), ?_, ?_⟩
      · rw [emb_none_apply, coe_heckeBetaHBar M H ℓ h0]
      · show (qExpand Qb ℓ (qExpand Qb ℓ _)).coeff 1 = 0
        refine qExpand_coeff_of_not_dvd ℓ _ fun h => ?_
        have h2 : (ℓ : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
        exact hprime.one_lt.ne' (by exact_mod_cast h2)
    · refine ⟨qTwist (ζ ^ (j : ℕ)) ((x1 M H : KK M H) : LaurentSeries Qb), ?_, ?_⟩
      · rw [emb_some_apply, w_beta_x0 hw]
      · show (qTwist (ζ ^ (j : ℕ)) _).coeff 1 = (ζ : Qb) ^ (j : ℕ) * (-1728)
        rw [qTwist_coeff, coe_x1_coeff_one, zpow_one, Units.val_pow_eq_pow_val]
  intro o₁ o₂ h
  obtain ⟨s₁, hs₁, hc₁⟩ := key o₁
  obtain ⟨s₂, hs₂, hc₂⟩ := key o₂
  have hs : s₁ = s₂ := ιE_injective ℓ (by rw [← hs₁, ← hs₂, h])
  rw [hs] at hc₁
  have hc : cf o₁ = cf o₂ := hc₁.symm.trans hc₂
  have hz : ∀ j : ℕ, (ζ : Qb) ^ j * (-1728) ≠ 0 := fun j =>
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero ζ)) (by norm_num)
  rcases o₁ with _ | j₁ <;> rcases o₂ with _ | j₂
  · rfl
  · exact absurd hc.symm (hz _)
  · exact absurd hc (hz _)
  · have hv : (ζ : Qb) ^ (j₁ : ℕ) = (ζ : Qb) ^ (j₂ : ℕ) :=
      mul_right_cancel₀ (by norm_num : (-1728 : Qb) ≠ 0) hc
    exact congrArg some (Fin.ext (hζ'.pow_inj j₁.2 j₂.2 hv))

theorem emb_bijective (h0 : HeckeBetaHDefined M H ℓ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) (hw : ALSpec hℓM w) :
    Function.Bijective (emb h0 hζ w hw) := by
  haveI := finiteDimensional_alpha M H ℓ hℓM
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective h0 hζ w hw, ?_⟩
  rw [Fintype.card_option, Fintype.card_fin, AlgHom.card, finrank_alpha M H ℓ hℓM]

theorem qExpand_norm (h0 : HeckeBetaHDefined M H ℓ) {ζ : Qbˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    {hℓM : ¬ ℓ ∣ M} (w : EEt M H ℓ ≃ₐ[Qb] EEt M H ℓ) (hw : ALSpec hℓM w) (v : EEt M H ℓ) :
    qExpand Qb ℓ ((Algebra.norm (KK M H) v : KK M H) : LaurentSeries Qb)
      = (∏ j ∈ Finset.range ℓ, qTwist (ζ ^ j) ((w v : EEt M H ℓ) : LaurentSeries Qb))
        * qExpand Qb ℓ (v : LaurentSeries Qb) := by
  haveI := finiteDimensional_alpha M H ℓ hℓM
  apply ιE_injective ℓ
  have h1 := Algebra.norm_eq_prod_embeddings (K := KK M H) (L := EEt M H ℓ) (E := Om ℓ) v
  have h2 : algebraMap (KK M H) (Om ℓ) (Algebra.norm (KK M H) v)
      = ιE ℓ (qExpand Qb ℓ ((Algebra.norm (KK M H) v : KK M H) : LaurentSeries Qb)) := by
    rw [algebraMap_KOm_apply, coe_heckeBetaHBar M H ℓ h0]
  rw [← h2, h1, ← (emb_bijective h0 hζ w hw).prod_comp (fun σ => σ v), Fintype.prod_option,
    map_mul, map_prod, Finset.prod_range]
  simp only [emb_none_apply, emb_some_apply]
  exact mul_comm _ _

end Norm

end KroneckerNormHSol
p2m_reactivate "P2MW.S_ModularCurve_qExpand_norm_heckeBetaHBar.KroneckerNormHSol"

end
p2m_reactivate "P2MW.S_ModularCurve_qExpand_norm_heckeBetaHBar.KroneckerNormHSol"

open KroneckerNormHSol ModularCurve in
theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ ℓ)
    (u : ModularCurve.xHFunctionFieldBar M H) :
    ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
        ((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
          Algebra.norm (ModularCurve.xHFunctionFieldBar M H)
            (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ u) :
            ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) =
      (∏ b ∈ Finset.range ℓ,
          ModularCurve.qTwist (ζ ^ b)
            ((ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) u :
              ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ))) *
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
          (ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ (u : LaurentSeries (AlgebraicClosure ℚ))) := by
  have h0 : HeckeBetaHDefined M H ℓ := (hin.heckeInputsHAlong ℓ Fact.out).betaHDefined
  obtain ⟨w, hw⟩ := exists_AL (M := M) (H := H) (ℓ := ℓ) hℓM hin
  have hnorm := qExpand_norm h0 hζ w hw (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ u)
  rw [hw.2, coe_heckeAlphaHBar, coe_heckeBetaHBar M H ℓ h0] at hnorm
  exact hnorm

end S_ModularCurve_qExpand_norm_heckeBetaHBar
end P2MW
export P2MW.S_ModularCurve_qExpand_norm_heckeBetaHBar (solution)
