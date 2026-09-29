-- Prove2me | solution 1 for ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8dc2292c-d291-5732-adb4-4ec888bfecbf

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_HeckeDifferential
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential

namespace A2G1H1U

section Twist

variable {R : Type*} [Field R]

def twistFun (c : Rˣ) (x : LaurentSeries R) : LaurentSeries R where
  coeff n := ((c ^ n : Rˣ) : R) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

@[scoped simp] theorem twistFun_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twistFun c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem support_twistFun (c : Rˣ) (x : LaurentSeries R) : (twistFun c x).support = x.support := by
  ext n
  simp only [HahnSeries.mem_support, twistFun_coeff, ne_eq, Units.mul_right_eq_zero]

theorem twistFun_single (c : Rˣ) (k : ℤ) (r : R) :
    twistFun c (single k r) = single k (((c ^ k : Rˣ) : R) * r) := by
  ext n
  by_cases h : n = k
  · subst h; simp
  · simp [coeff_single_of_ne h]

def twist (c : Rˣ) : LaurentSeries R →ₐ[R] LaurentSeries R where
  toFun := twistFun c
  map_one' := by
    rw [← single_zero_one, twistFun_single]; simp
  map_mul' x y := by
    ext a
    rw [twistFun_coeff,
      coeff_mul_right' (x := x) (y := y) (twistFun c y).isPWO_support
        (support_twistFun c y).symm.subset,
      coeff_mul_left' (x := twistFun c x) (y := twistFun c y) x.isPWO_support
        (support_twistFun c x).subset,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [twistFun_coeff, twistFun_coeff, ← hij.2.2, zpow_add, Units.val_mul]
    ring
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]
  commutes' r := by
    rw [algebraMap_laurentSeries_eq_single]
    show twistFun c (single 0 r) = single 0 r
    rw [twistFun_single]; simp

@[scoped simp] theorem twist_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twist c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem twist_qExpand_of_pow_eq_one (c : Rˣ) (m : ℕ) [NeZero m] (hc : c ^ m = 1)
    (z : LaurentSeries R) : twist c (qExpand R m z) = qExpand R m z := by
  ext n
  rw [twist_coeff]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [zpow_mul, zpow_natCast, hc, one_zpow, Units.val_one, one_mul]
  · rw [qExpand_coeff_of_not_dvd m _ h, mul_zero]

theorem twist_C (c : Rˣ) (r : R) : twist c (C r) = C r := by
  show twistFun c (single 0 r) = single 0 r
  rw [twistFun_single]; simp

theorem twist_injective (c : Rˣ) : Function.Injective (twist c) := by
  intro a b hab
  ext n
  have := congrArg (fun s : LaurentSeries R => s.coeff n) hab
  simp only [twist_coeff] at this
  exact (mul_right_inj' (Units.ne_zero _)).mp this

theorem twist_ne_zero (c : Rˣ) {x : LaurentSeries R} (hx : x ≠ 0) : twist c x ≠ 0 :=
  fun h => hx (twist_injective c (by rw [h, map_zero]))

end Twist

section Euler

variable {R : Type*} [CommRing R]

theorem qEuler_qExpand (m : ℕ) [NeZero m] (x : LaurentSeries R) :
    qEuler R (qExpand R m x) = C (m : R) * qExpand R m (qEuler R x) := by
  ext n
  rw [qEuler_coeff, C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, qEuler_coeff]
    push_cast
    ring
  · rw [qExpand_coeff_of_not_dvd m _ h, qExpand_coeff_of_not_dvd m _ h, mul_zero, mul_zero]

theorem coeff_C_mul (r : R) (x : LaurentSeries R) (n : ℤ) :
    (C r * x).coeff n = r * x.coeff n := by
  rw [C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

end Euler

section Pull

variable {L : Type*} [Field L]

theorem diffQExp_pullbackAlong (F₁ F₂ : IntermediateField L (LaurentSeries L))
    (φ : F₁ →ₐ[L] F₂) (ρ : LaurentSeries L →+* LaurentSeries L) (c : L)
    (hφ : ∀ x : F₁, ((φ x : F₂) : LaurentSeries L) = ρ x)
    (hρ : ∀ y, qEuler L (ρ y) = C c * ρ (qEuler L y)) (η : Ω[F₁⁄L]) :
    diffQExp F₂ (pullbackAlong φ η) = C c * ρ (diffQExp F₁ η) := by
  have key : ∀ η : Ω[F₁⁄L], η ∈ Submodule.span F₁ (Set.range (D L F₁)) → ∀ f : F₁,
      diffQExp F₂ (pullbackAlong φ (f • η)) = C c * ρ (diffQExp F₁ (f • η)) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, diffQExp_smul_D, diffQExp_smul_D, hφ, hφ, hρ,
        map_mul, mul_left_comm]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, mul_add]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem diffQExp_smul (F : IntermediateField L (LaurentSeries L)) (u : F) (ξ : Ω[F⁄L]) :
    diffQExp F (u • ξ) = (u : LaurentSeries L) * diffQExp F ξ := by
  rw [map_smul]; rfl

end Pull

section RootSum

variable {R : Type*} [Field R]

def rootSum (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) : LaurentSeries R :=
  ∑ j ∈ Finset.range ℓ, twist (u ^ j) x

theorem rootSum_apply (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) :
    rootSum u ℓ x = ∑ j ∈ Finset.range ℓ, twist (u ^ j) x := rfl

theorem rootSum_add (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R) :
    rootSum u ℓ (x + y) = rootSum u ℓ x + rootSum u ℓ y := by
  simp only [rootSum, map_add, Finset.sum_add_distrib]

theorem rootSum_zero (u : Rˣ) (ℓ : ℕ) : rootSum u ℓ (0 : LaurentSeries R) = 0 := by
  simp only [rootSum, map_zero, Finset.sum_const_zero]

theorem rootSum_mul_of_fixed (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R)
    (hy : ∀ j : ℕ, twist (u ^ j) y = y) : rootSum u ℓ (x * y) = rootSum u ℓ x * y := by
  rw [rootSum_apply, rootSum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hy]

theorem sum_zpow_pow {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (n : ℤ) :
    ∑ j ∈ Finset.range ℓ, (ζ ^ n) ^ j = if (ℓ : ℤ) ∣ n then (ℓ : R) else 0 := by
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd n).mpr h]
    simp
  · have hne : ζ ^ n ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd n).mp h')
    rw [geom_sum_eq hne]
    have : (ζ ^ n) ^ ℓ = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

theorem rootSum_coeff {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (hz : ζ ≠ 0)
    (x : LaurentSeries R) (n : ℤ) :
    (rootSum (Units.mk0 ζ hz) ℓ x).coeff n = if (ℓ : ℤ) ∣ n then (ℓ : R) * x.coeff n else 0 := by
  rw [rootSum_apply, HahnSeries.coeff_sum]
  simp only [twist_coeff]
  rw [← Finset.sum_mul]
  have h : ∀ j ∈ Finset.range ℓ, (((Units.mk0 ζ hz ^ j) ^ n : Rˣ) : R) = (ζ ^ n) ^ j := by
    intro j _
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [Finset.sum_congr rfl h, sum_zpow_pow hζ n]
  split_ifs <;> simp

end RootSum

section Separating

open ModularForm UpperHalfPlane EisensteinSeries CongruenceSubgroup
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

def xq : LaurentSeries ℚ := intSeriesC ℚ (P6 ^ 2) / intSeriesC ℚ (P4 ^ 3)

theorem xq_mem : xq ∈ qExpFunctionFieldC ℚ Γ :=
  div_mem_qExpFunctionFieldC (B12 Γ) (A12 Γ) (isIntegralQExp_B12 Γ) (isIntegralQExp_A12 Γ)
    intSeriesC_P4_cube_ne_zero

end Separating

section TwistPS

local notation "Qb" => AlgebraicClosure ℚ

theorem intSeriesC_coeff_of_neg (K : Type*) [Field K] (p : PowerSeries ℤ) {n : ℤ} (hn : n < 0) :
    (intSeriesC K p).coeff n = 0 := by
  rw [intSeriesC, PowerSeries.coeff_coe, if_pos hn]

theorem intSeriesC_coeff_natCast (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    (intSeriesC K p).coeff (n : ℤ) = ((PowerSeries.coeff n p : ℤ) : K) := by
  rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast]

theorem twist_intSeriesC (c : Qbˣ) (p : PowerSeries ℤ) :
    twist c (intSeriesC Qb p) =
      HahnSeries.ofPowerSeries ℤ Qb (PowerSeries.rescale (c : Qb) (p.map (Int.castRingHom Qb))) := by
  ext n
  rw [twist_coeff, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [intSeriesC_coeff_of_neg Qb p hn, mul_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hn)
    rw [intSeriesC_coeff_natCast, Int.natAbs_natCast, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
      eq_intCast, zpow_natCast, Units.val_pow_eq_pow_val]

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [Algebra ℚ L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · rw [map_zero]
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

def numB : LaurentSeries Qb := intSeriesC Qb (P6 ^ 2)

def denA : LaurentSeries Qb := intSeriesC Qb (P4 ^ 3)

theorem denA_ne_zero : denA ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff (by rw [map_pow, constantCoeff_P4, one_pow])

def PBs (a : Qb) : PowerSeries Qb := PowerSeries.rescale a ((P6 ^ 2).map (Int.castRingHom Qb))

def PAs (a : Qb) : PowerSeries Qb := PowerSeries.rescale a ((P4 ^ 3).map (Int.castRingHom Qb))

theorem coeff_zero_PBs (a : Qb) : PowerSeries.coeff 0 (PBs a) = 1 := by
  rw [PBs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, constantCoeff_P6]
  simp

theorem coeff_zero_PAs (a : Qb) : PowerSeries.coeff 0 (PAs a) = 1 := by
  rw [PAs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, constantCoeff_P4]
  simp

theorem coeff_one_PBs (a : Qb) : PowerSeries.coeff 1 (PBs a) = a * (-1008) := by
  rw [PBs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P6,
    constantCoeff_P6, eq_intCast]
  push_cast
  ring

theorem coeff_one_PAs (a : Qb) : PowerSeries.coeff 1 (PAs a) = a * 720 := by
  rw [PAs, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P4,
    constantCoeff_P4, eq_intCast]
  push_cast
  ring

theorem coeff_one_mul' (φ ψ : PowerSeries Qb) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ + PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.Nat.antidiagonal_zero]
  simp

theorem twist_sep {a b : Qbˣ} (h : twist a (numB / denA) = twist b (numB / denA)) : (a : Qb) = b := by
  rw [map_div₀, map_div₀, div_eq_div_iff (twist_ne_zero a denA_ne_zero) (twist_ne_zero b denA_ne_zero)]
    at h
  rw [numB, denA, twist_intSeriesC, twist_intSeriesC, twist_intSeriesC, twist_intSeriesC, ← map_mul,
    ← map_mul] at h
  have h' := HahnSeries.ofPowerSeries_injective h
  have h1 := congrArg (PowerSeries.coeff 1) h'
  change PowerSeries.coeff 1 (PBs a * PAs b) = PowerSeries.coeff 1 (PBs b * PAs a) at h1
  rw [coeff_one_mul', coeff_one_mul', coeff_zero_PBs, coeff_zero_PAs, coeff_one_PBs, coeff_one_PAs,
    coeff_zero_PBs, coeff_zero_PAs, coeff_one_PBs, coeff_one_PAs] at h1
  have h2 : (1728 : Qb) * (b - a) = 0 := by linear_combination h1
  have h1728 : (1728 : Qb) ≠ 0 := by norm_num
  have := (mul_eq_zero.mp h2).resolve_left h1728
  exact (sub_eq_zero.mp this).symm

end TwistPS

section Trace

local notation "Qb" => AlgebraicClosure ℚ

def EE (_ℓ : ℕ) : Type := AlgebraicClosure (LaurentSeries Qb)

variable (ℓ : ℕ) in
scoped instance : Field (EE ℓ) := inferInstanceAs (Field (AlgebraicClosure (LaurentSeries Qb)))

variable (ℓ : ℕ) in
scoped instance : IsAlgClosed (EE ℓ) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries Qb)))

def ιE (ℓ : ℕ) : LaurentSeries Qb →+* EE ℓ :=
  algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))

theorem ιE_injective (ℓ : ℕ) : Function.Injective (ιE ℓ) :=
  (algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))).injective

variable (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime]

abbrev FXt : Type := ↥(x1FunctionFieldBar M)

abbrev FUf : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (x1x0FunctionFieldC ℚ M (M * ℓ))

abbrev FUt : Type := ↥(FUf M ℓ)

abbrev bβ : FXt M →ₐ[Qb] FUt M ℓ := heckeBetaOneBar Qb M ℓ

abbrev bα : FXt M →ₐ[Qb] FUt M ℓ := heckeAlphaOneBar Qb M ℓ

@[reducible] def algAlongBeta : Algebra (FXt M) (FUt M ℓ) :=
  algebraAlong (bβ M ℓ)

@[reducible] def algBetaE : Algebra (FXt M) (EE ℓ) :=
  (((ιE ℓ).comp (algebraMap (FUt M ℓ) (LaurentSeries Qb))).comp (bβ M ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongBeta algBetaE

omit [NeZero M] in
theorem isScalarTower_beta : IsScalarTower Qb (FXt M) (FUt M ℓ) :=
  isScalarTower_along (bβ M ℓ)

attribute [local instance] isScalarTower_beta

theorem finrank_beta (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) :
    Module.finrank (FXt M) (FUt M ℓ) = ℓ := by
  have h := ModularCurve.finrankAlong_heckeBetaOneBar Qb M ℓ hβ
  rw [if_pos hℓM] at h
  exact h

theorem finiteDimensional_beta (hβ : HeckeBetaOneDefined M ℓ) :
    FiniteDimensional (FXt M) (FUt M ℓ) := by
  refine Module.finite_of_finrank_pos ?_
  have h := ModularCurve.finrankAlong_heckeBetaOneBar Qb M ℓ hβ
  change Module.finrank (FXt M) (FUt M ℓ) = _ at h
  rw [h]
  split_ifs
  · exact (Fact.out : ℓ.Prime).pos
  · exact Nat.succ_pos ℓ

theorem separableAlong_beta (hβ : HeckeBetaOneDefined M ℓ) : SeparableAlong Qb (bβ M ℓ) := by
  haveI := finiteDimensional_beta M ℓ hβ
  show Algebra.IsSeparable (FXt M) (FUt M ℓ)
  infer_instance

variable {M ℓ}

def sigmaTwist (hβ : HeckeBetaOneDefined M ℓ) (c : Qbˣ) (hc : c ^ ℓ = 1) :
    FUt M ℓ →ₐ[FXt M] EE ℓ where
  toRingHom := (ιE ℓ).comp ((twist c).toRingHom.comp (algebraMap (FUt M ℓ) (LaurentSeries Qb)))
  commutes' f := by
    show ιE ℓ (twist c ((bβ M ℓ f : FUt M ℓ) : LaurentSeries Qb)) =
      ιE ℓ ((bβ M ℓ f : FUt M ℓ) : LaurentSeries Qb)
    rw [coe_heckeBetaOneBar M ℓ hβ, twist_qExpand_of_pow_eq_one c ℓ hc]

omit [NeZero M] in
theorem sigmaTwist_apply (hβ : HeckeBetaOneDefined M ℓ) (c : Qbˣ) (hc : c ^ ℓ = 1) (v : FUt M ℓ) :
    sigmaTwist hβ c hc v = ιE ℓ (twist c (v : LaurentSeries Qb)) := rfl

def zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Qbˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem zu_pow {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

def emb (hβ : HeckeBetaOneDefined M ℓ) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Fin ℓ → (FUt M ℓ →ₐ[FXt M] EE ℓ) :=
  fun j => sigmaTwist hβ (zu hζ ^ (j : ℕ)) (zu_pow hζ j)

variable (M) in

def xBar : FXt M :=
  ⟨coeffEmb Qb xq, coeffEmb_mem_laurentBaseChange Qb (xq_mem (CongruenceSubgroup.Gamma1 M))⟩

omit [NeZero M] in
theorem coe_xBar : ((xBar M : FXt M) : LaurentSeries Qb) = numB / denA := by
  show coeffEmb Qb xq = _
  rw [xq, map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  rfl

omit [NeZero M] in

theorem emb_injective (hβ : HeckeBetaOneDefined M ℓ) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (emb hβ hζ) := by

  have vsome : ∀ j : Fin ℓ, emb hβ hζ j (bα M ℓ (xBar M)) =
      ιE ℓ (twist (zu hζ ^ (j : ℕ)) (numB / denA)) := by
    intro j
    show sigmaTwist hβ (zu hζ ^ (j : ℕ)) (zu_pow hζ j) (bα M ℓ (xBar M)) = _
    rw [sigmaTwist_apply, coe_heckeAlphaOneBar, coe_xBar]
  intro i j h
  have h' := congrArg (fun σ : FUt M ℓ →ₐ[FXt M] EE ℓ => σ (bα M ℓ (xBar M))) h
  beta_reduce at h'
  rw [vsome, vsome] at h'
  have h1 := twist_sep (ιE_injective ℓ h')
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu, Units.val_mk0] at h1
  exact Fin.ext (hζ.pow_inj i.2 j.2 h1)

theorem emb_bijective (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Bijective (emb hβ hζ) := by
  haveI := finiteDimensional_beta M ℓ hβ
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective hβ hζ, ?_⟩
  rw [Fintype.card_fin, AlgHom.card, finrank_beta M ℓ hβ hℓM]

theorem qExpand_trace (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (v : FUt M ℓ) :
    qExpand Qb ℓ ((Algebra.trace (FXt M) (FUt M ℓ) v : FXt M) : LaurentSeries Qb)
      = rootSum (zu hζ) ℓ (v : LaurentSeries Qb) := by
  haveI := finiteDimensional_beta M ℓ hβ
  apply ιE_injective ℓ
  have h1 := trace_eq_sum_embeddings (EE ℓ) (K := FXt M) (L := FUt M ℓ) (x := v)
  have h2 : algebraMap (FXt M) (EE ℓ) (Algebra.trace (FXt M) (FUt M ℓ) v)
      = ιE ℓ (qExpand Qb ℓ ((Algebra.trace (FXt M) (FUt M ℓ) v : FXt M) : LaurentSeries Qb)) := by
    show ιE ℓ ((bβ M ℓ _ : FUt M ℓ) : LaurentSeries Qb) = _
    rw [coe_heckeBetaOneBar M ℓ hβ]
  rw [← h2, h1, ← (emb_bijective hβ hℓM hζ).sum_comp (fun σ => σ v), rootSum_apply, map_sum,
    Finset.sum_range]
  rfl

end Trace

section Assembly

local notation "Qb" => AlgebraicClosure ℚ

variable {M ℓ : ℕ} [NeZero M] [Fact ℓ.Prime]

attribute [local instance] algAlongBeta algBetaE isScalarTower_beta

local notation "FN" => x1FunctionFieldBar M
local notation "FNl" => FUf M ℓ
local notation "β" => heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ
local notation "α" => heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ

omit [NeZero M] in

theorem diffQExp_pullback_beta (hβ : HeckeBetaOneDefined M ℓ) (η : Ω[↥FN⁄Qb]) :
    diffQExp FNl (pullbackAlong β η) = C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN η) :=
  diffQExp_pullbackAlong FN FNl β (qExpand Qb ℓ) ℓ (fun x => coe_heckeBetaOneBar M ℓ hβ x)
    (fun y => qEuler_qExpand ℓ y) η

theorem twist_fix {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) (z : LaurentSeries Qb) :
    twist (zu hζ ^ j) (C (ℓ : Qb) * qExpand Qb ℓ z) = C (ℓ : Qb) * qExpand Qb ℓ z := by
  rw [map_mul, twist_C, twist_qExpand_of_pow_eq_one _ ℓ (zu_pow hζ j)]

def MC {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (ξ : Ω[↥FNl⁄Qb]) : Prop :=
  ∀ v : ↥FNl, C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (traceAlong β (v • ξ)))
    = rootSum (zu hζ) ℓ ((v : LaurentSeries Qb) * diffQExp FNl ξ)

theorem MC_base (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (η : Ω[↥FN⁄Qb]) : MC hζ (pullbackAlong β η) := by
  intro v
  rw [traceAlong_smul_pullbackAlong β (separableAlong_beta M ℓ hβ) v η, diffQExp_smul, map_mul,
    qExpand_trace hβ hℓM hζ v, diffQExp_pullback_beta hβ,
    rootSum_mul_of_fixed _ _ _ _ (fun j => twist_fix hζ j _)]
  ring

omit [NeZero M] in
theorem MC_smul {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (ξ : Ω[↥FNl⁄Qb]) (h : MC (M := M) hζ ξ) (u' : ↥FNl) : MC (M := M) hζ (u' • ξ) := by
  intro v
  have e1 : v • (u' • ξ) = (v * u') • ξ := smul_smul v u' ξ
  have e2 : (v : LaurentSeries Qb) * diffQExp FNl (u' • ξ)
      = ((v * u' : ↥FNl) : LaurentSeries Qb) * diffQExp FNl ξ := by
    rw [diffQExp_smul, ← mul_assoc]; rfl
  rw [e1, e2]
  exact h (v * u')

omit [NeZero M] in
theorem MC_add {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (ξ₁ ξ₂ : Ω[↥FNl⁄Qb]) (h₁ : MC (M := M) hζ ξ₁) (h₂ : MC (M := M) hζ ξ₂) :
    MC (M := M) hζ (ξ₁ + ξ₂) := by
  intro v
  simp only [smul_add, map_add, mul_add, rootSum_add]
  rw [h₁ v, h₂ v]

omit [NeZero M] in
theorem MC_zero {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : MC (M := M) hζ 0 := by
  intro v
  simp only [smul_zero, map_zero, mul_zero, rootSum_zero]

theorem MC_all (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (ξ : Ω[↥FNl⁄Qb]) : MC hζ ξ := by
  haveI := finiteDimensional_beta M ℓ hβ
  haveI : Algebra.IsSeparable (FXt M) (FUt M ℓ) := separableAlong_beta M ℓ hβ
  haveI : Algebra.FormallyEtale (FXt M) (FUt M ℓ) := Algebra.FormallyEtale.of_isSeparable _ _
  obtain ⟨t, rfl⟩ :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Qb (FXt M) (FUt M ℓ)).surjective ξ
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact MC_zero hζ
  | tmul u' η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    change MC hζ (u' • pullbackAlong β η)
    exact MC_smul hζ _ (MC_base hβ hℓM hζ η) u'
  | add x y hx hy => rw [map_add]; exact MC_add hζ _ _ hx hy

theorem key_identity (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (ω : Ω[↥FN⁄Qb]) :
    C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (Differential.correspondence β α ω))
      = rootSum (zu hζ) ℓ (diffQExp FN ω) := by
  have key : ∀ ω : Ω[↥FN⁄Qb], ω ∈ Submodule.span (↥FN) (Set.range (D Qb ↥FN)) → ∀ f : ↥FN,
      C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (Differential.correspondence β α (f • ω)))
        = rootSum (zu hζ) ℓ (diffQExp FN (f • ω)) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem ω h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      have hM := MC_all hβ hℓM hζ (D Qb ↥FNl (α g)) (α f)
      rw [correspondence_apply, pullbackAlong_smul, pullbackAlong_D, hM, diffQExp_D,
        diffQExp_smul_D, coe_heckeAlphaOneBar, coe_heckeAlphaOneBar]
    | zero => intro f; simp [rootSum_zero]
    | add x y _ _ hx hy =>
      intro f
      simp only [smul_add, map_add, mul_add, rootSum_add]
      rw [hx f, hy f]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem coeff_identity (hβ : HeckeBetaOneDefined M ℓ) (hℓM : ℓ ∣ M) (ω : Ω[↥FN⁄Qb]) (n : ℤ) :
    (diffQExp FN (Differential.correspondence β α ω)).coeff n
      = (diffQExp FN ω).coeff (n * ℓ) := by
  haveI : NeZero ((ℓ : ℕ) : Qb) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb ℓ
  have h := congrArg (fun s : LaurentSeries Qb => s.coeff ((ℓ : ℤ) * n)) (key_identity hβ hℓM hζ ω)
  beta_reduce at h
  rw [coeff_C_mul, qExpand_coeff_mul, zu, rootSum_coeff hζ, if_pos (dvd_mul_right _ _)] at h
  have hℓ0 : ((ℓ : ℕ) : Qb) ≠ 0 := NeZero.ne _
  have h' := mul_left_cancel₀ hℓ0 h
  rw [h', mul_comm (ℓ : ℤ) n]

end Assembly

end A2G1H1U
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd.A2G1H1U"

open ModularCurve

theorem solution
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
        (AlgebraicCurve.Differential.correspondence
          (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
          (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) ω)).coeff n =
      (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω).coeff (n * ℓ) :=
  A2G1H1U.coeff_identity hβ hℓM ω n

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd.A2G1H1U"

end S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
end P2MW
export P2MW.S_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd (solution)
