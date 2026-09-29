-- Prove2me | solution 1 for ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5c8abf58-22bc-5053-8195-fc19492aa12d

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential

namespace W7UCotQExpHeckeDvd

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

section Bar

local notation "Qb" => AlgebraicClosure ℚ

def jBar (M : ℕ) : modularFunctionFieldBar M :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (by
    simpa [qExpand_one_apply] using jqd_mem_full M (one_dvd _) (d := 1))⟩

@[scoped simp] theorem coe_jBar (M : ℕ) : ((jBar M : modularFunctionFieldBar M) : LaurentSeries Qb)
    = coeffEmb Qb jq := rfl

theorem coeffEmb_jq_coeff_neg_one : (coeffEmb Qb jq).coeff (-1) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

end Bar

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

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

@[reducible] def algAlongBeta :
    Algebra (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) :=
  algebraAlong (heckeBetaBar Qb N ℓ)

@[reducible] def algBetaE : Algebra (modularFunctionFieldBar N) (EE ℓ) :=
  (((ιE ℓ).comp (algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb))).comp
    (heckeBetaBar Qb N ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongBeta algBetaE

omit [NeZero N] in
theorem isScalarTower_beta :
    IsScalarTower Qb (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) :=
  isScalarTower_along (heckeBetaBar Qb N ℓ)

attribute [local instance] isScalarTower_beta

theorem finrank_beta (hℓN : ℓ ∣ N) :
    Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) = ℓ := by
  have h := ModularCurve.finrankAlong_heckeBetaBar Qb N ℓ
  rw [if_pos hℓN] at h
  exact h

theorem finiteDimensional_beta :
    FiniteDimensional (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) := by
  refine Module.finite_of_finrank_pos ?_
  have h := ModularCurve.finrankAlong_heckeBetaBar Qb N ℓ
  change Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) = _ at h
  rw [h]
  split_ifs
  · exact (Fact.out : ℓ.Prime).pos
  · exact Nat.succ_pos ℓ

attribute [local instance] finiteDimensional_beta

theorem isSeparable_beta :
    Algebra.IsSeparable (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) :=
  inferInstance

attribute [local instance] isSeparable_beta

theorem separableAlong_beta : SeparableAlong Qb (heckeBetaBar Qb N ℓ) :=
  isSeparable_beta N ℓ

variable {N ℓ}

def sigmaTwist (c : Qbˣ) (hc : c ^ ℓ = 1) :
    modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ where
  toRingHom := (ιE ℓ).comp ((twist c).toRingHom.comp
    (algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb)))
  commutes' f := by
    show ιE ℓ (twist c ((heckeBetaBar Qb N ℓ f : modularFunctionFieldBar (N * ℓ)) :
        LaurentSeries Qb)) = ιE ℓ ((heckeBetaBar Qb N ℓ f : modularFunctionFieldBar (N * ℓ)) :
        LaurentSeries Qb)
    rw [coe_heckeBetaBar, twist_qExpand_of_pow_eq_one c ℓ hc]

omit [NeZero N] in
theorem sigmaTwist_apply (c : Qbˣ) (hc : c ^ ℓ = 1) (v : modularFunctionFieldBar (N * ℓ)) :
    sigmaTwist (N := N) c hc v = ιE ℓ (twist c (v : LaurentSeries Qb)) := rfl

def zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Qbˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem zu_pow {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

def emb {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Fin ℓ → (modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ) :=
  fun j => sigmaTwist (zu hζ ^ (j : ℕ)) (zu_pow hζ j)

omit [NeZero N] in
theorem emb_injective {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (emb (N := N) hζ) := by
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne ℓ)

  have key : ∀ j : Fin ℓ, ∃ s : LaurentSeries Qb,
      emb (N := N) hζ j (jBar (N * ℓ)) = ιE ℓ s ∧ s.coeff (-1) = (ζ ^ (j : ℕ))⁻¹ := by
    intro j
    refine ⟨twist (zu hζ ^ (j : ℕ)) (coeffEmb Qb jq), rfl, ?_⟩
    rw [twist_coeff, coeffEmb_jq_coeff_neg_one, mul_one, zpow_neg_one, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, zu, Units.val_mk0]
  intro j₁ j₂ h
  obtain ⟨s₁, hs₁, hc₁⟩ := key j₁
  obtain ⟨s₂, hs₂, hc₂⟩ := key j₂
  have hs : s₁ = s₂ := ιE_injective ℓ (by rw [← hs₁, ← hs₂, h])
  rw [hs] at hc₁
  have hv : ζ ^ (j₁ : ℕ) = ζ ^ (j₂ : ℕ) := inv_inj.mp (hc₁.symm.trans hc₂)
  exact Fin.ext (hζ.pow_inj j₁.2 j₂.2 hv)

theorem emb_bijective (hℓN : ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Bijective (emb (N := N) hζ) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective hζ, ?_⟩
  rw [Fintype.card_fin, AlgHom.card, finrank_beta N ℓ hℓN]

theorem qExpand_trace (hℓN : ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (v : modularFunctionFieldBar (N * ℓ)) :
    qExpand Qb ℓ ((Algebra.trace (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) v :
        modularFunctionFieldBar N) : LaurentSeries Qb)
      = rootSum (zu hζ) ℓ (v : LaurentSeries Qb) := by
  apply ιE_injective ℓ
  have h1 := trace_eq_sum_embeddings (EE ℓ) (K := modularFunctionFieldBar N)
    (L := modularFunctionFieldBar (N * ℓ)) (x := v)
  have h2 : algebraMap (modularFunctionFieldBar N) (EE ℓ)
      (Algebra.trace (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) v)
      = ιE ℓ (qExpand Qb ℓ ((Algebra.trace (modularFunctionFieldBar N)
          (modularFunctionFieldBar (N * ℓ)) v : modularFunctionFieldBar N) : LaurentSeries Qb)) := by
    show ιE ℓ ((heckeBetaBar Qb N ℓ _ : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb) = _
    rw [coe_heckeBetaBar]
  rw [← h2, h1, ← (emb_bijective hℓN hζ).sum_comp (fun σ => σ v), rootSum_apply, map_sum,
    Finset.sum_range]
  rfl

end Trace

section Assembly

local notation "Qb" => AlgebraicClosure ℚ

variable {N ℓ : ℕ} [NeZero N] [Fact ℓ.Prime]

attribute [local instance] algAlongBeta algBetaE isScalarTower_beta finiteDimensional_beta
  isSeparable_beta

local notation "FN" => modularFunctionFieldBar N
local notation "FNl" => modularFunctionFieldBar (N * ℓ)
local notation "β" => heckeBetaBar (AlgebraicClosure ℚ) N ℓ
local notation "α" => heckeAlphaBar (AlgebraicClosure ℚ) N ℓ

theorem heckeDiffBar_apply (x : Ω[FN⁄Qb]) :
    heckeDiffBar N ⟨ℓ, Fact.out⟩ x = traceAlong β (pullbackAlong α x) := rfl

omit [NeZero N] in

theorem diffQExp_pullback_beta (η : Ω[FN⁄Qb]) :
    diffQExp FNl (pullbackAlong β η) = C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN η) :=
  diffQExp_pullbackAlong FN FNl β (qExpand Qb ℓ) ℓ (fun x => coe_heckeBetaBar N ℓ x)
    (fun y => qEuler_qExpand ℓ y) η

theorem twist_fix {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) (z : LaurentSeries Qb) :
    twist (zu hζ ^ j) (C (ℓ : Qb) * qExpand Qb ℓ z) = C (ℓ : Qb) * qExpand Qb ℓ z := by
  rw [map_mul, twist_C, twist_qExpand_of_pow_eq_one _ ℓ (zu_pow hζ j)]

def MC {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (ξ : Ω[FNl⁄Qb]) : Prop :=
  ∀ v : FNl, C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (traceAlong β (v • ξ)))
    = rootSum (zu hζ) ℓ ((v : LaurentSeries Qb) * diffQExp FNl ξ)

theorem MC_base (hℓN : ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (η : Ω[FN⁄Qb]) : MC hζ (pullbackAlong β η) := by
  intro v
  rw [traceAlong_smul_pullbackAlong β (separableAlong_beta N ℓ) v η, diffQExp_smul, map_mul,
    qExpand_trace hℓN hζ v, diffQExp_pullback_beta,
    rootSum_mul_of_fixed _ _ _ _ (fun j => twist_fix hζ j _)]
  ring

omit [NeZero N] in
theorem MC_smul {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (ξ : Ω[FNl⁄Qb]) (h : MC (N := N) hζ ξ) (u' : FNl) : MC (N := N) hζ (u' • ξ) := by
  intro v
  have e1 : v • (u' • ξ) = (v * u') • ξ := smul_smul v u' ξ
  have e2 : (v : LaurentSeries Qb) * diffQExp FNl (u' • ξ)
      = ((v * u' : FNl) : LaurentSeries Qb) * diffQExp FNl ξ := by
    rw [diffQExp_smul, ← mul_assoc]; rfl
  rw [e1, e2]
  exact h (v * u')

omit [NeZero N] in
theorem MC_add {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (ξ₁ ξ₂ : Ω[FNl⁄Qb]) (h₁ : MC (N := N) hζ ξ₁) (h₂ : MC (N := N) hζ ξ₂) :
    MC (N := N) hζ (ξ₁ + ξ₂) := by
  intro v
  simp only [smul_add, map_add, mul_add, rootSum_add]
  rw [h₁ v, h₂ v]

omit [NeZero N] in
theorem MC_zero {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : MC (N := N) hζ 0 := by
  intro v
  simp only [smul_zero, map_zero, mul_zero, rootSum_zero]

theorem MC_all (hℓN : ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (ξ : Ω[FNl⁄Qb]) : MC hζ ξ := by
  haveI : Algebra.FormallyEtale FN FNl := Algebra.FormallyEtale.of_isSeparable FN FNl
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Qb FN FNl).surjective ξ
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact MC_zero hζ
  | tmul u' η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    change MC hζ (u' • pullbackAlong β η)
    exact MC_smul hζ _ (MC_base hℓN hζ η) u'
  | add x y hx hy => rw [map_add]; exact MC_add hζ _ _ hx hy

theorem key_identity (hℓN : ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (ω : Ω[FN⁄Qb]) :
    C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (heckeDiffBar N ⟨ℓ, Fact.out⟩ ω))
      = rootSum (zu hζ) ℓ (diffQExp FN ω) := by
  have key : ∀ ω : Ω[FN⁄Qb], ω ∈ Submodule.span FN (Set.range (D Qb FN)) → ∀ f : FN,
      C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (heckeDiffBar N ⟨ℓ, Fact.out⟩ (f • ω)))
        = rootSum (zu hζ) ℓ (diffQExp FN (f • ω)) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem ω h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      have hM := MC_all hℓN hζ (D Qb FNl (α g)) (α f)
      rw [heckeDiffBar_apply, pullbackAlong_smul, pullbackAlong_D, hM, diffQExp_D,
        diffQExp_smul_D, coe_heckeAlphaBar, coe_heckeAlphaBar]
    | zero => intro f; simp [rootSum_zero]
    | add x y _ _ hx hy =>
      intro f
      simp only [smul_add, map_add, mul_add, rootSum_add]
      rw [hx f, hy f]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem coeff_identity (hℓN : ℓ ∣ N) (ω : Ω[FN⁄Qb]) (n : ℤ) :
    (diffQExp FN (heckeDiffBar N ⟨ℓ, Fact.out⟩ ω)).coeff n
      = (diffQExp FN ω).coeff (n * ℓ) := by
  haveI : NeZero ((ℓ : ℕ) : Qb) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb ℓ
  have h := congrArg (fun s : LaurentSeries Qb => s.coeff ((ℓ : ℤ) * n)) (key_identity hℓN hζ ω)
  beta_reduce at h
  rw [coeff_C_mul, qExpand_coeff_mul, zu, rootSum_coeff hζ, if_pos (dvd_mul_right _ _)] at h
  have hℓ0 : ((ℓ : ℕ) : Qb) ≠ 0 := NeZero.ne _
  have h' := mul_left_cancel₀ hℓ0 h
  rw [h', mul_comm (ℓ : ℤ) n]

end Assembly

end W7UCotQExpHeckeDvd
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd.W7UCotQExpHeckeDvd"

open ModularCurve

theorem solution (N : ℕ) [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExpBar N (ModularCurve.heckeDiffBar N ⟨ℓ, Fact.out⟩ ω)).coeff n =
      (ModularCurve.diffQExpBar N ω).coeff (n * ℓ) :=
  W7UCotQExpHeckeDvd.coeff_identity hℓN ω n

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd.W7UCotQExpHeckeDvd"

end S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd
end P2MW
export P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_dvd (solution)
