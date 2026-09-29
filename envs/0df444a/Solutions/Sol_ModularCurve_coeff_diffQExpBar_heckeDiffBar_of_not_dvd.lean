-- Prove2me | solution 1 for ModularCurve.coeff_diffQExpBar_heckeDiffBar_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/fa144dfd-0aac-5b99-b50b-8fb8cc05743f

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential

namespace W5MCotQExpHecke

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

theorem pullbackAlong_pullbackAlong (F₁ F₂ F₃ : Type*) [Field F₁] [Field F₂] [Field F₃]
    [Algebra L F₁] [Algebra L F₂] [Algebra L F₃] (φ : F₁ →ₐ[L] F₂) (ψ : F₂ →ₐ[L] F₃)
    (η : Ω[F₁⁄L]) :
    pullbackAlong ψ (pullbackAlong φ η) = pullbackAlong (ψ.comp φ) η := by
  have key : ∀ η : Ω[F₁⁄L], η ∈ Submodule.span F₁ (Set.range (D L F₁)) → ∀ f : F₁,
      pullbackAlong ψ (pullbackAlong φ (f • η)) = pullbackAlong (ψ.comp φ) (f • η) := by
    intro η hη
    induction hη using Submodule.span_induction with
    | mem η h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      rw [pullbackAlong_smul, pullbackAlong_D, pullbackAlong_smul, pullbackAlong_D,
        pullbackAlong_smul, pullbackAlong_D, AlgHom.comp_apply, AlgHom.comp_apply]
    | zero => intro f; simp
    | add x y _ _ hx hy =>
      intro f
      rw [smul_add, map_add, map_add, hx, hy, map_add]
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key η (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem diffQExp_smul (F : IntermediateField L (LaurentSeries L)) (u : F) (ξ : Ω[F⁄L]) :
    diffQExp F (u • ξ) = (u : LaurentSeries L) * diffQExp F ξ := by
  rw [map_smul]; rfl

end Pull

section RootSum

variable {R : Type*} [Field R]

theorem twist_C (c : Rˣ) (r : R) : twist c (C r) = C r := by
  show twistFun c (single 0 r) = single 0 r
  rw [twistFun_single]; simp

def rootSum (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) : LaurentSeries R :=
  ∑ j ∈ Finset.range ℓ, twist (u ^ j) x

theorem rootSum_apply (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) :
    rootSum u ℓ x = ∑ j ∈ Finset.range ℓ, twist (u ^ j) x := rfl

theorem rootSum_add (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R) :
    rootSum u ℓ (x + y) = rootSum u ℓ x + rootSum u ℓ y := by
  simp only [rootSum, map_add, Finset.sum_add_distrib]

theorem rootSum_zero (u : Rˣ) (ℓ : ℕ) : rootSum u ℓ (0 : LaurentSeries R) = 0 := by
  simp only [rootSum, map_zero, Finset.sum_const_zero]

theorem rootSum_C_mul (u : Rˣ) (ℓ : ℕ) (r : R) (x : LaurentSeries R) :
    rootSum u ℓ (C r * x) = C r * rootSum u ℓ x := by
  simp only [rootSum, map_mul, twist_C, Finset.mul_sum]

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

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
      = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]

theorem modularFunctionFieldBar_eq_adjoin (M : ℕ) :
    modularFunctionFieldBar M
      = IntermediateField.adjoin Qb (coeffEmb Qb '' divisorExpansions M) := by
  apply le_antisymm
  · change laurentBaseChange Qb (modularFunctionFieldFull M) ≤ _
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ _) at hy
    have hy' : coeffEmb Qb y ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M)).map (coeffEmb Qb) :=
      ⟨y, hy, rfl⟩
    rw [RingHom.map_field_closure] at hy'
    refine (Subfield.closure_le (t := (IntermediateField.adjoin Qb
      (coeffEmb Qb '' divisorExpansions M)).toSubfield)).mpr ?_ hy'
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨c, rfl⟩ | hx
    · rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange Qb (IntermediateField.subset_adjoin ℚ _ hx)

theorem algHom_ext_bar (M : ℕ) {E : Type*} [Semiring E] [Algebra Qb E]
    {f g : modularFunctionFieldBar M →ₐ[Qb] E}
    (h : ∀ (d : ℕ) [NeZero d], d ∣ M → ∀ x : modularFunctionFieldBar M,
      (x : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ d jq) → f x = g x) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qb (modularFunctionFieldBar_eq_adjoin M) ?_
  rintro _ ⟨x, ⟨d, hne, hd, rfl⟩, rfl⟩
  exact h d hd _ rfl

def jBar (M : ℕ) : modularFunctionFieldBar M :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (by
    simpa [qExpand_one_apply] using jqd_mem_full M (one_dvd _) (d := 1))⟩

@[scoped simp] theorem coe_jBar (M : ℕ) : ((jBar M : modularFunctionFieldBar M) : LaurentSeries Qb)
    = coeffEmb Qb jq := rfl

theorem coeffEmb_jq_coeff_neg_one : (coeffEmb Qb jq).coeff (-1) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

def ALSpec (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) : Prop :=
  ∀ (d : ℕ) [NeZero d], d ∣ N → ∀ x : modularFunctionFieldBar (N * ℓ),
    ((x : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ d jq) →
      ((w x : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)
        = qExpand Qb ℓ (coeffEmb Qb (qExpand ℚ d jq))) ∧
    ((x : LaurentSeries Qb) = qExpand Qb ℓ (coeffEmb Qb (qExpand ℚ d jq)) →
      ((w x : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)
        = coeffEmb Qb (qExpand ℚ d jq))

theorem exists_AL (hℓN : ¬ ℓ ∣ N) :
    ∃ w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ), ALSpec N ℓ w :=
  ModularCurve.exists_algEquiv_modularFunctionFieldBar_atkinLehner N ℓ Fact.out hℓN

variable {N ℓ}

theorem AL_beta {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (hw : ALSpec N ℓ w) (x : modularFunctionFieldBar N) :
    w (heckeBetaBar Qb N ℓ x) = heckeAlphaBar Qb N ℓ x := by
  have h : w.toAlgHom.comp (heckeBetaBar Qb N ℓ) = heckeAlphaBar Qb N ℓ := by
    refine algHom_ext_bar N fun d _ hd x hx => Subtype.ext ?_
    have h2 := (hw d hd (heckeBetaBar Qb N ℓ x)).2 (by rw [coe_heckeBetaBar, hx])
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, coe_heckeAlphaBar]
    rw [hx]; exact h2
  exact DFunLike.congr_fun h x

theorem AL_alpha {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (hw : ALSpec N ℓ w) (x : modularFunctionFieldBar N) :
    w (heckeAlphaBar Qb N ℓ x) = heckeBetaBar Qb N ℓ x := by
  have h : w.toAlgHom.comp (heckeAlphaBar Qb N ℓ) = heckeBetaBar Qb N ℓ := by
    refine algHom_ext_bar N fun d _ hd x hx => Subtype.ext ?_
    have h1 := (hw d hd (heckeAlphaBar Qb N ℓ x)).1 (by rw [coe_heckeAlphaBar, hx])
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, coe_heckeBetaBar]
    rw [hx]; exact h1
  exact DFunLike.congr_fun h x

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

theorem finrank_beta (hℓN : ¬ ℓ ∣ N) :
    Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) = ℓ + 1 := by
  have h := ModularCurve.finrankAlong_heckeBetaBar Qb N ℓ
  rw [if_neg hℓN] at h
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

def sigmaLast (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ))
    (hw : ALSpec N ℓ w) :
    modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ where
  toRingHom := (ιE ℓ).comp ((qExpand Qb ℓ).comp
    ((algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb)).comp
      w.toAlgHom.toRingHom))
  commutes' f := by
    show ιE ℓ (qExpand Qb ℓ ((w (heckeBetaBar Qb N ℓ f) : modularFunctionFieldBar (N * ℓ)) :
        LaurentSeries Qb)) = ιE ℓ ((heckeBetaBar Qb N ℓ f : modularFunctionFieldBar (N * ℓ)) :
        LaurentSeries Qb)
    rw [AL_beta hw, coe_heckeAlphaBar, coe_heckeBetaBar]

theorem sigmaLast_apply (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ))
    (hw : ALSpec N ℓ w) (v : modularFunctionFieldBar (N * ℓ)) :
    sigmaLast w hw v = ιE ℓ (qExpand Qb ℓ ((w v : modularFunctionFieldBar (N * ℓ)) :
      LaurentSeries Qb)) := rfl

def zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Qbˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem zu_pow {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

def emb {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w) :
    Option (Fin ℓ) → (modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ)
  | none => sigmaLast w hw
  | some j => sigmaTwist (zu hζ ^ (j : ℕ)) (zu_pow hζ j)

theorem w_jBar {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (hw : ALSpec N ℓ w) :
    ((w (jBar (N * ℓ)) : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)
      = qExpand Qb ℓ (coeffEmb Qb jq) := by
  have h : jBar (N * ℓ) = heckeAlphaBar Qb N ℓ (jBar N) := Subtype.ext (by
    rw [coe_heckeAlphaBar]; rfl)
  rw [h, AL_alpha hw, coe_heckeBetaBar, coe_jBar]

theorem emb_injective {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w) :
    Function.Injective (emb hζ w hw) := by
  have hprime : ℓ.Prime := Fact.out
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne ℓ)

  let cf : Option (Fin ℓ) → Qb := fun o => Option.elim o (0 : Qb) (fun j => (ζ ^ (j : ℕ))⁻¹)
  have key : ∀ o : Option (Fin ℓ), ∃ s : LaurentSeries Qb,
      emb hζ w hw o (jBar (N * ℓ)) = ιE ℓ s ∧ s.coeff (-1) = cf o := by
    rintro (_ | j)
    · refine ⟨qExpand Qb ℓ (qExpand Qb ℓ (coeffEmb Qb jq)), ?_, ?_⟩
      · show sigmaLast w hw (jBar (N * ℓ)) = _
        rw [sigmaLast_apply, w_jBar hw]
      · show (qExpand Qb ℓ (qExpand Qb ℓ (coeffEmb Qb jq))).coeff (-1) = 0
        refine qExpand_coeff_of_not_dvd ℓ _ fun h => ?_
        have h1 : (ℓ : ℤ) ∣ 1 := (dvd_neg).mp h
        have h2 : (ℓ : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
        exact hprime.one_lt.ne' (by exact_mod_cast h2)
    · refine ⟨twist (zu hζ ^ (j : ℕ)) (coeffEmb Qb jq), rfl, ?_⟩
      show (twist (zu hζ ^ (j : ℕ)) (coeffEmb Qb jq)).coeff (-1) = (ζ ^ (j : ℕ))⁻¹
      rw [twist_coeff, coeffEmb_jq_coeff_neg_one, mul_one, zpow_neg_one, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, zu, Units.val_mk0]
  intro o₁ o₂ h
  obtain ⟨s₁, hs₁, hc₁⟩ := key o₁
  obtain ⟨s₂, hs₂, hc₂⟩ := key o₂
  have hs : s₁ = s₂ := ιE_injective ℓ (by rw [← hs₁, ← hs₂, h])
  rw [hs] at hc₁
  have hc : cf o₁ = cf o₂ := hc₁.symm.trans hc₂
  rcases o₁ with _ | j₁ <;> rcases o₂ with _ | j₂
  · rfl
  · exact absurd hc.symm (inv_ne_zero (pow_ne_zero _ hz))
  · exact absurd hc (inv_ne_zero (pow_ne_zero _ hz))
  · have hv : ζ ^ (j₁ : ℕ) = ζ ^ (j₂ : ℕ) := inv_inj.mp hc
    exact congrArg some (Fin.ext (hζ.pow_inj j₁.2 j₂.2 hv))

theorem emb_bijective (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w) :
    Function.Bijective (emb hζ w hw) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective hζ w hw, ?_⟩
  rw [Fintype.card_option, Fintype.card_fin, AlgHom.card, finrank_beta N ℓ hℓN]

theorem qExpand_trace (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w)
    (v : modularFunctionFieldBar (N * ℓ)) :
    qExpand Qb ℓ ((Algebra.trace (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) v :
        modularFunctionFieldBar N) : LaurentSeries Qb)
      = rootSum (zu hζ) ℓ (v : LaurentSeries Qb)
        + qExpand Qb ℓ ((w v : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb) := by
  apply ιE_injective ℓ
  have h1 := trace_eq_sum_embeddings (EE ℓ) (K := modularFunctionFieldBar N)
    (L := modularFunctionFieldBar (N * ℓ)) (x := v)
  have h2 : algebraMap (modularFunctionFieldBar N) (EE ℓ)
      (Algebra.trace (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) v)
      = ιE ℓ (qExpand Qb ℓ ((Algebra.trace (modularFunctionFieldBar N)
          (modularFunctionFieldBar (N * ℓ)) v : modularFunctionFieldBar N) : LaurentSeries Qb)) := by
    show ιE ℓ ((heckeBetaBar Qb N ℓ _ : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb) = _
    rw [coe_heckeBetaBar]
  rw [← h2, h1, ← (emb_bijective hℓN hζ w hw).sum_comp (fun σ => σ v), Fintype.sum_option,
    map_add, rootSum_apply, map_sum, Finset.sum_range, add_comm]
  rfl

end Trace

section Assembly

local notation "Qb" => AlgebraicClosure ℚ

theorem coeff_C_mul {R : Type*} [CommRing R] (r : R) (x : LaurentSeries R) (n : ℤ) :
    (C r * x).coeff n = r * x.coeff n := by
  rw [C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

variable {N ℓ : ℕ} [NeZero N] [Fact ℓ.Prime]

attribute [local instance] algAlongBeta algBetaE isScalarTower_beta finiteDimensional_beta
  isSeparable_beta

local notation "FN" => modularFunctionFieldBar N
local notation "FNl" => modularFunctionFieldBar (N * ℓ)
local notation "β" => heckeBetaBar (AlgebraicClosure ℚ) N ℓ
local notation "α" => heckeAlphaBar (AlgebraicClosure ℚ) N ℓ

theorem heckeDiffBar_apply (x : Ω[FN⁄Qb]) :
    heckeDiffBar N ⟨ℓ, Fact.out⟩ x = traceAlong β (pullbackAlong α x) := rfl

theorem diffQExp_pullback_beta (η : Ω[FN⁄Qb]) :
    diffQExp FNl (pullbackAlong β η) = C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN η) :=
  diffQExp_pullbackAlong FN FNl β (qExpand Qb ℓ) ℓ (fun x => coe_heckeBetaBar N ℓ x)
    (fun y => qEuler_qExpand ℓ y) η

theorem diffQExp_pullback_w_beta
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} (hw : ALSpec N ℓ w)
    (η : Ω[FN⁄Qb]) :
    diffQExp FNl (pullbackAlong (w.toAlgHom.comp β) η) = diffQExp FN η := by
  rw [diffQExp_pullbackAlong FN FNl (w.toAlgHom.comp β) (RingHom.id _) 1 ?_ ?_ η, C_one, one_mul,
    RingHom.id_apply]
  · intro x
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, AL_beta hw, coe_heckeAlphaBar, RingHom.id_apply]
  · intro y
    rw [C_one, one_mul]
    rfl

theorem twist_fix {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) (z : LaurentSeries Qb) :
    twist (zu hζ ^ j) (C (ℓ : Qb) * qExpand Qb ℓ z) = C (ℓ : Qb) * qExpand Qb ℓ z := by
  rw [map_mul, twist_C, twist_qExpand_of_pow_eq_one _ ℓ (zu_pow hζ j)]

def MC {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ))
    (ξ : Ω[FNl⁄Qb]) : Prop :=
  ∀ v : FNl, C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (traceAlong β (v • ξ)))
    = rootSum (zu hζ) ℓ ((v : LaurentSeries Qb) * diffQExp FNl ξ)
      + C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FNl (pullbackAlong w.toAlgHom (v • ξ)))

theorem MC_base (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} (hw : ALSpec N ℓ w)
    (η : Ω[FN⁄Qb]) : MC hζ w (pullbackAlong β η) := by
  intro v
  rw [traceAlong_smul_pullbackAlong β (separableAlong_beta N ℓ) v η, diffQExp_smul, map_mul,
    qExpand_trace hℓN hζ w hw v, diffQExp_pullback_beta,
    rootSum_mul_of_fixed _ _ _ _ (fun j => twist_fix hζ j _), pullbackAlong_smul,
    pullbackAlong_pullbackAlong, diffQExp_smul, diffQExp_pullback_w_beta hw, map_mul,
    AlgEquiv.coe_algHom]
  ring

omit [NeZero N] in
theorem MC_smul {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (ξ : Ω[FNl⁄Qb]) (h : MC hζ w ξ) (u' : FNl) : MC hζ w (u' • ξ) := by
  intro v
  have e1 : v • (u' • ξ) = (v * u') • ξ := smul_smul v u' ξ
  have e2 : (v : LaurentSeries Qb) * diffQExp FNl (u' • ξ)
      = ((v * u' : FNl) : LaurentSeries Qb) * diffQExp FNl ξ := by
    rw [diffQExp_smul, ← mul_assoc]; rfl
  rw [e1, e2]
  exact h (v * u')

omit [NeZero N] in
theorem MC_add {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (ξ₁ ξ₂ : Ω[FNl⁄Qb]) (h₁ : MC hζ w ξ₁) (h₂ : MC hζ w ξ₂) : MC hζ w (ξ₁ + ξ₂) := by
  intro v
  simp only [smul_add, map_add, mul_add, rootSum_add]
  rw [h₁ v, h₂ v]
  ring

omit [NeZero N] in
theorem MC_zero {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} :
    MC hζ w 0 := by
  intro v
  simp only [smul_zero, map_zero, mul_zero, rootSum_zero, add_zero]

theorem MC_all (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} (hw : ALSpec N ℓ w)
    (ξ : Ω[FNl⁄Qb]) : MC hζ w ξ := by
  haveI : Algebra.FormallyEtale FN FNl := Algebra.FormallyEtale.of_isSeparable FN FNl
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale Qb FN FNl).surjective ξ
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact MC_zero hζ
  | tmul u' η =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    change MC hζ w (u' • pullbackAlong β η)
    exact MC_smul hζ _ (MC_base hℓN hζ hw η) u'
  | add x y hx hy => rw [map_add]; exact MC_add hζ _ _ hx hy

theorem key_identity (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} (hw : ALSpec N ℓ w)
    (ω : Ω[FN⁄Qb]) :
    C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (heckeDiffBar N ⟨ℓ, Fact.out⟩ ω))
      = rootSum (zu hζ) ℓ (diffQExp FN ω)
        + C (ℓ : Qb) * (C (ℓ : Qb) * qExpand Qb ℓ (qExpand Qb ℓ (diffQExp FN ω))) := by
  have key : ∀ ω : Ω[FN⁄Qb], ω ∈ Submodule.span FN (Set.range (D Qb FN)) → ∀ f : FN,
      C (ℓ : Qb) * qExpand Qb ℓ (diffQExp FN (heckeDiffBar N ⟨ℓ, Fact.out⟩ (f • ω)))
        = rootSum (zu hζ) ℓ (diffQExp FN (f • ω))
          + C (ℓ : Qb) * (C (ℓ : Qb) * qExpand Qb ℓ (qExpand Qb ℓ (diffQExp FN (f • ω)))) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem ω h =>
      obtain ⟨g, rfl⟩ := h
      intro f
      have hM := MC_all hℓN hζ hw (D Qb FNl (α g)) (α f)
      rw [heckeDiffBar_apply, pullbackAlong_smul, pullbackAlong_D, hM, diffQExp_D,
        pullbackAlong_smul, pullbackAlong_D, AlgEquiv.coe_algHom,
        AL_alpha hw, AL_alpha hw, diffQExp_smul_D, diffQExp_smul_D, coe_heckeAlphaBar,
        coe_heckeAlphaBar, coe_heckeBetaBar, coe_heckeBetaBar, qEuler_qExpand, map_mul, map_mul,
        map_mul, map_mul, qExpand_C]
      show _ = _ + C (ℓ : Qb) * (C (ℓ : Qb) *
        (qExpand Qb ℓ (qExpand Qb ℓ (f : LaurentSeries Qb))
          * qExpand Qb ℓ (qExpand Qb ℓ (qEuler Qb (g : LaurentSeries Qb)))))
      ring
    | zero => intro f; simp [rootSum_zero]
    | add x y _ _ hx hy =>
      intro f
      simp only [smul_add, map_add, mul_add, rootSum_add]
      rw [hx f, hy f]
      ring
    | smul a x _ hx => intro f; rw [smul_smul]; exact hx (f * a)
  simpa using key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial) 1

theorem coeff_identity (hℓN : ¬ ℓ ∣ N) (ω : Ω[FN⁄Qb]) (n : ℤ) :
    (diffQExp FN (heckeDiffBar N ⟨ℓ, Fact.out⟩ ω)).coeff n
      = (diffQExp FN ω).coeff (n * ℓ)
        + (ℓ : Qb) * (if (ℓ : ℤ) ∣ n then (diffQExp FN ω).coeff (n / ℓ) else 0) := by
  haveI : NeZero ((ℓ : ℕ) : Qb) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb ℓ
  obtain ⟨w, hw⟩ := exists_AL N ℓ hℓN
  have h := congrArg (fun s : LaurentSeries Qb => s.coeff ((ℓ : ℤ) * n)) (key_identity hℓN hζ hw ω)
  beta_reduce at h
  rw [coeff_C_mul, qExpand_coeff_mul, HahnSeries.coeff_add, coeff_C_mul, coeff_C_mul,
    qExpand_coeff_mul, zu, rootSum_coeff hζ, if_pos (dvd_mul_right _ _), ← mul_add] at h
  have hℓ0 : ((ℓ : ℕ) : Qb) ≠ 0 := NeZero.ne _
  have h' := mul_left_cancel₀ hℓ0 h
  rw [h', mul_comm (ℓ : ℤ) n]
  congr 2
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [qExpand_coeff_mul, Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne ℓ))]
  · exact qExpand_coeff_of_not_dvd ℓ _ hd

end Assembly

end W5MCotQExpHecke
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd.W5MCotQExpHecke"

open ModularCurve

theorem solution (N : ℕ) [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExpBar N (ModularCurve.heckeDiffBar N ⟨ℓ, Fact.out⟩ ω)).coeff n =
      (ModularCurve.diffQExpBar N ω).coeff (n * ℓ) +
        (ℓ : AlgebraicClosure ℚ) *
          (if (ℓ : ℤ) ∣ n then (ModularCurve.diffQExpBar N ω).coeff (n / ℓ) else 0) :=
  W5MCotQExpHecke.coeff_identity hℓN ω n

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd.W5MCotQExpHecke"

end S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_coeff_diffQExpBar_heckeDiffBar_of_not_dvd (solution)
