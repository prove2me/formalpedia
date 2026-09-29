-- Prove2me | solution 1 for ModularCurve.principal_le_closure_divisor_laurentIntegral_diamondAutHBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a8ea4361-ad35-56bb-ab84-c23939022329

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped MatrixGroups ModularForm Classical
open IntermediateField AlgebraicCurve ModularCurve

namespace PLCDSol

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

abbrev ι : LaurentSeries A →+* LaurentSeries L := coeffMap A.subtype

abbrev ϖ : LaurentSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
  coeffMap (IsLocalRing.residue A)

theorem ι_injective : Function.Injective (ι A) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact h1

theorem ι_eq_zero_iff (x : LaurentSeries A) : ι A x = 0 ↔ x = 0 := by
  rw [← map_zero (ι A)]; exact (ι_injective A).eq_iff

theorem ϖ_eq_zero_iff (y : LaurentSeries A) :
    ϖ A y = 0 ↔ ∀ n, y.coeff n ∈ IsLocalRing.maximalIdeal A := by
  constructor
  · intro h n
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    exact (IsLocalRing.residue_eq_zero_iff _).mp h1
  · intro h
    ext n
    simp only [coeffMap_coeff, HahnSeries.coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (h n)

theorem ι_C (a : A) : ι A (HahnSeries.C a) = algebraMap L (LaurentSeries L) (a : L) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]; rfl

theorem ϖ_C (a : A) : ϖ A (HahnSeries.C a) =
    algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
      (IsLocalRing.residue A a) := by
  rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

def intSeriesA (p : PowerSeries ℤ) : LaurentSeries A :=
  HahnSeries.ofPowerSeries ℤ A (p.map (Int.castRingHom A))

theorem coeffMap_intSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : PowerSeries ℤ) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R (p.map (Int.castRingHom R))) =
      HahnSeries.ofPowerSeries ℤ S (p.map (Int.castRingHom S)) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem algebraMap_eq_C {K : Type*} [Field K] (a : K) : algebraMap K (LaurentSeries K) a = HahnSeries.C a := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem ι_intSeriesA (p : PowerSeries ℤ) : ι A (intSeriesA A p) = intSeriesC L p :=
  coeffMap_intSeries _ p

theorem ϖ_intSeriesA (p : PowerSeries ℤ) :
    ϖ A (intSeriesA A p) = intSeriesC (IsLocalRing.ResidueField A) p :=
  coeffMap_intSeries _ p

theorem coeffEmb_intSeriesC [Algebra ℚ L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p :=
  coeffMap_intSeries _ p

theorem coeffEmb_algebraMap [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

theorem exists_inv_mem_maximalIdeal {c : L} (hc : c ∉ A) :
    ∃ h : c⁻¹ ∈ A, (⟨c⁻¹, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
  have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
  refine ⟨hci, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  apply hc
  have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
    have := congrArg (fun a : A => (a : L)) u.inv_val
    simpa [hu] using this
  rw [mul_inv_eq_one₀ hc0] at h1
  rw [← h1]; exact SetLike.coe_mem _

theorem exists_mem_residue_ne_zero {e : L} {z a : LaurentSeries A} (hz : ϖ A z ≠ 0) (ha : ϖ A a ≠ 0)
    (h : algebraMap L (LaurentSeries L) e * ι A z = ι A a) :
    ∃ he : e ∈ A, IsLocalRing.residue A ⟨e, he⟩ ≠ 0 := by
  have heA : e ∈ A := by
    by_contra hc
    have he0 : e ≠ 0 := by rintro rfl; exact hc A.zero_mem
    obtain ⟨hci, hcm⟩ := exists_inv_mem_maximalIdeal A hc
    have hza : z = HahnSeries.C ⟨e⁻¹, hci⟩ * a := by
      apply ι_injective A
      rw [map_mul, ι_C, ← h, ← mul_assoc, ← map_mul]
      simp [inv_mul_cancel₀ he0]
    apply hz
    rw [ϖ_eq_zero_iff]
    intro n
    rw [hza, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hcm
  refine ⟨heA, fun h0 => ha ?_⟩
  have haz : a = HahnSeries.C ⟨e, heA⟩ * z := by
    apply ι_injective A
    rw [map_mul, ι_C, ← h]
  rw [haz, map_mul, ϖ_C, h0, map_zero, zero_mul]

def IsInt (f : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ f * ι A y = ι A x

end Coeff

section Scaling

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_coeffMap_subtype_eq (x : LaurentSeries L) (hx : ∀ n, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, ι A y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq, Subtype.ext_iff, ZeroMemClass.coe_zero]
  · ext n
    rfl

theorem valuation_le_of_mem_span (T : Finset L) (c : L) (hc : ∀ t ∈ T, A.valuation t ≤ A.valuation c)
    {x : L} (hx : x ∈ Submodule.span ℤ (T : Set L)) : A.valuation x ≤ A.valuation c := by
  induction hx using Submodule.span_induction with
  | mem x h => exact hc x h
  | zero => simp
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul m x _ hx =>
      rw [zsmul_eq_mul, map_mul]
      calc A.valuation (m : L) * A.valuation x ≤ 1 * A.valuation c :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr (intCast_mem A m)) hx
        _ = A.valuation c := one_mul _

theorem exists_primitive_scaling {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
    (hxM : ∀ n, x.coeff n ∈ M) :
    ∃ c : L, c ≠ 0 ∧ (∀ n, c⁻¹ * x.coeff n ∈ A) ∧ ∃ n₀, c⁻¹ * x.coeff n₀ = 1 := by
  set N' : Submodule ℤ L := Submodule.span ℤ (Set.range x.coeff) with hN'
  have hle : N' ≤ M := Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hxM n)
  have hfg : N'.FG := (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian M hM)) N' hle
  obtain ⟨T, hTsub, hTspan⟩ : ∃ T : Finset L, (↑T ⊆ Set.range x.coeff) ∧
      Submodule.span ℤ (T : Set L) = N' := by
    obtain ⟨S, hS⟩ := hfg
    have hmem : ∀ s ∈ S, ∃ T : Finset L, ↑T ⊆ Set.range x.coeff ∧
        s ∈ Submodule.span ℤ (T : Set L) := fun s hs =>
      Submodule.mem_span_finite_of_mem_span (by rw [← hN', ← hS]; exact Submodule.subset_span hs)
    choose! Tf hTf₁ hTf₂ using hmem
    refine ⟨S.biUnion Tf, ?_, le_antisymm ?_ ?_⟩
    · simp only [Finset.coe_biUnion, Set.iUnion_subset_iff]
      exact fun s hs => hTf₁ s hs
    · exact Submodule.span_le.mpr fun t ht => by
        obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp ht
        exact Submodule.subset_span (hTf₁ s hs hts)
    · rw [← hS]
      refine Submodule.span_le.mpr fun s hs => ?_
      have h := hTf₂ s hs
      exact Submodule.span_mono (by
        intro t ht
        exact Finset.mem_biUnion.mpr ⟨s, hs, ht⟩) h
  obtain ⟨n₁, hn₁⟩ : ∃ n, x.coeff n ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by ext n; simpa using h n)
  have hcoeffN' : ∀ n, x.coeff n ∈ Submodule.span ℤ (T : Set L) := fun n => by
    rw [hTspan]; exact Submodule.subset_span ⟨n, rfl⟩
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hn₁
    simpa using hcoeffN' n₁
  obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image T A.valuation hTne
  have hvx : ∀ n, A.valuation (x.coeff n) ≤ A.valuation c := fun n =>
    valuation_le_of_mem_span A T c hcmax (hcoeffN' n)
  have hc0 : c ≠ 0 := by
    intro hc
    have h := hvx n₁
    rw [hc, map_zero, le_zero_iff, map_eq_zero] at h
    exact hn₁ h
  obtain ⟨n₀, hn₀⟩ := hTsub hcT
  refine ⟨c, hc0, fun n => ?_, n₀, by rw [hn₀, inv_mul_cancel₀ hc0]⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hc' : A.valuation c ≠ 0 := by simpa using hc0
  rw [inv_mul_le_one₀ (zero_lt_iff.mpr hc')]
  exact hvx n

theorem exists_primitive_form {x : LaurentSeries L} (hx : x ≠ 0) (M : Submodule ℤ L) (hM : M.FG)
    (hxM : ∀ n, x.coeff n ∈ M) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧
      x = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  obtain ⟨c, hc0, hcA, n₀, hn₀⟩ := exists_primitive_scaling A hx M hM hxM
  have hcoeff : ∀ n, (algebraMap L (LaurentSeries L) c⁻¹ * x).coeff n = c⁻¹ * x.coeff n := fun n => by
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A (algebraMap L (LaurentSeries L) c⁻¹ * x) fun n => by
    rw [hcoeff]; exact hcA n
  refine ⟨c, hc0, y, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField A) => s.coeff n₀) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (y.coeff n₀ : L) = 1 := by
      have := congrArg (fun s : LaurentSeries L => s.coeff n₀) hy
      simp only [coeffMap_coeff, hcoeff] at this
      rw [← hn₀]; exact this
    have h3 : y.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  · rw [hy, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end Scaling

section Forms

open ModularForm UpperHalfPlane EisensteinSeries

def δZ : PowerSeries ℤ := PowerSeries.X * dedekindEtaUnit

def delta1Pow (W : ℕ) : ModularForm 𝒮ℒ (12 * (W : ℤ)) :=
  ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow W).mcast (by ring)

theorem qExpansion_delta1Pow (W : ℕ) :
    qExpansion 1 (delta1Pow W) = (δZ ^ W).map (Int.castRingHom ℂ) := by
  rw [delta1Pow, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    map_pow]
  congr 1
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

def e4cube1 : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

theorem qExpansion_e4cube1 : qExpansion 1 (e4cube1) = (eisenstein4 ^ 3).map (Int.castRingHom ℂ) := by
  rw [e4cube1, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    map_pow, isIntegralQExp_E4]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

def deltaW (W : ℕ) : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ)) :=
  restrictForm (Subgroup.map_le_range _ Γ) (delta1Pow W)

def e4cube : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) e4cube1

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem coe_deltaW (W : ℕ) : (deltaW Γ W : ℍ → ℂ) = delta1Pow W := rfl

theorem coe_e4cube : (e4cube Γ : ℍ → ℂ) = e4cube1 := rfl

theorem isIntegralQExp_deltaW (W : ℕ) : IsIntegralQExp (deltaW Γ W : ℍ → ℂ) (δZ ^ W) := by
  rw [IsIntegralQExp, coe_deltaW, qExpansion_delta1Pow]

theorem isIntegralQExp_e4cube : IsIntegralQExp (e4cube Γ : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, coe_e4cube, qExpansion_e4cube1]

theorem isIntegralQExp_delta : IsIntegralQExp (delta Γ : ℍ → ℂ) δZ :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem slash_deltaW (W : ℕ) (γ : SL(2, ℤ)) :
    (deltaW Γ W : ℍ → ℂ) ∣[(12 * (W : ℤ))] (γ : GL (Fin 2) ℝ) = deltaW Γ W := by
  rw [coe_deltaW]
  exact SlashInvariantForm.slash_action_eqn (delta1Pow W) _ ⟨γ, rfl⟩

theorem slash_e4cube (γ : SL(2, ℤ)) :
    (e4cube Γ : ℍ → ℂ) ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ) = e4cube Γ := by
  rw [coe_e4cube]
  exact SlashInvariantForm.slash_action_eqn e4cube1 _ ⟨γ, rfl⟩

theorem slash_delta (γ : SL(2, ℤ)) :
    (delta Γ : ℍ → ℂ) ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ) = delta Γ :=
  SlashInvariantForm.slash_action_eqn (CuspForm.discriminant : ModularForm 𝒮ℒ 12) _ ⟨γ, rfl⟩

theorem intSeriesC_pow (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (p ^ n) = intSeriesC K p ^ n := by
  simp [intSeriesC]

theorem intSeriesC_delta_ne_zero (K : Type*) [Field K] : intSeriesC K δZ ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  have h2 : (HahnSeries.ofPowerSeries ℤ K (δZ.map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, δZ,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem intSeriesC_deltaPow_ne_zero (K : Type*) [Field K] (W : ℕ) : intSeriesC K (δZ ^ W) ≠ 0 := by
  rw [intSeriesC_pow]; exact pow_ne_zero _ (intSeriesC_delta_ne_zero K)

theorem jqModC_mul_delta (K : Type*) [Field K] :
    jqModC K * intSeriesC K δZ = intSeriesC K (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, δZ, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_div (K : Type*) [Field K] :
    jqModC K = intSeriesC K (eisenstein4 ^ 3) / intSeriesC K δZ := by
  rw [eq_div_iff (intSeriesC_delta_ne_zero K), jqModC_mul_delta]

theorem intSeriesC_deltaPow_mul_inv (K : Type*) [Field K] (W : ℕ) :
    intSeriesC K (δZ ^ W) * (intSeriesC K (dedekindEtaUnitInv ^ W) * HahnSeries.single (-(W : ℤ)) (1 : K)) = 1 := by
  have hUV : intSeriesC K (dedekindEtaUnit ^ W) * intSeriesC K (dedekindEtaUnitInv ^ W) = 1 := by
    rw [← intSeriesC_mul, ← mul_pow, dedekindEtaUnit_mul_inv, one_pow, intSeriesC_one]
  have hX : intSeriesC K (PowerSeries.X ^ W) * HahnSeries.single (-(W : ℤ)) (1 : K) = 1 := by
    rw [intSeriesC_pow, intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow,
      HahnSeries.single_mul_single]
    simp
  calc intSeriesC K (δZ ^ W) * (intSeriesC K (dedekindEtaUnitInv ^ W) * HahnSeries.single (-(W : ℤ)) (1 : K))
      = (intSeriesC K (PowerSeries.X ^ W) * HahnSeries.single (-(W : ℤ)) (1 : K)) *
          (intSeriesC K (dedekindEtaUnit ^ W) * intSeriesC K (dedekindEtaUnitInv ^ W)) := by
        rw [δZ, mul_pow, intSeriesC_mul]; ring
    _ = 1 := by rw [hX, hUV, one_mul]

end Forms

section DeltaInv

variable {L : Type*} [Field L] (A : ValuationSubring L)

def deltaInvA (W : ℕ) : LaurentSeries A :=
  intSeriesA A (dedekindEtaUnitInv ^ W) * HahnSeries.single (-(W : ℤ)) 1

theorem ι_deltaInvA (W : ℕ) :
    ι A (deltaInvA A W) = intSeriesC L (dedekindEtaUnitInv ^ W) * HahnSeries.single (-(W : ℤ)) (1 : L) := by
  rw [deltaInvA, map_mul, ι_intSeriesA, coeffMap_single]; rfl

theorem ϖ_deltaInvA (W : ℕ) :
    ϖ A (deltaInvA A W) = intSeriesC (IsLocalRing.ResidueField A) (dedekindEtaUnitInv ^ W) *
      HahnSeries.single (-(W : ℤ)) (1 : IsLocalRing.ResidueField A) := by
  rw [deltaInvA, map_mul, ϖ_intSeriesA, coeffMap_single, map_one]

theorem intSeriesC_deltaPow_mul_ι_deltaInvA (W : ℕ) :
    intSeriesC L (δZ ^ W) * ι A (deltaInvA A W) = 1 := by
  rw [ι_deltaInvA]; exact intSeriesC_deltaPow_mul_inv L W

theorem ϖ_deltaInvA_ne_zero (W : ℕ) : ϖ A (deltaInvA A W) ≠ 0 := by
  intro h
  have := intSeriesC_deltaPow_mul_inv (IsLocalRing.ResidueField A) W
  rw [← ϖ_deltaInvA, h, mul_zero] at this
  exact zero_ne_one this

end DeltaInv

section Shaped

open ModularForm UpperHalfPlane

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (L : Type*) [Field L] [Algebra ℚ L]

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

def numSet (W : ℕ) : Set (LaurentSeries L) :=
  {v | ∃ (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ),
    IsIntegralQExp h p ∧ v = intSeriesC L p}

def formGens : Set (LaurentSeries L) :=
  {u | ∃ (W : ℕ) (v : LaurentSeries L), v ∈ numSet Γ L W ∧ u = v / intSeriesC L (δZ ^ W)}

def FormShaped (W : ℕ) (x : LaurentSeries L) : Prop :=
  x * intSeriesC L (δZ ^ W) ∈ Submodule.span L (numSet Γ L W)

variable {Γ L}

theorem intSeriesC_mem_numSet {W : ℕ} {h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp h p) : intSeriesC L p ∈ numSet Γ L W :=
  ⟨h, p, hp, rfl⟩

theorem deltaPow_mem_numSet (W : ℕ) : intSeriesC L (δZ ^ W) ∈ numSet Γ L W :=
  intSeriesC_mem_numSet (isIntegralQExp_deltaW Γ W)

section FI

variable [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

include hT in

theorem numSet_mul {W W' : ℕ} {v v' : LaurentSeries L} (hv : v ∈ numSet Γ L W) (hv' : v' ∈ numSet Γ L W') :
    v * v' ∈ numSet Γ L (W + W') := by
  obtain ⟨h, p, hp, rfl⟩ := hv
  obtain ⟨h', p', hp', rfl⟩ := hv'
  refine ⟨(h.mul h').mcast (by push_cast; ring), p * p', ?_, (intSeriesC_mul L p p').symm⟩
  rw [IsIntegralQExp, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods hT),
    map_mul, hp, hp']

include hT in

theorem span_numSet_mul_mem {W W' : ℕ} {P v' : LaurentSeries L} (hP : P ∈ Submodule.span L (numSet Γ L W))
    (hv' : v' ∈ numSet Γ L W') : P * v' ∈ Submodule.span L (numSet Γ L (W + W')) := by
  induction hP using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (numSet_mul hT hv hv')
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [← HahnSeries.C_mul_eq_smul, mul_assoc, HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ _ hx

include hT in

theorem span_numSet_mul_span {W W' : ℕ} {P Q : LaurentSeries L} (hP : P ∈ Submodule.span L (numSet Γ L W))
    (hQ : Q ∈ Submodule.span L (numSet Γ L W')) : P * Q ∈ Submodule.span L (numSet Γ L (W + W')) := by
  induction hQ using Submodule.span_induction with
  | mem v hv => exact span_numSet_mul_mem hT hP hv
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [← HahnSeries.C_mul_eq_smul, mul_left_comm, HahnSeries.C_mul_eq_smul]
      exact Submodule.smul_mem _ _ hx

include hT in
theorem formShaped_mono {W : ℕ} (W' : ℕ) {x : LaurentSeries L} (hx : FormShaped Γ L W x) :
    FormShaped Γ L (W + W') x := by
  unfold FormShaped at hx ⊢
  rw [pow_add, intSeriesC_mul, ← mul_assoc]
  exact span_numSet_mul_mem hT hx (deltaPow_mem_numSet W')

include hT in
theorem formShaped_add {W W' : ℕ} {x y : LaurentSeries L} (hx : FormShaped Γ L W x) (hy : FormShaped Γ L W' y) :
    FormShaped Γ L (W + W') (x + y) := by
  have hx' := formShaped_mono hT W' hx
  have hy' := formShaped_mono hT W hy
  rw [add_comm W' W] at hy'
  unfold FormShaped at hx' hy' ⊢
  rw [add_mul]
  exact Submodule.add_mem _ hx' hy'

include hT in
theorem formShaped_mul {W W' : ℕ} {x y : LaurentSeries L} (hx : FormShaped Γ L W x) (hy : FormShaped Γ L W' y) :
    FormShaped Γ L (W + W') (x * y) := by
  unfold FormShaped at hx hy ⊢
  have heq : x * y * intSeriesC L (δZ ^ (W + W')) = x * intSeriesC L (δZ ^ W) * (y * intSeriesC L (δZ ^ W')) := by
    rw [pow_add, intSeriesC_mul]; ring
  rw [heq]
  exact span_numSet_mul_span hT hx hy

theorem formShaped_algebraMap (a : L) : FormShaped Γ L 0 (algebraMap L (LaurentSeries L) a) := by
  unfold FormShaped
  rw [pow_zero, intSeriesC_one, algebraMap_eq_C, HahnSeries.C_mul_eq_smul]
  have h1 : (1 : LaurentSeries L) ∈ numSet Γ L 0 := by
    refine ⟨(1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0).mcast (by simp), 1, ?_, by simp⟩
    show IsIntegralQExp (⇑(1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) 1
    rw [ModularForm.one_coe_eq_one]
    exact isIntegralQExp_one
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem formShaped_gen {u : LaurentSeries L} (hu : u ∈ formGens Γ L) : ∃ W, FormShaped Γ L W u := by
  obtain ⟨W, v, hv, rfl⟩ := hu
  refine ⟨W, ?_⟩
  unfold FormShaped
  rw [div_mul_cancel₀ _ (intSeriesC_deltaPow_ne_zero L W)]
  exact Submodule.subset_span hv

include hT in

theorem exists_formShaped_of_mem_adjoin {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (formGens Γ L)) :
    ∃ W, FormShaped Γ L W x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact formShaped_gen hx
  | algebraMap a => exact ⟨0, formShaped_algebraMap a⟩
  | add x y _ _ hx hy =>
      obtain ⟨W, hW⟩ := hx
      obtain ⟨W', hW'⟩ := hy
      exact ⟨W + W', formShaped_add hT hW hW'⟩
  | mul x y _ _ hx hy =>
      obtain ⟨W, hW⟩ := hx
      obtain ⟨W', hW'⟩ := hy
      exact ⟨W + W', formShaped_mul hT hW hW'⟩

theorem div_deltaPow_mem {W : ℕ} {h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))}
    {p : PowerSeries ℤ} (hp : IsIntegralQExp h p) :
    intSeriesC L p / intSeriesC L (δZ ^ W) ∈ FF := by
  have hmem := coeffEmb_mem_laurentBaseChange L
    (div_mem_qExpFunctionFieldC h (deltaW Γ W) hp (isIntegralQExp_deltaW Γ W) (intSeriesC_deltaPow_ne_zero ℚ W))
  rwa [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC] at hmem

theorem formGens_subset : formGens Γ L ⊆ (FF : Set (LaurentSeries L)) := by
  rintro _ ⟨W, v, ⟨h, p, hp, rfl⟩, rfl⟩
  exact div_deltaPow_mem hp

theorem adjoin_formGens_le : adjoin L (formGens Γ L) ≤ FF :=
  adjoin_le_iff.mpr formGens_subset

theorem algebra_adjoin_formGens_le {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (formGens Γ L)) : x ∈ FF :=
  adjoin_formGens_le (algebra_adjoin_le_adjoin L _ hx)

include hT in

theorem exists_formGens_div_of_mem_intFormRatiosC {x : LaurentSeries ℚ} (hx : x ∈ intFormRatiosC ℚ Γ) :
    ∃ u u' : LaurentSeries L, u ∈ formGens Γ L ∧ u' ∈ formGens Γ L ∧ u' ≠ 0 ∧ coeffEmb L x = u / u' := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx

  have hk : 0 ≤ k := by
    by_contra hk
    push Not at hk
    have hg' : g = 0 := ModularForm.isZero_of_neg_weight hk g
    apply hg0
    have hpg : pg = 0 := by
      have h := hg
      rw [hg', IsIntegralQExp, ModularForm.coe_zero, qExpansion_zero] at h
      ext n
      have := congrArg (PowerSeries.coeff n) h
      simpa using this
    rw [hpg, intSeriesC_zero]
  obtain ⟨w, rfl⟩ : ∃ w : ℕ, k = w := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  have hper := one_mem_strictPeriods hT
  have hG : IsIntegralQExp (((g.pow 12).mcast (by ring) :
      ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (w : ℤ))) : ℍ → ℂ) (pg ^ 12) := by
    rw [IsIntegralQExp, ModularForm.qExpansion_mcast, map_pow, hg, ModularForm.qExpansion_pow one_pos hper]
  have hF : IsIntegralQExp (((f.mul (g.pow 11)).mcast (by ring) :
      ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (w : ℤ))) : ℍ → ℂ) (pf * pg ^ 11) := by
    rw [IsIntegralQExp, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos hper, map_mul,
      map_pow, hf, hg, ModularForm.qExpansion_pow one_pos hper]
  have hg0L : intSeriesC L pg ≠ 0 := by
    intro h0
    apply hg0
    have h1 : coeffEmb L (intSeriesC ℚ pg) = 0 := by rw [coeffEmb_intSeriesC, h0]
    have hinj : Function.Injective (coeffEmb L : LaurentSeries ℚ → LaurentSeries L) := (coeffEmb L).injective
    exact hinj (h1.trans (map_zero _).symm)
  refine ⟨intSeriesC L (pf * pg ^ 11) / intSeriesC L (δZ ^ w), intSeriesC L (pg ^ 12) / intSeriesC L (δZ ^ w),
    ⟨w, _, intSeriesC_mem_numSet hF, rfl⟩, ⟨w, _, intSeriesC_mem_numSet hG, rfl⟩,
    div_ne_zero (by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0L) (intSeriesC_deltaPow_ne_zero L w), ?_⟩
  rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, div_div_div_cancel_right₀ (intSeriesC_deltaPow_ne_zero L w),
    intSeriesC_mul, intSeriesC_pow, intSeriesC_pow, div_eq_div_iff hg0L (pow_ne_zero _ hg0L)]
  ring

include hT in

theorem laurentBaseChange_le_adjoin_formGens : FF ≤ adjoin L (formGens Γ L) := by
  change adjoin L _ ≤ adjoin L (formGens Γ L)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) := hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    change coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) ∈ adjoin L (formGens Γ L)
    rw [coeffEmb_algebraMap]
    exact (adjoin L (formGens Γ L)).algebraMap_mem _
  · obtain ⟨u, u', hu, hu', -, h⟩ := exists_formGens_div_of_mem_intFormRatiosC (L := L) hT hz
    change coeffEmb L z ∈ adjoin L (formGens Γ L)
    rw [h]
    exact div_mem (IntermediateField.subset_adjoin L _ hu) (IntermediateField.subset_adjoin L _ hu')

end FI

variable (L) in

def intSet : Set (LaurentSeries L) := Set.range (intSeriesC L)

theorem numSet_subset_intSet (W : ℕ) : numSet Γ L W ⊆ intSet L := by
  rintro _ ⟨h, p, hp, rfl⟩; exact ⟨p, rfl⟩

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Submodule.span L (intSet L)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rcases le_or_gt 0 n with hn | hn
      · lift n to ℕ using hn
        rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, ← zsmul_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rw [intSeriesC, ofPowerSeries_coeff_of_neg _ hn]
        exact Submodule.zero_mem _
  | zero => exact ⟨⊥, Submodule.fg_bot, fun n => by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | smul a x _ hx =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      refine ⟨M₁.map (LinearMap.mulLeft ℤ a), hM₁.map _, fun n => ?_⟩
      rw [HahnSeries.coeff_smul, smul_eq_mul]
      exact ⟨x.coeff n, h₁ n, rfl⟩

end Shaped

section PrimShaped

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

theorem exists_primitive_of_intShaped {W : ℕ} {x : LaurentSeries L} (hx0 : x ≠ 0)
    (hx : x * intSeriesC L (δZ ^ W) ∈ Submodule.span L (intSet L)) :
    ∃ c : L, c ≠ 0 ∧ ∃ y : LaurentSeries A, ϖ A y ≠ 0 ∧ x = algebraMap L (LaurentSeries L) c * ι A y := by
  obtain ⟨M, hM, hPM⟩ := exists_fg_coeff_mem hx
  have hP0 : x * intSeriesC L (δZ ^ W) ≠ 0 := mul_ne_zero hx0 (intSeriesC_deltaPow_ne_zero L W)
  obtain ⟨c, hc0, P₀, hP₀, hP⟩ := exists_primitive_form A hP0 M hM hPM
  refine ⟨c, hc0, P₀ * deltaInvA A W, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hP₀ (ϖ_deltaInvA_ne_zero A W)
  · calc x = x * intSeriesC L (δZ ^ W) * ι A (deltaInvA A W) := by
            rw [mul_assoc, intSeriesC_deltaPow_mul_ι_deltaInvA, mul_one]
      _ = algebraMap L (LaurentSeries L) c * ι A (P₀ * deltaInvA A W) := by
            rw [hP, map_mul, mul_assoc]

end PrimShaped

section Engine

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have h := v.ord_coe_unit (Units.map (algebraMap K v.toValuationSubring).toMonoidHom (Units.mk0 a ha))
  simpa using h

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

def genElt {W : ℕ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
    (hp : IsIntegralQExp h p) : FF :=
  ⟨coeffEmb L (intSeriesC ℚ p / intSeriesC ℚ (δZ ^ W)),
    coeffEmb_mem_laurentBaseChange L
      (div_mem_qExpFunctionFieldC h (deltaW Γ W) hp (isIntegralQExp_deltaW Γ W) (intSeriesC_deltaPow_ne_zero ℚ W))⟩

theorem coe_genElt {W : ℕ} (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
    (hp : IsIntegralQExp h p) :
    ((genElt Γ h p hp : FF) : LaurentSeries L) = intSeriesC L p / intSeriesC L (δZ ^ W) := by
  change coeffEmb L (intSeriesC ℚ p / intSeriesC ℚ (δZ ^ W)) = _
  rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

theorem intShaped_image (σ : FF ≃ₐ[L] FF)
    (hσgen : ∀ (W : ℕ) (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
      (hp : IsIntegralQExp h p), ∃ (c : L) (p₁ : PowerSeries ℤ),
        ((σ (genElt Γ h p hp) : FF) : LaurentSeries L) =
          algebraMap L (LaurentSeries L) c * intSeriesC L p₁ / intSeriesC L (δZ ^ W))
    {W : ℕ} {x : LaurentSeries L} (hx : FormShaped Γ L W x) (hxF : x ∈ FF) :
    ((σ ⟨x, hxF⟩ : FF) : LaurentSeries L) * intSeriesC L (δZ ^ W) ∈ Submodule.span L (intSet L) := by
  unfold FormShaped at hx
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.mp hx
  have hg : ∀ i, ∃ (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ),
      IsIntegralQExp h p ∧ ((g i : LaurentSeries L)) = intSeriesC L p := fun i => (g i).2
  choose h p hp hgp using hg
  have hδ0 := intSeriesC_deltaPow_ne_zero L W

  have hxeq : (⟨x, hxF⟩ : FF) = ∑ i, algebraMap L FF (a i) * genElt Γ (h i) (p i) (hp i) := by
    apply Subtype.ext
    rw [IntermediateField.coe_sum]
    simp only [IntermediateField.coe_mul, coe_genElt]
    change x = ∑ i, algebraMap L (LaurentSeries L) (a i) * (intSeriesC L (p i) / intSeriesC L (δZ ^ W))
    simp only [← mul_div_assoc]
    rw [eq_comm, ← Finset.sum_div, div_eq_iff hδ0, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgp i, algebraMap_eq_C, HahnSeries.C_mul_eq_smul]
  choose c p₁ hcp using fun i => hσgen W (h i) (p i) (hp i)
  rw [hxeq, map_sum]
  simp only [map_mul, AlgEquiv.commutes, IntermediateField.coe_sum, IntermediateField.coe_mul, hcp]
  rw [Finset.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : ((algebraMap L FF (a i) : FF) : LaurentSeries L) *
      (algebraMap L (LaurentSeries L) (c i) * intSeriesC L (p₁ i) / intSeriesC L (δZ ^ W)) * intSeriesC L (δZ ^ W) =
      (a i * c i) • intSeriesC L (p₁ i) := by
    change algebraMap L (LaurentSeries L) (a i) * _ * _ = _
    rw [mul_assoc, div_mul_cancel₀ _ hδ0, ← mul_assoc, ← map_mul, algebraMap_eq_C, HahnSeries.C_mul_eq_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p₁ i, rfl⟩)

def genSet (σ : FF ≃ₐ[L] FF) : Set (Divisor L FF) :=
  {D | ∃ (y u : LaurentSeries A) (hy : ι A y ∈ FF),
      ι A u = ((σ ⟨ι A y, hy⟩ : FF) : LaurentSeries L) ∧
      ϖ A y ∈ Fb ∧ ϖ A y ≠ 0 ∧ ϖ A u ∈ Fb ∧ ϖ A u ≠ 0 ∧
      ∀ P, D P = P.ord (⟨ι A y, hy⟩ : FF)}

include hT in

theorem exists_mem_genSet [HasPrincipalDivisors L FF] (σ : FF ≃ₐ[L] FF)
    (hres : ∀ y : LaurentSeries A, ι A y ∈ FF → ϖ A y ∈ Fb)
    (hσint : ∀ f : FF, IsInt A ((σ f : FF) : LaurentSeries L) ↔ IsInt A (f : LaurentSeries L))
    (hσgen : ∀ (W : ℕ) (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
      (hp : IsIntegralQExp h p), ∃ (c : L) (p₁ : PowerSeries ℤ),
        ((σ (genElt Γ h p hp) : FF) : LaurentSeries L) =
          algebraMap L (LaurentSeries L) c * intSeriesC L p₁ / intSeriesC L (δZ ^ W))
    {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (formGens Γ L)) (hx0 : x ≠ 0) :
    ∃ D₀ ∈ genSet A Γ σ, ∀ v : Place L FF, D₀ v = v.ord (⟨x, algebra_adjoin_formGens_le hx⟩ : FF) := by
  have hxF : x ∈ FF := algebra_adjoin_formGens_le hx
  obtain ⟨W, hW⟩ := exists_formShaped_of_mem_adjoin hT hx

  have hWint : x * intSeriesC L (δZ ^ W) ∈ Submodule.span L (intSet L) :=
    Submodule.span_mono (numSet_subset_intSet W) hW
  obtain ⟨c, hc0, y, hy0, hxy⟩ := exists_primitive_of_intShaped A hx0 hWint
  have hιy : ι A y = algebraMap L (LaurentSeries L) c⁻¹ * x := by
    rw [hxy, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hyF : ι A y ∈ FF := by
    rw [hιy]; exact mul_mem ((laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).algebraMap_mem _) hxF
  set fy : FF := ⟨ι A y, hyF⟩ with hfy
  have hfy_eq : fy = algebraMap L FF c⁻¹ * (⟨x, hxF⟩ : FF) := Subtype.ext hιy
  have hιy0 : ι A y ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero A hy0
  have hfy0 : fy ≠ 0 := fun h => hιy0 (congrArg Subtype.val h)

  have hσx0 : ((σ ⟨x, hxF⟩ : FF) : LaurentSeries L) ≠ 0 := by
    intro h0
    have h1 : σ ⟨x, hxF⟩ = 0 := Subtype.ext h0
    rw [map_eq_zero_iff σ σ.injective] at h1
    exact hx0 (congrArg Subtype.val h1)
  obtain ⟨c', hc'0, y', hy'0, hσx⟩ :=
    exists_primitive_of_intShaped A hσx0 (intShaped_image Γ σ hσgen hW hxF)
  have hσfy : ((σ fy : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) (c⁻¹ * c') * ι A y' := by
    rw [hfy_eq, map_mul, AlgEquiv.commutes, IntermediateField.coe_mul, hσx, ← mul_assoc]
    change algebraMap L (LaurentSeries L) c⁻¹ * _ * _ = _
    rw [← map_mul]

  have hint : IsInt A ((σ fy : FF) : LaurentSeries L) :=
    (hσint fy).mpr ⟨y, 1, by simp, by simp [hfy]⟩
  have hint' : IsInt A ((σ fy⁻¹ : FF) : LaurentSeries L) := by
    refine (hσint fy⁻¹).mpr ⟨1, y, hy0, ?_⟩
    rw [IntermediateField.coe_inv, hfy, map_one]
    exact inv_mul_cancel₀ hιy0
  obtain ⟨a, b, hb0, hab⟩ := hint
  obtain ⟨a', b', hb'0, ha'b'⟩ := hint'
  rw [map_inv₀, IntermediateField.coe_inv] at ha'b'
  have hσfy0 : ((σ fy : FF) : LaurentSeries L) ≠ 0 := by
    intro h0
    have h1 : σ fy = 0 := Subtype.ext h0
    rw [map_eq_zero_iff σ σ.injective] at h1
    exact hfy0 h1
  have ha0 : ϖ A a ≠ 0 := by
    have hcross : b * b' = a * a' := by
      apply ι_injective A
      rw [map_mul, map_mul, ← hab, ← ha'b']
      field_simp
    intro h0
    have := congrArg (ϖ A) hcross
    rw [map_mul, map_mul, h0, zero_mul] at this
    exact mul_ne_zero hb0 hb'0 this

  have hkey : algebraMap L (LaurentSeries L) (c⁻¹ * c') * ι A (y' * b) = ι A a := by
    rw [map_mul (ι A), ← mul_assoc, ← hσfy, hab]
  obtain ⟨he, he0⟩ := exists_mem_residue_ne_zero A (by rw [map_mul]; exact mul_ne_zero hy'0 hb0) ha0 hkey
  set u : LaurentSeries A := HahnSeries.C ⟨c⁻¹ * c', he⟩ * y' with hu
  have hιu : ι A u = ((σ fy : FF) : LaurentSeries L) := by
    rw [hu, map_mul, ι_C, hσfy]
  have hu0 : ϖ A u ≠ 0 := by
    rw [hu, map_mul, ϖ_C]
    exact mul_ne_zero (by rwa [Ne, map_eq_zero]) hy'0
  have huF : ι A u ∈ FF := by rw [hιu]; exact (σ fy).2

  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) fy hfy0
  refine ⟨D₀, ⟨y, u, hyF, hιu, hres y hyF, hy0, hres u huF, hu0, hD₀⟩, fun v => ?_⟩
  rw [hD₀ v, hfy_eq]
  have hxne : (⟨x, hxF⟩ : FF) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hcne : algebraMap L FF c⁻¹ ≠ 0 := (_root_.map_ne_zero _).mpr (inv_ne_zero hc0)
  rw [v.ord_mul hcne hxne, ord_algebraMap_eq_zero v (inv_ne_zero hc0), zero_add]

include hT in

theorem principal_le_closure_genSet [HasPrincipalDivisors L FF] (σ : FF ≃ₐ[L] FF)
    (hres : ∀ y : LaurentSeries A, ι A y ∈ FF → ϖ A y ∈ Fb)
    (hσint : ∀ f : FF, IsInt A ((σ f : FF) : LaurentSeries L) ↔ IsInt A (f : LaurentSeries L))
    (hσgen : ∀ (W : ℕ) (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
      (hp : IsIntegralQExp h p), ∃ (c : L) (p₁ : PowerSeries ℤ),
        ((σ (genElt Γ h p hp) : FF) : LaurentSeries L) =
          algebraMap L (LaurentSeries L) c * intSeriesC L p₁ / intSeriesC L (δZ ^ W)) :
    Divisor.principal (K := L) (F := FF) ≤ AddSubgroup.closure (genSet A Γ σ) := by
  intro D hD
  obtain ⟨f, hf0, hDf⟩ := Divisor.mem_principal.mp hD
  have hfF : (f : LaurentSeries L) ∈ adjoin L (formGens Γ L) := laurentBaseChange_le_adjoin_formGens hT f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Dr, hDr, hDr'⟩ := exists_mem_genSet A Γ hT σ hres hσint hσgen hr hr0
  obtain ⟨Ds, hDs, hDs'⟩ := exists_mem_genSet A Γ hT σ hres hσint hσgen hs hs0
  have hrF : r ∈ FF := algebra_adjoin_formGens_le hr
  have hsF : s ∈ FF := algebra_adjoin_formGens_le hs
  have hfeq : f = (⟨r, hrF⟩ : FF) * (⟨s, hsF⟩ : FF)⁻¹ := by
    apply Subtype.ext
    rw [hrs, div_eq_mul_inv]
    rfl
  have hrne : (⟨r, hrF⟩ : FF) ≠ 0 := fun h => hr0 (congrArg Subtype.val h)
  have hsne : (⟨s, hsF⟩ : FF)⁻¹ ≠ 0 := inv_ne_zero fun h => hs0 (congrArg Subtype.val h)
  have hDeq : D = Dr - Ds := by
    ext v
    rw [Finsupp.sub_apply, hDf v, hDr' v, hDs' v, hfeq, v.ord_mul hrne hsne, v.ord_inv]
    ring
  rw [hDeq]
  exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure hDr) (AddSubgroup.subset_closure hDs)

def fixedIF {E : Type*} [Field E] [Algebra L E] (τ : E ≃ₐ[L] E) : IntermediateField L E where
  carrier := {e | τ e = e}
  mul_mem' {a b} ha hb := by
    change τ (a * b) = a * b
    rw [map_mul, show τ a = a from ha, show τ b = b from hb]
  one_mem' := map_one τ
  add_mem' {a b} ha hb := by
    change τ (a + b) = a + b
    rw [map_add, show τ a = a from ha, show τ b = b from hb]
  zero_mem' := map_zero τ
  algebraMap_mem' r := τ.commutes r
  inv_mem' a ha := by
    change τ a⁻¹ = a⁻¹
    rw [map_inv₀, show τ a = a from ha]

theorem apply_eq_self_of_mem_adjoin {E : Type*} [Field E] [Algebra L E] (τ : E ≃ₐ[L] E) {x : E}
    (hx : τ x = x) {e : E} (he : e ∈ IntermediateField.adjoin L ({x} : Set E)) : τ e = e := by
  have hle : IntermediateField.adjoin L ({x} : Set E) ≤ fixedIF τ :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  exact hle he

end Engine

section Modular

open ModularForm UpperHalfPlane

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "ΓH" => CohCarrier.GammaH M H

scoped instance instFiniteIndexGammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem exists_gamma0_apply_eq (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨γ.1, γ.2, ?_⟩
  have h : ((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) = d := by rw [hγ, inv_inv]
  have h2 : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = ((γ.1 0 0 : ℤ) : ZMod M) := rfl
  rw [← h2, h]

theorem coeffMap_ratComplex_injective :
    Function.Injective (coeffMap (algebraMap ℚ ℂ) : LaurentSeries ℚ → LaurentSeries ℂ) :=
  (coeffMap (algebraMap ℚ ℂ)).injective

theorem coeffMap_ratComplex_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = HahnSeries.ofPowerSeries ℤ ℂ (p.map (Int.castRingHom ℂ)) :=
  coeffMap_intSeries _ p

theorem coeffMap_ratComplex_algebraMap (c : ℚ) :
    coeffMap (algebraMap ℚ ℂ) (algebraMap ℚ (LaurentSeries ℚ) c) = HahnSeries.C (c : ℂ) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, HahnSeries.C_apply]
  rfl

theorem T_mem_Gamma1 : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [← GammaH_bot M]; exact translation_mem_GammaH M ⊥

theorem diamond_genElt (hin : HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ)
    (W : ℕ) (h : ModularForm (ΓH : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
    (hp : IsIntegralQExp h p) :
    ∃ (c : Qb) (p₁ : PowerSeries ℤ),
      ((diamondAutHBar M H d (genElt (L := Qb) ΓH h p hp) : xHFunctionFieldBar M H) : LaurentSeries Qb) =
        algebraMap Qb (LaurentSeries Qb) c * intSeriesC Qb p₁ / intSeriesC Qb (δZ ^ W) := by
  obtain ⟨γ, hγ0, hγd⟩ := exists_gamma0_apply_eq M d
  have hdia := hin.isDiamondAutHBar d
  obtain ⟨y, -, hσy, hyq⟩ := hdia (12 * (W : ℤ)) h (deltaW ΓH W) p (δZ ^ W) hp (isIntegralQExp_deltaW ΓH W)
    (intSeriesC_deltaPow_ne_zero ℚ W) γ hγ0 hγd

  rw [slash_deltaW ΓH W γ, ← (isIntegralQExp_deltaW ΓH W)] at hyq

  have h1H : ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      (ΓH : Subgroup (GL (Fin 2) ℝ)) := Subgroup.map_mono (Gamma1_le_GammaH M H)
  obtain ⟨D, f₁, p₁, hD0, hf₁p₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M (restrictForm h1H h) (p := p) hp γ hγ0
  have hD0' : (D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD0
  have hfun : ((h : ℍ → ℂ) ∣[(12 * (W : ℤ))] (γ : GL (Fin 2) ℝ)) = (D : ℂ)⁻¹ • (f₁ : ℍ → ℂ) := by
    rw [hf₁, smul_smul, inv_mul_cancel₀ hD0', one_smul]
    rfl
  have hper1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    one_mem_strictPeriods (T_mem_Gamma1 M)
  have hq : qExpansion 1 ((h : ℍ → ℂ) ∣[(12 * (W : ℤ))] (γ : GL (Fin 2) ℝ)) =
      (D : ℂ)⁻¹ • p₁.map (Int.castRingHom ℂ) := by
    rw [hfun, ModularForm.qExpansion_smul one_pos hper1, ← hf₁p₁]
  rw [hq] at hyq

  have hyeq : y * intSeriesC ℚ (δZ ^ W) = algebraMap ℚ (LaurentSeries ℚ) (D : ℚ)⁻¹ * intSeriesC ℚ p₁ := by
    apply coeffMap_ratComplex_injective
    rw [map_mul, map_mul, coeffMap_ratComplex_intSeriesC, coeffMap_ratComplex_intSeriesC,
      coeffMap_ratComplex_algebraMap, hyq, PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C]
    push_cast
    rfl
  have hy : y = algebraMap ℚ (LaurentSeries ℚ) (D : ℚ)⁻¹ * intSeriesC ℚ p₁ / intSeriesC ℚ (δZ ^ W) := by
    rw [eq_div_iff (intSeriesC_deltaPow_ne_zero ℚ W), hyeq]
  refine ⟨algebraMap ℚ Qb (D : ℚ)⁻¹, p₁, ?_⟩
  refine hσy.trans ?_
  rw [hy, map_div₀, map_mul, coeffEmb_intSeriesC, coeffEmb_intSeriesC, coeffEmb_algebraMap]

theorem diamond_j (hin : HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ)
    (hjF : coeffEmb Qb (jqModC ℚ) ∈ xHFunctionFieldBar M H) :
    diamondAutHBar M H d ⟨coeffEmb Qb (jqModC ℚ), hjF⟩ = ⟨coeffEmb Qb (jqModC ℚ), hjF⟩ := by
  obtain ⟨γ, hγ0, hγd⟩ := exists_gamma0_apply_eq M d
  have hdia := hin.isDiamondAutHBar d
  obtain ⟨y, -, hσy, hyq⟩ := hdia 12 (e4cube ΓH) (delta ΓH) (eisenstein4 ^ 3) δZ (isIntegralQExp_e4cube ΓH)
    (isIntegralQExp_delta ΓH) (intSeriesC_delta_ne_zero ℚ) γ hγ0 hγd
  rw [slash_delta ΓH γ, slash_e4cube ΓH γ, ← isIntegralQExp_delta ΓH, ← isIntegralQExp_e4cube ΓH] at hyq
  have hyeq : y * intSeriesC ℚ δZ = intSeriesC ℚ (eisenstein4 ^ 3) := by
    apply coeffMap_ratComplex_injective
    rw [map_mul, coeffMap_ratComplex_intSeriesC, coeffMap_ratComplex_intSeriesC, hyq]
  have hy : y = jqModC ℚ := by
    rw [jqModC_eq_div, eq_div_iff (intSeriesC_delta_ne_zero ℚ), hyeq]
  have helt : (⟨coeffEmb Qb (jqModC ℚ), hjF⟩ : xHFunctionFieldBar M H) =
      ⟨coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ δZ),
        coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC (e4cube ΓH) (delta ΓH)
          (isIntegralQExp_e4cube ΓH) (isIntegralQExp_delta ΓH) (intSeriesC_delta_ne_zero ℚ))⟩ :=
    Subtype.ext (by
      change coeffEmb Qb (jqModC ℚ) = coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ δZ)
      rw [← jqModC_eq_div])
  apply Subtype.ext
  rw [helt, hσy, hy]
  change coeffEmb Qb (jqModC ℚ) = coeffEmb Qb (intSeriesC ℚ (eisenstein4 ^ 3) / intSeriesC ℚ δZ)
  rw [← jqModC_eq_div]

end Modular

end PLCDSol
p2m_reactivate "P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol"

open PLCDSol in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ) :
    AlgebraicCurve.Divisor.principal (K := AlgebraicClosure ℚ) (F := ModularCurve.xHFunctionFieldBar M H) ≤
      AddSubgroup.closure
        {D | ∃ (y u : LaurentSeries A)
            (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.xHFunctionFieldBar M H),
            ModularCurve.coeffMap A.subtype u =
              ((ModularCurve.diamondAutHBar M H d ⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
                  ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) u ∈
              ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H ∧
            ModularCurve.coeffMap (IsLocalRing.residue A) u ≠ 0 ∧
            ∀ P, D P = P.ord (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
              ModularCurve.xHFunctionFieldBar M H)} := by
  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H with hΓ
  have hT : ModularGroup.T ∈ Γ := translation_mem_GammaH M H

  obtain ⟨R, hRint, hRres⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A Γ hT
  have hres : ∀ y : LaurentSeries A, ι A y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) →
      ϖ A y ∈ qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ := by
    intro y hy
    obtain ⟨hO, hval⟩ := hRres y hy
    rw [← hval]
    exact SetLike.coe_mem _

  let σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) ≃ₐ[AlgebraicClosure ℚ]
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := diamondAutHBar M H d

  have hjQ : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ := by
    rw [jqModC_eq_div]
    exact div_mem_qExpFunctionFieldC (e4cube Γ) (delta Γ) (isIntegralQExp_e4cube Γ) (isIntegralQExp_delta Γ)
      (intSeriesC_delta_ne_zero ℚ)
  have hjF : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) :=
    coeffEmb_mem_laurentBaseChange _ hjQ
  have hjι : ι A (jqModC A) = coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) := by
    change (jqModC A).map _ = (jqModC ℚ).map _
    rw [map_jqModC, map_jqModC]
  have hjιF : ι A (jqModC A) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := hjι ▸ hjF
  obtain ⟨hjO, hjres⟩ := hRres (jqModC A) hjιF
  set x₀ : R.integers := ⟨⟨ι A (jqModC A), hjιF⟩, hjO⟩ with hx₀
  have hjres' : ((R.residue x₀ : qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
      LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A) := by
    rw [hx₀, hjres]
    change (jqModC A).map _ = _
    exact map_jqModC _
  have hx₀coe : ((x₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :
      LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    change ι A (jqModC A) = _
    change (jqModC A).map _ = _
    exact map_jqModC _
  have hσj : σ (x₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) = x₀ := by
    have hx₀eq : (x₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) =
        ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), hjF⟩ := Subtype.ext hjι
    rw [hx₀eq]
    exact diamond_j M H hin d hjF

  obtain ⟨xP, hxP, htrP, hfinP, hleP⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A Γ hT
  obtain rfl : xP = R.residue x₀ := Subtype.ext (hxP.trans hjres'.symm)
  haveI := hfinP
  have hpos : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({R.residue x₀} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
      (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) := Module.finrank_pos
  have hle1 := hleP (x₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) hx₀coe
  have hle2 := ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hℓM A hA
    (R.residue x₀) (x₀ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) hjres' hx₀coe
  have hdeg := le_antisymm hle2 hle1

  set V : ValuationSubring (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    R.integers.comap (σ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) →+*
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) with hV
  have hVmem : ∀ e, e ∈ V ↔ σ e ∈ R.integers := fun e => ValuationSubring.mem_comap
  have hVeq : V = R.integers := by
    refine AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R x₀ ?_ hpos hdeg V ?_
    · intro halg
      apply ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField A)
      have := halg.algebraMap (A := LaurentSeries (IsLocalRing.ResidueField A))
      rwa [show algebraMap (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)
        (LaurentSeries (IsLocalRing.ResidueField A)) (R.residue x₀) = jqModC (IsLocalRing.ResidueField A)
        from hjres'] at this
    · intro e he
      rw [hVmem, apply_eq_self_of_mem_adjoin σ hσj he]
  have hσO : ∀ f, σ f ∈ R.integers ↔ f ∈ R.integers := fun f => by rw [← hVmem, hVeq]
  have hσint : ∀ f : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ),
      IsInt A ((σ f : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :
        LaurentSeries (AlgebraicClosure ℚ)) ↔ IsInt A (f : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f
    have h1 := hRint (σ f)
    have h2 := hRint f
    unfold IsInt
    rw [← h1, ← h2]
    exact hσO f

  have hσgen : ∀ (W : ℕ) (h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (W : ℤ))) (p : PowerSeries ℤ)
      (hp : IsIntegralQExp h p), ∃ (c : AlgebraicClosure ℚ) (p₁ : PowerSeries ℤ),
        ((σ (genElt Γ h p hp) : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :
            LaurentSeries (AlgebraicClosure ℚ)) =
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c * intSeriesC (AlgebraicClosure ℚ) p₁ /
            intSeriesC (AlgebraicClosure ℚ) (δZ ^ W) :=
    fun W h p hp => diamond_genElt M H hin d W h p hp

  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
    obtain ⟨z, hz, hzfin⟩ :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
    haveI := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hz hzfin
    exact IsCurveOver.hasPrincipalDivisors
  exact principal_le_closure_genSet A Γ hT σ hres hσint hσgen

end
end S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar
end P2MW
export P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar (solution)
