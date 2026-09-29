-- Prove2me | solution 1 for ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/691adc9f-b365-5c6a-abf6-fc87650cfc73

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open IntermediateField AlgebraicCurve ModularCurve Polynomial

namespace QExpDeuringRed

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

def intSeriesA (p : PowerSeries ℤ) : LaurentSeries A :=
  HahnSeries.ofPowerSeries ℤ A (p.map (Int.castRingHom A))

theorem coeffMap_intSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : PowerSeries ℤ) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R (p.map (Int.castRingHom R))) =
      HahnSeries.ofPowerSeries ℤ S (p.map (Int.castRingHom S)) := by
  rw [coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem ι_intSeriesA (p : PowerSeries ℤ) : ι A (intSeriesA A p) = intSeriesC L p :=
  coeffMap_intSeries _ p

theorem ϖ_intSeriesA (p : PowerSeries ℤ) :
    ϖ A (intSeriesA A p) = intSeriesC (IsLocalRing.ResidueField A) p :=
  coeffMap_intSeries _ p

theorem coeffEmb_intSeriesC [Algebra ℚ L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p :=
  coeffMap_intSeries _ p

def IsInt (f : LaurentSeries L) : Prop :=
  ∃ x y : LaurentSeries A, ϖ A y ≠ 0 ∧ f * ι A y = ι A x

variable {A}

theorem ϖ_ne_zero_ne_zero {y : LaurentSeries A} (hy : ϖ A y ≠ 0) : y ≠ 0 := by
  rintro rfl; exact hy (map_zero _)

theorem IsInt.zero : IsInt A (0 : LaurentSeries L) := ⟨0, 1, by simp, by simp⟩

theorem IsInt.one : IsInt A (1 : LaurentSeries L) := ⟨1, 1, by simp, by simp⟩

theorem IsInt.mul {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.add {f g : LaurentSeries L} (hf : IsInt A f) (hg : IsInt A g) : IsInt A (f + g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * y' + x' * y, y * y', by rw [map_mul]; exact mul_ne_zero hy hy', ?_⟩
  rw [map_mul, map_add, map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.neg {f : LaurentSeries L} (hf : IsInt A f) : IsInt A (-f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  exact ⟨-x, y, hy, by rw [map_neg, ← h]; ring⟩

theorem IsInt.cross {f : LaurentSeries L} {x y x' y' : LaurentSeries A}
    (h : f * ι A y = ι A x) (h' : f * ι A y' = ι A x') : x * y' = x' * y := by
  apply ι_injective A
  rw [map_mul, map_mul, ← h, ← h']; ring

theorem IsInt.inv_of {f : LaurentSeries L} {x y : LaurentSeries A} (hx : ϖ A x ≠ 0)
    (h : f * ι A y = ι A x) : f⁻¹ * ι A x = ι A y := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, ι_eq_zero_iff] at h
    exact hx (by rw [h, map_zero])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

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

section IntGenerators

open ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

abbrev intLaurentC (K : Type*) [CommRing K] : LaurentSeries ℤ →+* LaurentSeries K :=
  coeffMap (Int.castRingHom K)

theorem coeffMap_intLaurentC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : LaurentSeries ℤ) :
    coeffMap f (intLaurentC R P) = intLaurentC S P := by
  rw [coeffMap_coeffMap, RingHom.ext_int (f.comp _) (Int.castRingHom S)]

theorem intLaurentC_ofPowerSeries (K : Type*) [CommRing K] (p : PowerSeries ℤ) :
    intLaurentC K (HahnSeries.ofPowerSeries ℤ ℤ p) = HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K)) :=
  coeffMap_ofPowerSeries _ p

theorem intLaurentC_ofPowerSeries' (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intLaurentC K (HahnSeries.ofPowerSeries ℤ ℤ p) = intSeriesC K p :=
  coeffMap_ofPowerSeries _ p

theorem intLaurentC_single (K : Type*) [CommRing K] (n : ℤ) (a : ℤ) :
    intLaurentC K (HahnSeries.single n a) = HahnSeries.single n (a : K) := by
  rw [coeffMap_single, eq_intCast]

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, hT, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

def delta : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ Γ) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem isIntegralQExp_delta :
    IsIntegralQExp (delta Γ : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) :=
  ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

theorem intSeriesC_pow (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (p ^ n) = intSeriesC K p ^ n := by
  simp [intSeriesC]

theorem intSeriesC_deltaPow_ne_zero (K : Type*) [Field K] (w : ℕ) :
    intSeriesC K ((PowerSeries.X * dedekindEtaUnit) ^ w) ≠ 0 := by
  rw [intSeriesC_pow]
  refine pow_ne_zero _ fun h => ?_
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem deltaPow_mul_inv (w : ℕ) :
    intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
      (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ)) = 1 := by
  have hUV : intSeriesC ℚ (dedekindEtaUnit ^ w) * intSeriesC ℚ (dedekindEtaUnitInv ^ w) = 1 := by
    rw [← intSeriesC_mul, ← mul_pow, dedekindEtaUnit_mul_inv, one_pow, intSeriesC_one]
  have hX : intSeriesC ℚ (PowerSeries.X ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ) = 1 := by
    rw [intSeriesC_pow, intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow,
      HahnSeries.single_mul_single]
    simp
  calc intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
        (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ))
      = (intSeriesC ℚ (PowerSeries.X ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ)) *
          (intSeriesC ℚ (dedekindEtaUnit ^ w) * intSeriesC ℚ (dedekindEtaUnitInv ^ w)) := by
        rw [mul_pow, intSeriesC_mul]; ring
    _ = 1 := by rw [hX, hUV, one_mul]

theorem exists_intLaurent_of_mem_intFormRatiosC [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    {x : LaurentSeries ℚ} (hx : x ∈ intFormRatiosC ℚ Γ) :
    ∃ P Q : LaurentSeries ℤ, intLaurentC ℚ P ∈ qExpFunctionFieldC ℚ Γ ∧
      intLaurentC ℚ Q ∈ qExpFunctionFieldC ℚ Γ ∧ intLaurentC ℚ Q ≠ 0 ∧
      x = intLaurentC ℚ P / intLaurentC ℚ Q := by
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

  have hper := one_mem_strictPeriods Γ hT
  have hG : IsIntegralQExp ((g.pow 12 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (w : ℤ))) : ℍ → ℂ)
      (pg ^ 12) := by
    rw [IsIntegralQExp, map_pow, hg, ModularForm.qExpansion_pow one_pos hper]
  have hD : IsIntegralQExp ((((delta Γ).pow w).mcast (by ring) :
      ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (w : ℤ))) : ℍ → ℂ)
      ((PowerSeries.X * dedekindEtaUnit) ^ w) := by
    rw [IsIntegralQExp, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos hper, map_pow,
      isIntegralQExp_delta]
  have hbmem : intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) ∈
      qExpFunctionFieldC ℚ Γ :=
    div_mem_qExpFunctionFieldC _ _ hG hD (intSeriesC_deltaPow_ne_zero ℚ w)
  obtain ⟨Q, hQ⟩ : ∃ Q : LaurentSeries ℤ, Q =
      HahnSeries.ofPowerSeries ℤ ℤ (pg ^ 12 * dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) 1 :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : LaurentSeries ℤ, P =
      HahnSeries.ofPowerSeries ℤ ℤ (pf * pg ^ 11 * dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) 1 :=
    ⟨_, rfl⟩
  have hQeq : intLaurentC ℚ Q = intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) := by
    rw [eq_div_iff (intSeriesC_deltaPow_ne_zero ℚ w), hQ, map_mul (intLaurentC ℚ), intLaurentC_ofPowerSeries',
      intLaurentC_single, Int.cast_one, intSeriesC_mul]
    calc intSeriesC ℚ (pg ^ 12) * intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ) *
          intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w)
        = intSeriesC ℚ (pg ^ 12) * (intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
            (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ))) := by ring
      _ = intSeriesC ℚ (pg ^ 12) := by rw [deltaPow_mul_inv, mul_one]
  have hPeq : intLaurentC ℚ P = intSeriesC ℚ pf / intSeriesC ℚ pg * intLaurentC ℚ Q := by
    rw [hQeq, hP, map_mul (intLaurentC ℚ), intLaurentC_ofPowerSeries', intLaurentC_single, Int.cast_one,
      div_mul_div_comm, eq_div_iff (mul_ne_zero hg0 (intSeriesC_deltaPow_ne_zero ℚ w)), intSeriesC_mul,
      intSeriesC_mul]
    calc intSeriesC ℚ pf * intSeriesC ℚ (pg ^ 11) * intSeriesC ℚ (dedekindEtaUnitInv ^ w) *
          HahnSeries.single (-(w : ℤ)) (1 : ℚ) *
          (intSeriesC ℚ pg * intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w))
        = intSeriesC ℚ pf * (intSeriesC ℚ (pg ^ 11) * intSeriesC ℚ pg) *
            (intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
              (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ))) := by ring
      _ = intSeriesC ℚ pf * intSeriesC ℚ (pg ^ 12) := by
          rw [deltaPow_mul_inv, mul_one, ← intSeriesC_mul, ← pow_succ]
  have hQ0 : intLaurentC ℚ Q ≠ 0 := by
    rw [hQeq]
    exact div_ne_zero (by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0) (intSeriesC_deltaPow_ne_zero ℚ w)
  refine ⟨P, Q, ?_, hQeq ▸ hbmem, hQ0, ?_⟩
  · rw [hPeq]
    exact mul_mem (div_mem_qExpFunctionFieldC f g hf hg hg0) (hQeq ▸ hbmem)
  · rw [hPeq, mul_div_assoc, div_self hQ0, mul_one]

variable (L : Type*) [Field L] [Algebra ℚ L]

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

def gensF : Set (LaurentSeries L) :=
  {u | ∃ P : LaurentSeries ℤ, intLaurentC ℚ P ∈ qExpFunctionFieldC ℚ Γ ∧ u = intLaurentC L P}

theorem coeffEmb_intLaurentC (P : LaurentSeries ℤ) : coeffEmb L (intLaurentC ℚ P) = intLaurentC L P :=
  coeffMap_intLaurentC _ P

theorem gensF_subset : gensF Γ L ⊆ (FF : Set (LaurentSeries L)) := by
  rintro _ ⟨P, hP, rfl⟩
  rw [← coeffEmb_intLaurentC]
  exact coeffEmb_mem_laurentBaseChange L hP

theorem adjoin_gensF_le : adjoin L (gensF Γ L) ≤ FF :=
  adjoin_le_iff.mpr (gensF_subset Γ L)

theorem laurentBaseChange_le_adjoin_gensF [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    FF ≤ adjoin L (gensF Γ L) := by
  change adjoin L _ ≤ adjoin L (gensF Γ L)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gensF Γ L)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gensF Γ L)).algebraMap_mem _
  · obtain ⟨P, Q, hP, hQ, -, rfl⟩ := exists_intLaurent_of_mem_intFormRatiosC Γ hT hz
    change coeffEmb L (intLaurentC ℚ P / intLaurentC ℚ Q) ∈ adjoin L (gensF Γ L)
    rw [map_div₀, coeffEmb_intLaurentC, coeffEmb_intLaurentC]
    exact div_mem (IntermediateField.subset_adjoin L _ ⟨P, hP, rfl⟩)
      (IntermediateField.subset_adjoin L _ ⟨Q, hQ, rfl⟩)

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gensF Γ L)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨P, -, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [intLaurentC, coeffMap_coeff, eq_intCast, ← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | algebraMap a =>
      refine ⟨Submodule.span ℤ {a}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
      split_ifs
      · exact Submodule.subset_span rfl
      · exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | mul x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ * M₂, hM₁.mul hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_mul]
      exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (h₁ _) (h₂ _)

theorem algebra_adjoin_gensF_le {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gensF Γ L)) : x ∈ FF :=
  adjoin_gensF_le Γ L (algebra_adjoin_le_adjoin L _ hx)

end IntGenerators

section Gauss

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

include hT in

theorem exists_frac_form (f : FF) (hf : f ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ x₀ y₀ : LaurentSeries A, ϖ A x₀ ≠ 0 ∧ ϖ A y₀ ≠ 0 ∧
      (f : LaurentSeries L) * ι A y₀ = algebraMap L (LaurentSeries L) c * ι A x₀ := by
  have hfF : (f : LaurentSeries L) ∈ adjoin L (gensF Γ L) := laurentBaseChange_le_adjoin_gensF Γ L hT f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Mr, hMr, hrM⟩ := exists_fg_coeff_mem Γ L hr
  obtain ⟨Ms, hMs, hsM⟩ := exists_fg_coeff_mem Γ L hs
  obtain ⟨cr, hcr, r₀, hr₀, hr'⟩ := exists_primitive_form A hr0 Mr hMr hrM
  obtain ⟨cs, hcs, s₀, hs₀, hs'⟩ := exists_primitive_form A hs0 Ms hMs hsM
  have hιs : ι A s₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hs₀
  refine ⟨cr / cs, div_ne_zero hcr hcs, r₀, s₀, hr₀, hs₀, ?_⟩
  rw [hrs, hr', hs', map_div₀]
  field_simp

def gaussRing : ValuationSubring FF where
  carrier := {f | IsInt A (f : LaurentSeries L)}
  mul_mem' {f g} hf hg := by
    change IsInt A ((f * g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_mul]; exact hf.mul hg
  one_mem' := by change IsInt A ((1 : FF) : LaurentSeries L); exact IsInt.one
  add_mem' {f g} hf hg := by
    change IsInt A ((f + g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_add]; exact hf.add hg
  zero_mem' := by change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
  neg_mem' {f} hf := by
    change IsInt A ((-f : FF) : LaurentSeries L)
    rw [IntermediateField.coe_neg]; exact hf.neg
  mem_or_inv_mem' f := by
    by_cases hf : f = 0
    · left; subst hf; change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
    obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form A Γ hT f hf
    rcases A.mem_or_inv_mem c with hc | hc
    · left
      refine ⟨HahnSeries.C ⟨c, hc⟩ * x₀, y₀, hy₀, ?_⟩
      rw [h, map_mul, ι_C]
    · right
      change IsInt A ((f⁻¹ : FF) : LaurentSeries L)
      refine ⟨HahnSeries.C ⟨c⁻¹, hc⟩ * y₀, x₀, hx₀, ?_⟩
      have hf' : (f : LaurentSeries L) ≠ 0 := fun h' => hf (Subtype.ext h')
      rw [IntermediateField.coe_inv, map_mul, ι_C]
      have hcC : algebraMap L (LaurentSeries L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      calc (f : LaurentSeries L)⁻¹ * ι A x₀
          = (f : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) c)⁻¹ *
              ((f : LaurentSeries L) * ι A y₀) := by rw [h]; field_simp
        _ = algebraMap L (LaurentSeries L) (↑(⟨c⁻¹, hc⟩ : A) : L) * ι A y₀ := by
              rw [map_inv₀]; field_simp

theorem mem_gaussRing_iff (f : FF) : f ∈ gaussRing A Γ hT ↔ IsInt A (f : LaurentSeries L) := Iff.rfl

end Gauss

section Residue

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

theorem exists_witness (f : gaussRing A Γ hT) :
    ∃ p : LaurentSeries A × LaurentSeries A,
      ϖ A p.2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A p.2 = ι A p.1 := by
  obtain ⟨x, y, hy, h⟩ := f.2
  exact ⟨(x, y), hy, h⟩

def wit (f : gaussRing A Γ hT) : LaurentSeries A × LaurentSeries A :=
  Classical.choose (exists_witness A Γ hT f)

theorem wit_spec (f : gaussRing A Γ hT) :
    ϖ A (wit A Γ hT f).2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A (wit A Γ hT f).2 = ι A (wit A Γ hT f).1 :=
  Classical.choose_spec (exists_witness A Γ hT f)

def resL (f : gaussRing A Γ hT) : LaurentSeries kk :=
  ϖ A (wit A Γ hT f).1 / ϖ A (wit A Γ hT f).2

theorem resL_eq {f : gaussRing A Γ hT} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resL A Γ hT f = ϖ A x / ϖ A y := by
  obtain ⟨hy', h'⟩ := wit_spec A Γ hT f
  have hc := IsInt.cross (A := A) h' h
  rw [resL, div_eq_div_iff hy' hy, ← map_mul, ← map_mul, hc]

def resHom : gaussRing A Γ hT →+* LaurentSeries kk where
  toFun := resL A Γ hT
  map_one' := by
    rw [resL_eq A Γ hT (x := 1) (y := 1) (by simp) (by simp)]; simp
  map_mul' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A Γ hT f
    obtain ⟨hg, hg'⟩ := wit_spec A Γ hT g
    have h : (((f * g : gaussRing A Γ hT) : FF) : LaurentSeries L) * ι A ((wit A Γ hT f).2 * (wit A Γ hT g).2)
        = ι A ((wit A Γ hT f).1 * (wit A Γ hT g).1) := by
      rw [map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A Γ hT (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A Γ hT f * resL A Γ hT g
    rw [resL, resL, map_mul, map_mul, mul_div_mul_comm]
  map_zero' := by
    rw [resL_eq A Γ hT (x := 0) (y := 1) (by simp) (by simp)]; simp
  map_add' f g := by
    obtain ⟨hf, hf'⟩ := wit_spec A Γ hT f
    obtain ⟨hg, hg'⟩ := wit_spec A Γ hT g
    have h : (((f + g : gaussRing A Γ hT) : FF) : LaurentSeries L) * ι A ((wit A Γ hT f).2 * (wit A Γ hT g).2)
        = ι A ((wit A Γ hT f).1 * (wit A Γ hT g).2 + (wit A Γ hT g).1 * (wit A Γ hT f).2) := by
      rw [map_add, map_mul, map_mul, map_mul, ← hf', ← hg']; push_cast; ring
    rw [resL_eq A Γ hT (by rw [map_mul]; exact mul_ne_zero hf hg) h]
    change _ = resL A Γ hT f + resL A Γ hT g
    rw [resL, resL, div_add_div _ _ hf hg, map_add, map_mul, map_mul, map_mul]
    ring

theorem resHom_eq {f : gaussRing A Γ hT} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resHom A Γ hT f = ϖ A x / ϖ A y :=
  resL_eq A Γ hT hy h

theorem resHom_eq_zero_iff (f : gaussRing A Γ hT) :
    resHom A Γ hT f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (gaussRing A Γ hT) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨hy, h⟩ := wit_spec A Γ hT f
  constructor
  · rintro h0 ⟨u, rfl⟩
    have := congrArg (resHom A Γ hT) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hu
    by_contra h0
    apply hu
    rw [resHom_eq A Γ hT hy h, div_eq_zero_iff, or_iff_left hy] at h0
    have hf0 : ((f : FF) : LaurentSeries L) ≠ 0 := by
      intro hf
      rw [hf, zero_mul, eq_comm, ι_eq_zero_iff] at h
      exact h0 (by rw [h, map_zero])
    have hf0' : (f : FF) ≠ 0 := fun h' => hf0 (by rw [h']; rfl)
    have hinv : (f : FF)⁻¹ ∈ gaussRing A Γ hT := by
      refine ⟨(wit A Γ hT f).2, (wit A Γ hT f).1, h0, ?_⟩
      rw [IntermediateField.coe_inv]
      exact IsInt.inv_of (A := A) h0 h
    exact ⟨⟨f, ⟨(f : FF)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0'),
      Subtype.ext (inv_mul_cancel₀ hf0')⟩, rfl⟩

theorem coe_algebraMap (c : L) :
    ((algebraMap L FF c : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl

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

theorem algebraMap_mem_gaussRing_iff (c : L) : algebraMap L FF c ∈ gaussRing A Γ hT ↔ c ∈ A := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    rw [coe_algebraMap] at h
    by_contra hc
    have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
    obtain ⟨hci, hcm⟩ := exists_inv_mem_maximalIdeal A hc
    have hyx : y = HahnSeries.C ⟨c⁻¹, hci⟩ * x := by
      apply ι_injective A
      rw [map_mul, ι_C, ← h, ← mul_assoc, ← map_mul]
      simp [inv_mul_cancel₀ hc0]
    apply hy
    rw [ϖ_eq_zero_iff]
    intro n
    rw [hyx, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hcm
  · intro hc
    refine ⟨HahnSeries.C ⟨c, hc⟩, 1, by simp, ?_⟩
    rw [coe_algebraMap, ι_C, map_one, mul_one]

theorem resHom_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A Γ hT) :
    resHom A Γ hT ⟨algebraMap L FF a, h⟩ = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a) := by
  rw [resHom_eq A Γ hT (x := HahnSeries.C a) (y := 1) (by simp)
    (by rw [map_one, mul_one]; change algebraMap L (LaurentSeries L) (a : L) = _; rw [ι_C]),
    ϖ_C, map_one, div_one]

end Residue

section PolyJ

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem exists_primitive_poly {r : L[X]} (hr : r ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ ∃ r₀ : A[X], r = C c * r₀.map A.subtype ∧ r₀.map (IsLocalRing.residue A) ≠ 0 := by
  have hne : (r.support.image r.coeff).Nonempty := by
    rw [Finset.image_nonempty, Polynomial.nonempty_support_iff]; exact hr
  obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image _ A.valuation hne
  obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hcT
  have hc0 : r.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  have hvx : ∀ n, A.valuation (r.coeff n) ≤ A.valuation (r.coeff n₀) := fun n => by
    by_cases hn : n ∈ r.support
    · exact hcmax _ (Finset.mem_image_of_mem _ hn)
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  have hcA : ∀ n, (r.coeff n₀)⁻¹ * r.coeff n ∈ A := fun n => by
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    have hc' : A.valuation (r.coeff n₀) ≠ 0 := by simpa using hc0
    rw [inv_mul_le_one₀ (zero_lt_iff.mpr hc')]
    exact hvx n
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : A[X], r₀.map A.subtype = C (r.coeff n₀)⁻¹ * r := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    exact ⟨⟨_, hcA n⟩, rfl⟩
  refine ⟨r.coeff n₀, hc0, r₀, ?_, ?_⟩
  · rw [hr₀, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
  · intro h
    have h1 := congrArg (fun p : (IsLocalRing.ResidueField A)[X] => p.coeff n₀) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
    have h2 : (r₀.coeff n₀ : L) = 1 := by
      have := congrArg (fun p : L[X] => p.coeff n₀) hr₀
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul, inv_mul_cancel₀ hc0] at this
      exact this
    have h3 : r₀.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1

theorem algebraMap_laurentSeries_A (a : A) : algebraMap A (LaurentSeries A) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap A (PowerSeries A) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem ι_aeval (p : A[X]) : ι A (aeval (jqModC A) p) = aeval (jqModC L) (p.map A.subtype) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, coeffMap_jqModC]
  congr 1
  refine RingHom.ext fun a => ?_
  change ι A (algebraMap A (LaurentSeries A) a) = algebraMap L (LaurentSeries L) (a : L)
  rw [algebraMap_laurentSeries_A]
  exact ι_C A a

theorem ϖ_aeval (p : A[X]) :
    ϖ A (aeval (jqModC A) p) = aeval (jqModC kk) (p.map (IsLocalRing.residue A)) := by
  rw [aeval_def, aeval_def, hom_eval₂, eval₂_map, coeffMap_jqModC]
  congr 1
  refine RingHom.ext fun a => ?_
  change ϖ A (algebraMap A (LaurentSeries A) a) =
    algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a)
  rw [algebraMap_laurentSeries_A]
  exact ϖ_C A a

theorem aeval_jqModC_ne_zero {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    aeval (jqModC K) p ≠ 0 := fun h =>
  hp ((transcendental_iff.mp (ModularCurve.transcendental_jqModC K)) p h)

theorem jqModC_mem_rat : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ :=
  intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)

theorem jqModC_mem_FF : jqModC L ∈ FF := by
  have h := coeffEmb_mem_laurentBaseChange L (jqModC_mem_rat Γ)
  rwa [coeffEmb, coeffMap_jqModC] at h

def jF : FF := ⟨jqModC L, jqModC_mem_FF Γ⟩

theorem coe_jF : ((jF Γ : FF) : LaurentSeries L) = jqModC L := rfl

theorem coe_jF' : ((jF Γ : FF) : LaurentSeries L) = ι A (jqModC A) := by
  rw [coe_jF, coeffMap_jqModC]

def jbar (K : Type*) [Field K] : qExpFunctionFieldC K Γ :=
  ⟨jqModC K, intFormRatiosC_subset K Γ (ModularCurve.jqModC_mem_intFormRatiosC K Γ)⟩

theorem coe_jbar (K : Type*) [Field K] : ((jbar Γ K : qExpFunctionFieldC K Γ) : LaurentSeries K) = jqModC K :=
  rfl

theorem transcendental_jbar (K : Type*) [Field K] :
    Transcendental K (jbar Γ K : qExpFunctionFieldC K Γ) :=
  fun h => transcendental_jqModC K
    ((isAlgebraic_algHom_iff (qExpFunctionFieldC K Γ).val Subtype.val_injective).mpr h)

theorem transcendental_jF : Transcendental L (jF Γ : FF) :=
  fun h => transcendental_jqModC L
    ((isAlgebraic_algHom_iff (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).val
      Subtype.val_injective).mpr h)

theorem jF_mem_gaussRing : (jF Γ : FF) ∈ gaussRing A Γ hT :=
  (mem_gaussRing_iff A Γ hT _).mpr ⟨jqModC A, 1, by rw [map_one]; exact one_ne_zero,
    by rw [map_one, mul_one, coe_jF']⟩

theorem resHom_jF : resHom A Γ hT ⟨jF Γ, jF_mem_gaussRing A Γ hT⟩ = jqModC kk := by
  rw [resHom_eq A Γ hT (f := ⟨jF Γ, jF_mem_gaussRing A Γ hT⟩) (x := jqModC A) (y := 1)
    (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact coe_jF' A Γ),
    map_one, div_one, coeffMap_jqModC]

theorem intSeriesC_ne_zero_rat {K : Type*} [Field K] {p : PowerSeries ℤ} (hp : intSeriesC K p ≠ 0) :
    intSeriesC ℚ p ≠ 0 := by
  intro h0
  apply hp
  have hp0 : p = 0 := by
    ext n
    have h1 := congrArg (fun z : LaurentSeries ℚ => z.coeff (n : ℤ)) h0
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      HahnSeries.coeff_zero, eq_intCast, Int.cast_eq_zero] at h1
    simpa using h1
  rw [hp0, intSeriesC_zero]

theorem exists_resHom_eq {z : LaurentSeries kk} (hz : z ∈ qExpFunctionFieldC kk Γ) :
    ∃ f : gaussRing A Γ hT, resHom A Γ hT f = z := by
  let S : Subfield (LaurentSeries kk) :=
    { carrier := Set.range (resHom A Γ hT)
      mul_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f * g, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exact ⟨f + g, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      neg_mem' := by rintro _ ⟨f, rfl⟩; exact ⟨-f, map_neg _ _⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases h0 : resHom A Γ hT f = 0
        · exact ⟨0, by rw [h0, inv_zero, map_zero]⟩
        · have hu : IsUnit f := by
            by_contra hu
            exact h0 ((resHom_eq_zero_iff A Γ hT f).mpr
              ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))
          obtain ⟨u, rfl⟩ := hu
          refine ⟨↑u⁻¹, ?_⟩
          exact (inv_eq_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm }
  have hle : Subfield.closure (Set.range (algebraMap kk (LaurentSeries kk)) ∪ intFormRatiosC kk Γ)
      ≤ S := by
    rw [Subfield.closure_le]
    rintro z (⟨t, rfl⟩ | ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩)
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
      exact ⟨⟨_, (algebraMap_mem_gaussRing_iff A Γ hT (a : L)).mpr a.2⟩, resHom_algebraMap A Γ hT a _⟩
    ·
      have hgQ : intSeriesC ℚ pg ≠ 0 := intSeriesC_ne_zero_rat hg0
      have hmem : ι A (intSeriesA A pf) / ι A (intSeriesA A pg) ∈ FF := by
        have h := coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC f g hf hg hgQ)
        rwa [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, ← ι_intSeriesA A pf,
          ← ι_intSeriesA A pg] at h
      have hϖg : ϖ A (intSeriesA A pg) ≠ 0 := by rwa [ϖ_intSeriesA]
      have hιg : ι A (intSeriesA A pg) ≠ 0 := by
        rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hϖg
      have hw : ((⟨_, hmem⟩ : FF) : LaurentSeries L) * ι A (intSeriesA A pg) = ι A (intSeriesA A pf) := by
        change ι A (intSeriesA A pf) / ι A (intSeriesA A pg) * ι A (intSeriesA A pg) = _
        rw [div_mul_cancel₀ _ hιg]
      have hO : (⟨_, hmem⟩ : FF) ∈ gaussRing A Γ hT := (mem_gaussRing_iff A Γ hT _).mpr ⟨_, _, hϖg, hw⟩
      refine ⟨⟨_, hO⟩, ?_⟩
      rw [resHom_eq A Γ hT (f := ⟨_, hO⟩) hϖg hw, ϖ_intSeriesA, ϖ_intSeriesA]
  obtain ⟨f, hf⟩ := hle (show z ∈ Subfield.closure _ from hz)
  exact ⟨f, hf⟩

set_option maxHeartbeats 6400000 in

theorem exists_adjoin_coe_eq_resHom {g : FF} (hgK : g ∈ IntermediateField.adjoin L {(jF Γ : FF)})
    (hgO : g ∈ gaussRing A Γ hT) :
    ∃ t : IntermediateField.adjoin kk {(jbar Γ kk : Fb)},
      (((t : Fb) : LaurentSeries kk)) = resHom A Γ hT ⟨g, hgO⟩ := by
  rw [mem_adjoin_simple_iff] at hgK
  obtain ⟨r, s, hrs⟩ := hgK
  by_cases hg0 : g = 0
  · refine ⟨0, ?_⟩
    have : (⟨g, hgO⟩ : gaussRing A Γ hT) = 0 := Subtype.ext hg0
    rw [this, map_zero]; rfl
  have hr0 : r ≠ 0 := by rintro rfl; apply hg0; rw [hrs, map_zero, zero_div]
  have hs0 : s ≠ 0 := by rintro rfl; apply hg0; rw [hrs, map_zero, div_zero]
  obtain ⟨cr, hcr, r₀, hr', hr₀⟩ := exists_primitive_poly A hr0
  obtain ⟨cs, hcs, s₀, hs', hs₀⟩ := exists_primitive_poly A hs0
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀, R₀ = aeval (jqModC A) r₀ := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀def⟩ : ∃ S₀, S₀ = aeval (jqModC A) s₀ := ⟨_, rfl⟩
  have hιR : aeval (jqModC L) (r₀.map A.subtype) = ι A R₀ := by rw [hR₀def, ι_aeval]
  have hιS : aeval (jqModC L) (s₀.map A.subtype) = ι A S₀ := by rw [hS₀def, ι_aeval]
  have hϖR : ϖ A R₀ = aeval (jqModC kk) (r₀.map (IsLocalRing.residue A)) := by rw [hR₀def, ϖ_aeval]
  have hϖS : ϖ A S₀ = aeval (jqModC kk) (s₀.map (IsLocalRing.residue A)) := by rw [hS₀def, ϖ_aeval]
  have hR₀ : ϖ A R₀ ≠ 0 := by rw [hϖR]; exact aeval_jqModC_ne_zero hr₀
  have hS₀ : ϖ A S₀ ≠ 0 := by rw [hϖS]; exact aeval_jqModC_ne_zero hs₀
  have hιS₀ : ι A S₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hS₀
  have hιR₀ : ι A R₀ ≠ 0 := by rw [Ne, ι_eq_zero_iff]; exact ϖ_ne_zero_ne_zero hR₀
  have e0 : ∀ p : L[X], ((aeval (jF Γ) p : FF) : LaurentSeries L) = aeval (jqModC L) p := fun p => by
    rw [← coe_jF (L := L) Γ]
    exact (aeval_algHom_apply (laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).val (jF Γ) p).symm
  have e1 : (g : LaurentSeries L) = aeval (jqModC L) r / aeval (jqModC L) s := by
    rw [hrs, IntermediateField.coe_div, e0, e0]
  have hgcoe : (g : LaurentSeries L) * ι A S₀ = algebraMap L _ (cr / cs) * ι A R₀ := by
    rw [e1, hr', hs', map_mul, map_mul, aeval_C, aeval_C, hιR, hιS, map_div₀]
    have hcs' : algebraMap L (LaurentSeries L) cs ≠ 0 := (_root_.map_ne_zero _).mpr hcs
    field_simp
  by_cases he : cr / cs ∈ A
  · have hw : (g : LaurentSeries L) * ι A S₀ = ι A (HahnSeries.C ⟨cr / cs, he⟩ * R₀) := by
      rw [hgcoe, map_mul, ι_C]
    have e0k : ∀ p : kk[X], ((aeval (jbar Γ kk : Fb) p : Fb) : LaurentSeries kk) = aeval (jqModC kk) p :=
      fun p => (aeval_algHom_apply (qExpFunctionFieldC kk Γ).val (jbar Γ kk) p).symm
    have hmemK : ∀ p : kk[X], aeval (jbar Γ kk : Fb) p ∈ IntermediateField.adjoin kk {(jbar Γ kk : Fb)} :=
      fun p => IntermediateField.algebra_adjoin_le_adjoin kk _ (Polynomial.aeval_mem_adjoin_singleton kk _)
    refine ⟨⟨aeval (jbar Γ kk : Fb) (C (IsLocalRing.residue A ⟨cr / cs, he⟩) * r₀.map (IsLocalRing.residue A)) /
      aeval (jbar Γ kk : Fb) (s₀.map (IsLocalRing.residue A)), div_mem (hmemK _) (hmemK _)⟩, ?_⟩
    change (((aeval (jbar Γ kk : Fb) (C (IsLocalRing.residue A ⟨cr / cs, he⟩) * r₀.map (IsLocalRing.residue A)) /
      aeval (jbar Γ kk : Fb) (s₀.map (IsLocalRing.residue A)) : Fb)) : LaurentSeries kk) = _
    rw [resHom_eq A Γ hT (f := ⟨g, hgO⟩) hS₀ hw, map_mul (ϖ A), ϖ_C, hϖR, hϖS,
      IntermediateField.coe_div, map_mul, IntermediateField.coe_mul, e0k, e0k, aeval_C]
    rw [e0k]
  · exfalso
    obtain ⟨hei, hem⟩ := exists_inv_mem_maximalIdeal A he
    have he0 : cr / cs ≠ 0 := div_ne_zero hcr hcs
    have hg0' : (g : LaurentSeries L) ≠ 0 := fun h => hg0 (Subtype.ext h)
    obtain ⟨g', hg'⟩ : ∃ g' : FF, (g' : LaurentSeries L) = (g : LaurentSeries L)⁻¹ := ⟨g⁻¹, rfl⟩
    obtain ⟨a, ha, hres0⟩ : ∃ a : A, (a : L) = (cr / cs)⁻¹ ∧ IsLocalRing.residue A a = 0 :=
      ⟨⟨_, hei⟩, rfl, Ideal.Quotient.eq_zero_iff_mem.mpr hem⟩
    have hw : (g' : LaurentSeries L) * ι A R₀ = ι A (HahnSeries.C a * S₀) := by
      rw [hg', map_mul, ι_C, ha]
      have hC : algebraMap L (LaurentSeries L) (cr / cs) ≠ 0 := (_root_.map_ne_zero _).mpr he0
      calc (g : LaurentSeries L)⁻¹ * ι A R₀
          = (g : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) (cr / cs))⁻¹ *
              ((g : LaurentSeries L) * ι A S₀) := by rw [hgcoe]; field_simp
        _ = algebraMap L (LaurentSeries L) (cr / cs)⁻¹ * ι A S₀ := by
              rw [map_inv₀]; field_simp
    have hinvO : g' ∈ gaussRing A Γ hT := (mem_gaussRing_iff A Γ hT _).mpr ⟨_, _, hR₀, hw⟩
    have hϖx : ϖ A (HahnSeries.C a * S₀) = 0 := by
      simp only [map_mul (ϖ A), ϖ_C, hres0, map_zero, zero_mul]
    have hres : resHom A Γ hT ⟨g', hinvO⟩ = 0 := by
      simp only [resHom_eq A Γ hT (f := ⟨g', hinvO⟩) hR₀ hw, hϖx, zero_div]
    have h1 : (⟨g, hgO⟩ : gaussRing A Γ hT) * ⟨g', hinvO⟩ = 1 := by
      apply Subtype.ext; apply Subtype.ext
      change (g : LaurentSeries L) * (g' : LaurentSeries L) = 1
      rw [hg']; exact mul_inv_cancel₀ hg0'
    have h2 : resHom A Γ hT ⟨g, hgO⟩ * resHom A Γ hT ⟨g', hinvO⟩ = 1 := by
      rw [← map_mul (resHom A Γ hT), h1, map_one]
    rw [hres, mul_zero] at h2
    exact zero_ne_one h2

end PolyJ

section Image

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

set_option maxHeartbeats 6400000 in

theorem resHom_mem
    [Module.Finite (IntermediateField.adjoin L {(jF Γ : FF)}) FF]
    [FiniteDimensional (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb]
    (hle : Module.finrank (IntermediateField.adjoin L {(jF Γ : FF)}) FF ≤
      Module.finrank (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb)
    (f : gaussRing A Γ hT) : resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ := by
  set K0 := IntermediateField.adjoin L {(jF Γ : FF)} with hK0
  set K0' := IntermediateField.adjoin kk {(jbar Γ kk : Fb)} with hK0'
  set n := Module.finrank K0' Fb with hn
  let bbar := Module.finBasisOfFinrankEq K0' Fb hn.symm
  have hb : ∀ i, ∃ b : gaussRing A Γ hT, resHom A Γ hT b = ((bbar i : Fb) : LaurentSeries kk) :=
    fun i => exists_resHom_eq A Γ hT (bbar i).2
  choose b hb using hb
  let v : Option (Fin n) → FF := fun o => o.elim (f : FF) (fun i => (b i : FF))
  have hdep : ¬ LinearIndependent K0 v := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_fin] at h
    omega
  obtain ⟨g, hg, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.mp hdep
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun o => (gaussRing A Γ hT).valuation ((g o : K0) : FF)) Finset.univ_nonempty
  have hgi₀ : ((g i₀ : K0) : FF) ≠ 0 := by
    intro h0
    apply hi₁
    have := hi₀ i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ZeroMemClass.coe_eq_zero.mp this
  have hvpos : 0 < (gaussRing A Γ hT).valuation ((g i₀ : K0) : FF) := (Valuation.pos_iff _).mpr hgi₀

  let c : Option (Fin n) → FF := fun o => ((g o : K0) : FF) / ((g i₀ : K0) : FF)
  have hcK : ∀ o, c o ∈ K0 := fun o => div_mem (g o).2 (g i₀).2
  have hcO : ∀ o, c o ∈ gaussRing A Γ hT := fun o => by
    rw [← (gaussRing A Γ hT).valuation_le_one_iff]
    show (gaussRing A Γ hT).valuation (_ / _) ≤ 1
    rw [map_div₀, div_le_one₀ hvpos]
    exact hi₀ o (Finset.mem_univ o)
  have hci₀ : c i₀ = 1 := div_self hgi₀
  have hrel : ∑ o, c o * v o = 0 := by
    have h1 : ∑ o, ((g o : K0) : FF) * v o = 0 := by
      simpa only [IntermediateField.smul_def, smul_eq_mul] using hg
    calc ∑ o, c o * v o = ((g i₀ : K0) : FF)⁻¹ * ∑ o, ((g o : K0) : FF) * v o := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun o _ => by simp only [c]; ring
      _ = 0 := by rw [h1, mul_zero]

  have ht : ∀ o, ∃ t : K0', ((t : Fb) : LaurentSeries kk) = resHom A Γ hT ⟨c o, hcO o⟩ :=
    fun o => exists_adjoin_coe_eq_resHom A Γ hT (hcK o) (hcO o)
  choose t ht using ht
  have hti₀ : t i₀ = 1 := by
    have h1 : (⟨c i₀, hcO i₀⟩ : gaussRing A Γ hT) = 1 := Subtype.ext hci₀
    have h2 : ((t i₀ : Fb) : LaurentSeries kk) = (((1 : K0') : Fb) : LaurentSeries kk) := by
      rw [ht i₀, h1, map_one]; simp
    exact Subtype.ext (Subtype.ext h2)

  let w : Option (Fin n) → gaussRing A Γ hT := fun o => o.elim f b
  have hvw : ∀ o, v o = (w o : FF) := by rintro (_ | _) <;> rfl
  have hrelO : ∑ o, (⟨c o, hcO o⟩ : gaussRing A Γ hT) * w o = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [hvw] at hrel
    exact hrel
  have hres : ∑ o, ((t o : Fb) : LaurentSeries kk) * resHom A Γ hT (w o) = 0 := by
    have := congrArg (resHom A Γ hT) hrelO
    simpa only [map_sum, map_mul, map_zero, ht] using this
  have hwn : resHom A Γ hT (w none) = resHom A Γ hT f := rfl
  have hws : ∀ i, resHom A Γ hT (w (some i)) = ((bbar i : Fb) : LaurentSeries kk) := fun i => hb i
  rw [Fintype.sum_option, hwn] at hres
  simp only [hws] at hres
  by_cases htn : t none = 0
  · exfalso
    have hsum : ∑ i, ((t (some i) : Fb) : LaurentSeries kk) * ((bbar i : Fb) : LaurentSeries kk) = 0 := by
      simpa only [htn, ZeroMemClass.coe_zero, zero_mul, zero_add] using hres
    have hsum' : (∑ i, t (some i) • bbar i : Fb) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [IntermediateField.smul_def, smul_eq_mul, IntermediateField.coe_mul] at hsum ⊢
      exact hsum
    have hall := Fintype.linearIndependent_iff.mp bbar.linearIndependent (fun i => t (some i)) hsum'
    have : t i₀ = 0 := by
      rcases i₀ with _ | i
      · exact htn
      · exact hall i
    rw [hti₀] at this
    exact one_ne_zero this
  · have htn' : ((t none : Fb) : LaurentSeries kk) ≠ 0 := by
      intro h; apply htn
      exact Subtype.ext (Subtype.ext (by simpa using h))
    have key : resHom A Γ hT f =
        -(∑ i, ((t (some i) : Fb) : LaurentSeries kk) * ((bbar i : Fb) : LaurentSeries kk)) /
          ((t none : Fb) : LaurentSeries kk) := by
      rw [eq_div_iff htn', eq_neg_iff_add_eq_zero, mul_comm]
      exact hres
    rw [key]
    exact div_mem (neg_mem (sum_mem fun i _ => mul_mem (t (some i) : Fb).2 (bbar i).2)) (t none : Fb).2

end Image

section Assembly

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

theorem exists_smul_mem_gaussRing (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A Γ hT, resHom A Γ hT ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form A Γ hT f hf
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ gaussRing A Γ hT := (mem_gaussRing_iff A Γ hT _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A Γ hT (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) : (⟨ι A y, hyF⟩ : FF) ∈ gaussRing A Γ hT :=
  ⟨y, 1, by simp, by simp⟩

theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A Γ hT ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A Γ hT hyF⟩ = ϖ A y := by
  rw [resHom_eq A Γ hT (x := y) (y := 1) (by simp) (by simp)]; simp

def resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) :
    gaussRing A Γ hT →+* Fb :=
  (resHom A Γ hT).codRestrict (qExpFunctionFieldC kk Γ) hmem

theorem coe_resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (f : gaussRing A Γ hT) : ((resF A Γ hT hmem f : Fb) : LaurentSeries kk) = resHom A Γ hT f := rfl

theorem resF_ne_zero_iff (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (f : gaussRing A Γ hT) : resF A Γ hT hmem f ≠ 0 ↔ resHom A Γ hT f ≠ 0 := by
  rw [Ne, Ne, ← coe_resF A Γ hT hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_surjective (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) : Function.Surjective (resF A Γ hT hmem) := fun z => by
  obtain ⟨f, hf⟩ := exists_resHom_eq A Γ hT z.2
  exact ⟨f, Subtype.ext hf⟩

theorem ker_resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) : RingHom.ker (resF A Γ hT hmem) = IsLocalRing.maximalIdeal (gaussRing A Γ hT) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resF A Γ hT hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_algebraMap (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (a : A) (h : algebraMap L FF a ∈ gaussRing A Γ hT) :
    resF A Γ hT hmem ⟨algebraMap L FF a, h⟩ = algebraMap kk Fb (IsLocalRing.residue A a) :=
  Subtype.ext (resHom_algebraMap A Γ hT a h)

theorem exists_smul_mem_resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A Γ hT, resF A Γ hT hmem ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A Γ hT f hf
  exact ⟨c, h, (resF_ne_zero_iff A Γ hT hmem _).mpr hne⟩

theorem resF_jF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) : resF A Γ hT hmem ⟨jF Γ, jF_mem_gaussRing A Γ hT⟩ = jbar Γ kk :=
  Subtype.ext (resHom_jF A Γ hT)

theorem exists_placeMap (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) [IsAlgClosed L] [IsCurveOver L FF] [IsCurveOver kk Fb]
    (hfin : Module.finrank (IntermediateField.adjoin L {(jF Γ : FF)}) FF =
      Module.finrank (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb)
    (hpos : 0 < Module.finrank (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb)
    (hgood : genusFF kk Fb = genusFF L FF) :
    ∃ r : Place L FF → Place kk Fb,
      ∀ f : gaussRing A Γ hT, resF A Γ hT hmem f ≠ 0 → ∀ D : Divisor L FF, (∀ P, D P = P.ord (f : FF)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (resF A Γ hT hmem f : Fb) :=
  AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction A
    (gaussRing A Γ hT) (resF A Γ hT hmem) (algebraMap_mem_gaussRing_iff A Γ hT) (resF_surjective A Γ hT hmem)
    (ker_resF A Γ hT hmem) (fun a => resF_algebraMap A Γ hT hmem a _) (exists_smul_mem_resF A Γ hT hmem)
    ⟨⟨jF Γ, jF_mem_gaussRing A Γ hT⟩, by
      rw [resF_jF]
      exact ⟨transcendental_jbar Γ kk, hpos, hfin⟩⟩
    hgood

end Assembly

section ClauseB

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have h := v.ord_coe_unit (Units.map (algebraMap K v.toValuationSubring).toMonoidHom (Units.mk0 a ha))
  simpa using h

theorem exists_mem_integralPrincipalDivisors_of_mem_adjoin [HasPrincipalDivisors L FF]
    (hq : ∀ y : LaurentSeries A, ι A y ∈ FF → ϖ A y ∈ Fb)
    {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gensF Γ L)) (hx0 : x ≠ 0) :
    ∃ D₀ ∈ laurentIntegralPrincipalDivisors A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb,
      ∀ v : Place L FF, D₀ v = v.ord (⟨x, algebra_adjoin_gensF_le Γ L hx⟩ : FF) := by
  obtain ⟨M, hM, hxM⟩ := exists_fg_coeff_mem Γ L hx
  obtain ⟨c, hc0, hcA, n₀, hn₀⟩ := exists_primitive_scaling A hx0 M hM hxM
  have hxF : x ∈ FF := algebra_adjoin_gensF_le Γ L hx
  have hx'F : algebraMap L (LaurentSeries L) c⁻¹ * x ∈ FF :=
    mul_mem ((laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).algebraMap_mem _) hxF
  have hcoeff : ∀ n, (algebraMap L (LaurentSeries L) c⁻¹ * x).coeff n = c⁻¹ * x.coeff n := fun n => by
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A (algebraMap L (LaurentSeries L) c⁻¹ * x) fun n => by
    rw [hcoeff]; exact hcA n
  have hyF : ι A y ∈ FF := hy ▸ hx'F
  have hyk : ϖ A y ∈ Fb := hq y hyF
  have hy0 : ϖ A y ≠ 0 := by
    intro h
    have h1 := congrArg (fun s : LaurentSeries kk => s.coeff n₀) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (y.coeff n₀ : L) = 1 := by
      have := congrArg (fun s : LaurentSeries L => s.coeff n₀) hy
      simp only [coeffMap_coeff, hcoeff] at this
      rw [← hn₀]; exact this
    have h3 : y.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨D₀, hD₀, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := L) (⟨ι A y, hyF⟩ : FF) (by
      intro h
      apply hy0
      have h' : ι A y = 0 := congrArg Subtype.val h
      rw [(ι_eq_zero_iff A y).mp h', map_zero])
  refine ⟨D₀, ⟨y, hyF, hyk, hy0, hD₀⟩, fun v => ?_⟩
  rw [hD₀ v]
  have heq : (⟨ι A y, hyF⟩ : FF) = algebraMap L FF c⁻¹ * ⟨x, hxF⟩ := by
    apply Subtype.ext
    change ι A y = algebraMap L (LaurentSeries L) c⁻¹ * x
    rw [hy]
  have hxne : (⟨x, hxF⟩ : FF) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hcne : algebraMap L FF c⁻¹ ≠ 0 := (_root_.map_ne_zero _).mpr (inv_ne_zero hc0)
  rw [heq, v.ord_mul hcne hxne, ord_algebraMap_eq_zero v (inv_ne_zero hc0), zero_add]

include hT in

theorem laurentPrincipalGeneratedByIntegral_of [HasPrincipalDivisors L FF]
    (hq : ∀ y : LaurentSeries A, ι A y ∈ FF → ϖ A y ∈ Fb) :
    LaurentPrincipalGeneratedByIntegral A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb := by
  intro D hD
  obtain ⟨f, hf0, hDf⟩ := Divisor.mem_principal.mp hD
  have hfF : (f : LaurentSeries L) ∈ adjoin L (gensF Γ L) := laurentBaseChange_le_adjoin_gensF Γ L hT f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Dr, hDr, hDr'⟩ := exists_mem_integralPrincipalDivisors_of_mem_adjoin A Γ hq hr hr0
  obtain ⟨Ds, hDs, hDs'⟩ := exists_mem_integralPrincipalDivisors_of_mem_adjoin A Γ hq hs hs0
  have hrF : r ∈ FF := algebra_adjoin_gensF_le Γ L hr
  have hsF : s ∈ FF := algebra_adjoin_gensF_le Γ L hs
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

end ClauseB

end QExpDeuringRed

open QExpDeuringRed in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hdeg : ∀ (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)
      (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) →
      (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≤
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ))
    (hgen : AlgebraicCurve.genusFF (IsLocalRing.ResidueField A)
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    ModularCurve.ReductionInputsQExpModL A Γ := by

  obtain ⟨x, hx, htr, hfinb, hleP⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
      (AlgebraicClosure ℚ) A Γ hT
  obtain rfl : x = jbar Γ (IsLocalRing.ResidueField A) := Subtype.ext hx
  haveI := hfinb
  have hpos : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) {(jbar Γ (IsLocalRing.ResidueField A) :
        qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)})
      (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) := Module.finrank_pos
  have h1 := hleP (jF Γ) (coe_jF Γ)
  haveI : Module.Finite (IntermediateField.adjoin (AlgebraicClosure ℚ)
      {(jF Γ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))})
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    Module.finite_of_finrank_pos (lt_of_lt_of_le hpos h1)
  have h2 := hdeg (jbar Γ (IsLocalRing.ResidueField A)) (jF Γ) rfl (coe_jF Γ)
  have hfin := le_antisymm h2 h1
  have hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ :=
    resHom_mem A Γ hT h2

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (IsLocalRing.ResidueField A) := IsAlgClosed.perfectField _
  haveI : IsCurveOver (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
    obtain ⟨z, hz, hzfin⟩ :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
    exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hz hzfin
  haveI : IsCurveOver (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfinb

  obtain ⟨r, hr⟩ := exists_placeMap A Γ hT hmem hfin hpos hgen
  refine ⟨r, ⟨fun P => ?_, fun y hy hyk hy0 D hD Q => ?_⟩,
    laurentPrincipalGeneratedByIntegral_of A Γ hT fun y hyF => ?_⟩
  · rw [IsCurveOver.deg_eq_one_of_isAlgClosed (K := IsLocalRing.ResidueField A) (r P),
      IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) P]
  · have hres : resF A Γ hT hmem ⟨⟨ι A y, hy⟩, ι_mem_gaussRing A Γ hT hy⟩ =
        ⟨ϖ A y, hyk⟩ := Subtype.ext (resHom_ι A Γ hT hy)
    have hne : resF A Γ hT hmem ⟨⟨ι A y, hy⟩, ι_mem_gaussRing A Γ hT hy⟩ ≠ 0 := by
      rw [hres]; exact fun h => hy0 (congrArg Subtype.val h)
    have := hr ⟨⟨ι A y, hy⟩, ι_mem_gaussRing A Γ hT hy⟩ hne D hD Q
    rwa [hres] at this
  · have h := hmem ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A Γ hT hyF⟩
    rwa [resHom_ι A Γ hT hyF] at h

end

end S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
end P2MW
export P2MW.S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq (solution)
