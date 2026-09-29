-- Prove2me | solution 1 for ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bba6c68a-8095-58f7-afa7-4055f48d787e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials
import Theorems.Thm_AlgebraicCurve_mem_regularDiffs_iff
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential
open scoped MatrixGroups

noncomputable section

namespace IntH

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pow' (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : v.ord (-f) = v.ord (-1) + v.ord f := by
    rw [← v.ord_mul (by norm_num) hf, neg_one_mul]
  have h2 : v.ord ((-1 : F)) = 0 := by
    have := v.ord_zpow (-1 : F) 2
    norm_num at this
    linarith
  rw [h1, h2, zero_add]

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (ha : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) (ha0 : (a : F) ≠ 0) : 0 < v.ord (a : F) := by
  by_contra hle
  push Not at hle
  have h0 : 0 ≤ v.ord (a : F) := v.ord_nonneg_of_mem a.2
  have heq : v.ord (a : F) = 0 := le_antisymm hle h0
  have hinv : (a : F)⁻¹ ∈ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg (inv_ne_zero ha0), v.ord_inv, heq, neg_zero]
  have hunit : IsUnit a := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(a : F)⁻¹, hinv⟩, ?_⟩
    ext
    simp [mul_inv_cancel₀ ha0]
  exact (IsLocalRing.mem_maximalIdeal _).mp ha hunit

theorem exists_value [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    ∃ c : K, f - algebraMap K F c = 0 ∨ 0 < v.ord (f - algebraMap K F c) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨f, hf⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
    exact sub_self _
  have hcoe : ((⟨f, hf⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) =
      f - algebraMap K F c := by
    push_cast
    rw [v.coe_algebraMap]
  by_cases h0 : f - algebraMap K F c = 0
  · exact Or.inl h0
  · right
    have := ord_pos_of_mem_maximalIdeal v hmem (by rw [hcoe]; exact h0)
    rwa [hcoe] at this

end Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_bound [PerfectField K] [CharZero K] (J : F) (hDJ : D K F J ≠ 0)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({J} : Set F)) F]
    (x : F) (hx0 : x ≠ 0) (hreg : ∀ v : Place K F, 0 ≤ v.ordDiff (x • D K F J))
    (v : Place K F) {g : F} (hg : v.ord g ≠ 0) (hDg : D K F g = D K F J) :
    1 - v.ord g ≤ v.ord x := by
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({J} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  have h := hreg v
  rw [← hDg] at h
  rw [Place.ordDiff_smul_of_perfectField J v hx0 (by rw [hDg]; exact hDJ), Place.ordDiff_D_eq_ord_sub_one J v hg] at h
  omega

theorem ram_profile (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (jbar : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) :
    v.ord jbar ≤ 3 ∧ v.ord (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ≤ 2 ∧
      (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 → v.ord (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) a) ≤ 1) := by
  have key : ∀ (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))),
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) = E →
      ∀ (y : ↥E), (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) → ∀ P : Place (AlgebraicClosure ℚ) ↥E,
        P.ord y ≤ 3 ∧ P.ord (y - algebraMap (AlgebraicClosure ℚ) ↥E 1728) ≤ 2 ∧
          (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 → P.ord (y - algebraMap (AlgebraicClosure ℚ) ↥E a) ≤ 1) := by
    rintro E rfl y hy P
    have h := ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
      M Γ hΓ₁ y hy P
    refine ⟨h.1, ?_, h.2.2⟩
    rw [map_ofNat]
    exact h.2.1
  exact key _ (ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) Γ) jbar hjbar v

end IntH

open IntH in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (jbar : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hx : x • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) jbar ∈
      regularDifferentials (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
        (x ^ 6 * jbar ^ 4 * (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^ 3) ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
        (x ^ (2 * Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) *
          jbar ^ (Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) + 1) *
          (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^
            Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := by
  classical

  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ Γ := hΓ₁ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  obtain ⟨x₀, hx₀, htr, hFD⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (AlgebraicClosure ℚ) Γ hT
  have hxj : x₀ = jbar := Subtype.ext (hx₀.trans hjbar.symm)
  subst hxj
  haveI := hFD
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hFD
  haveI hEFT : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hFD
  haveI hALG : Algebra.IsAlgebraic ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := Algebra.IsAlgebraic.of_finite _ _
  haveI hSEP : Algebra.IsSeparable ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := inferInstance
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := IsCurveOver.hasPrincipalDivisors
  have hDJ : D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) x₀ ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental (AlgebraicClosure ℚ) x₀ htr
  set ψ : ℕ := Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) with hψdef
  set J : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := x₀ with hJdef
  have hψpos : 0 < ψ := Module.finrank_pos
  have hJ0 : J ≠ 0 := by
    intro h
    apply hDJ
    rw [h, map_zero]

  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, ?_⟩
    · rw [zero_pow (by norm_num), zero_mul, zero_mul]; exact isIntegral_zero
    · rw [zero_pow (by omega), zero_mul, zero_mul]; exact isIntegral_zero

  have hreg : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), 0 ≤ v.ordDiff (x • D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) J) := by
    have h1 : x • D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) J ∈ regularDiffs (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := by
      rw [AlgebraicCurve.regularDiffs_eq_regularDifferentials]; exact hx
    exact (AlgebraicCurve.mem_regularDiffs_iff (J : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) _).mp h1

  obtain ⟨S, hS, hsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed (AlgebraicClosure ℚ) J htr hFD
  have hwidth : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v.ord J < 0 → -v.ord J ≤ (ψ : ℤ) := by
    intro v hv
    rw [hψdef, ← hsum]
    exact Finset.single_le_sum (f := fun w => -w.ord J)
      (fun w hw => by have := (hS w).mp hw; show (0 : ℤ) ≤ -w.ord J; omega) ((hS v).mpr hv)
  have hpole : ∃ v₀ : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v₀.ord J < 0 := by
    by_contra hno
    push Not at hno
    have hSe : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact absurd ((hS v).mp hv) (not_lt.mpr (hno v))
    rw [hSe, Finset.sum_empty] at hsum
    have h' : (ψ : ℤ) = 0 := by rw [hψdef]; exact hsum.symm
    omega
  obtain ⟨v₀, hv₀⟩ := hpole

  have hram := fun v => IntH.ram_profile M Γ hΓ₁ J hjbar v
  have hJne1728 : J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := ord_algebraMap v₀ (c := (1728 : (AlgebraicClosure ℚ))) (by norm_num)
    rw [← h] at this
    omega

  have h1728_0 : v₀.ord (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = 0 := ord_algebraMap v₀ (by norm_num)
  have hordJsub_of_pos : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), 0 < v.ord J → v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = 0 := by
    intro v hv
    have hc : v.ord (-(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) = 0 := by rw [ord_neg]; exact ord_algebraMap v (by norm_num)
    have := v.ord_add_eq_of_lt (f := -(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) (g := J)
      (neg_ne_zero.mpr (by rw [Ne, map_eq_zero]; norm_num)) hJ0 (by rw [hc]; exact hv)
    rw [hc] at this
    rwa [sub_eq_add_neg, add_comm]
  have hordJsub_of_neg : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v.ord J < 0 → v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = v.ord J := by
    intro v hv
    have hc : v.ord (-(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) = 0 := by rw [ord_neg]; exact ord_algebraMap v (by norm_num)
    have := v.ord_add_eq_of_lt (f := J) (g := -(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) hJ0
      (neg_ne_zero.mpr (by rw [Ne, map_eq_zero]; norm_num)) (by rw [hc]; exact hv)
    rwa [← sub_eq_add_neg] at this
  have hordJ_of_sub_pos : ∀ (v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) (c : (AlgebraicClosure ℚ)), c ≠ 0 → 0 < v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) →
      v.ord J = 0 := by
    intro v c hc hv
    have h1 : v.ord (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) = 0 := ord_algebraMap v hc
    have hne : J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c ≠ 0 := by
      intro h; rw [h, v.ord_zero] at hv; exact lt_irrefl _ hv
    have := v.ord_add_eq_of_lt (f := algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) (g := J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c)
      (by rw [Ne, map_eq_zero]; exact hc) hne (by rw [h1]; exact hv)
    rw [h1, add_sub_cancel] at this
    exact this

  have hDsub : ∀ c : (AlgebraicClosure ℚ), D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) = D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) J := by
    intro c
    rw [map_sub, Derivation.map_algebraMap, sub_zero]

  have hfinite : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v.ord J = 0 →
      (0 ≤ v.ord x ∧ v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = 0) ∨
      (∃ a : ℤ, 0 < a ∧ a ≤ 2 ∧ v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = a ∧ 1 - a ≤ v.ord x) := by
    intro v hvJ
    have hJmem : J ∈ v.toValuationSubring := by rw [v.mem_iff_ord_nonneg hJ0, hvJ]
    obtain ⟨c, hc⟩ := exists_value v hJmem
    have hcpos : 0 < v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) := by
      rcases hc with hc | hc
      · exfalso
        rw [sub_eq_zero] at hc
        have := ord_algebraMap v₀ (c := c) (by rintro rfl; rw [map_zero] at hc; exact hJ0 hc)
        rw [← hc] at this
        omega
      · exact hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hcpos
      omega
    by_cases hc1728 : c = 1728
    · subst hc1728
      right
      refine ⟨v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728), hcpos, ?_, rfl, ?_⟩
      · exact (hram v).2.1
      · exact IntH.ord_bound J hDJ x hx0 hreg v hcpos.ne' (hDsub 1728)
    · left
      have h1 : v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) = 1 := by
        have hle := (hram v).2.2 c hc0 hc1728
        omega
      have hb := IntH.ord_bound J hDJ x hx0 hreg v (g := J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) (by rw [h1]; norm_num) (hDsub c)
      rw [h1] at hb
      refine ⟨by omega, ?_⟩

      have hcc : v.ord (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) (c - 1728)) = 0 := ord_algebraMap v (sub_ne_zero.mpr hc1728)
      have := v.ord_add_eq_of_lt (f := algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) (c - 1728)) (g := J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c)
        (by rw [Ne, map_eq_zero]; exact sub_ne_zero.mpr hc1728)
        (by intro h; rw [h, v.ord_zero] at hcpos; exact lt_irrefl _ hcpos) (by rw [hcc]; exact hcpos)
      rw [hcc] at this
      rw [← this, map_sub]
      congr 1
      ring
  refine ⟨?_, ?_⟩
  ·
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := (AlgebraicClosure ℚ)) (F := ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) J htr _ ?_
    intro v hvJ
    have hne : x ^ 6 * J ^ 4 * (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728)
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    rcases hvJ.lt_or_eq with hpos | hzero
    ·
      have ha3 : v.ord J ≤ 3 := (hram v).1
      have hb := IntH.ord_bound J hDJ x hx0 hreg v hpos.ne' rfl
      rw [hordJsub_of_pos v hpos]
      push_cast
      nlinarith
    · rcases hfinite v hzero.symm with ⟨hx', h1728'⟩ | ⟨a, ha0, ha2, h1728', hb⟩
      · rw [← hzero, h1728']; push_cast; nlinarith
      · rw [← hzero, h1728']; push_cast; nlinarith
  ·
    have htr' : Transcendental (AlgebraicClosure ℚ) J⁻¹ := by
      intro halg
      exact htr (by simpa using halg.inv)
    have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) = IntermediateField.adjoin (AlgebraicClosure ℚ) ({J} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) J)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have h1 := IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (J⁻¹)
        have h2 : (J⁻¹)⁻¹ ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := inv_mem h1
        rwa [inv_inv] at h2
    haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := by
      rw [hadj]; exact hFD
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := (AlgebraicClosure ℚ)) (F := ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) J⁻¹ htr' _ ?_
    intro v hvJinv
    rw [v.ord_inv] at hvJinv
    have hvJ : v.ord J ≤ 0 := by omega
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    rcases hvJ.lt_or_eq with hneg | hzero
    ·
      have hw := hwidth v hneg
      have hb := IntH.ord_bound J hDJ x hx0 hreg v hneg.ne rfl
      rw [hordJsub_of_neg v hneg]
      push_cast
      nlinarith
    · rcases hfinite v hzero with ⟨hx', h1728'⟩ | ⟨a, ha0, ha2, h1728', hb⟩
      · rw [hzero, h1728']; push_cast; nlinarith
      · rw [hzero, h1728']; push_cast; nlinarith

end

end S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC (solution)
