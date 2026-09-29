-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3e5f43a9-912c-56c8-b5e7-da8675a00500

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_jqNModC_mem_chartAlgFin_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (g : ↥(chartAlgFin A (↥K) j)),
      (((g : ↥(chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) ∧
      ((g : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0 ∧
      ∃ (k : ℕ) (z : ↥(chartAlgFin A (↥K) j)), g * z = algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ^ k := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩

  have hmem : ModularCurve.modularUnitSeries q ∈ ModularCurve.modularFunctionFieldFull q :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q
  obtain ⟨hu, hw⟩ := ModularCurve.modularUnitSeries_mem_chartAlgFin_int q hmem

  have hΦmem : ∀ x : ↥(ModularCurve.modularFunctionFieldFull q), ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (x : LaurentSeries ℚ)) ∈ K := by
    intro x
    rw [hK]
    exact ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
      L q (q * ℓ) ((q * ℓ) ^ 2 * M') ⟨ℓ * M', by ring⟩ _ (x : LaurentSeries ℚ) x.2
  let Φ : ↥(ModularCurve.modularFunctionFieldFull q) →+* ↥K :=
    { toFun := fun x => ⟨_, hΦmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hΦ : ∀ x : ↥(ModularCurve.modularFunctionFieldFull q), ((Φ x : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (x : LaurentSeries ℚ)) := fun _ => rfl
  let Φₐ : ↥(ModularCurve.modularFunctionFieldFull q) →ₐ[ℤ] ↥K := Φ.toIntAlgHom

  set j' : ↥K := Φ (ModularCurve.IgusaScheme.jFull q) with hj'def
  have hj'coe : ((j' : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ) := by
    rw [hj'def, hΦ, ModularCurve.IgusaScheme.coe_jFull]
    show ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffMap (algebraMap ℚ L) (ModularCurve.jqModC ℚ)) = _
    rw [ModularCurve.coeffMap_jqModC]
    rfl
  have hj'C : j' ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := by
    have h1lt : 1 < q * ℓ := by nlinarith [(Fact.out : q.Prime).two_le, (Fact.out : ℓ.Prime).two_le]
    have hmemK : ModularCurve.jqNModC L (q * ℓ) ∈ K := by rw [← hj'coe]; exact j'.2
    have := ModularCurve.jqNModC_mem_chartAlgFin_of_mem L K A j hj (q * ℓ) h1lt hmemK
    convert this using 1
    exact Subtype.ext hj'coe

  have step1 : ∀ y : ↥(ModularCurve.modularFunctionFieldFull q), y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull q) (ModularCurve.IgusaScheme.jFull q) →
      (Φ y : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg ℤ (↥K) {j'} := by
    intro y hy
    have hle : (Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull q} : Set ↥(ModularCurve.modularFunctionFieldFull q))).map Φₐ ≤
        Algebra.adjoin ℤ ({j'} : Set ↥K) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_singleton_iff.mpr (by rw [hj'def]; rfl)))
    let φ₁ : ↥(Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull q} : Set ↥(ModularCurve.modularFunctionFieldFull q))) →+* ↥(Algebra.adjoin ℤ ({j'} : Set ↥K)) :=
      (Subalgebra.inclusion hle).toRingHom.comp (Φₐ.subalgebraMap _).toRingHom
    have hy' : IsIntegral ↥(Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull q} : Set ↥(ModularCurve.modularFunctionFieldFull q))) y := hy
    exact hy'.map_of_comp_eq φ₁ Φ (by ext x; rfl)
  have step2 : AlgebraicCurve.TwoChartIntegralModel.chartAlg ℤ (↥K) ({j'} : Set ↥K) ≤
      (AlgebraicCurve.TwoChartIntegralModel.chartAlg A (↥K) ({j'} : Set ↥K)).restrictScalars ℤ :=
    AlgebraicCurve.TwoChartIntegralModel.chartAlg_le_restrictScalars ℤ (↥K) A {j'}
  have step3 : ∀ y : ↥K, y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlg A (↥K) ({j'} : Set ↥K) → y ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := by
    intro y hy
    have hy' : IsIntegral ↥(Algebra.adjoin A ({j'} : Set ↥K)) y := hy
    have hj'' : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)) j' := hj'C
    let R₁ := ↥(Algebra.adjoin A ({j} : Set ↥K))
    let S₁ : Subalgebra R₁ ↥K := Algebra.adjoin R₁ ({j'} : Set ↥K)
    haveI : Algebra.IsIntegral R₁ ↥S₁ :=
      Algebra.IsIntegral.adjoin (fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact hj'')
    have hle : (Algebra.adjoin A ({j'} : Set ↥K)).toSubring ≤ (S₁.restrictScalars A).toSubring := by
      intro x hx
      exact (Algebra.adjoin_le (S := S₁.restrictScalars A) (by
        intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact Algebra.subset_adjoin (Set.mem_singleton _))) hx
    have hyS : IsIntegral ↥S₁ y := hy'.map_of_comp_eq (Subring.inclusion hle) (RingHom.id ↥K) (by ext; rfl)
    exact isIntegral_trans (R := R₁) y hyS
  have hinC : ∀ y : ↥(ModularCurve.modularFunctionFieldFull q), y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull q) (ModularCurve.IgusaScheme.jFull q) →
      (Φ y : ↥K) ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := fun y hy => step3 _ (step2 (step1 y hy))

  set uF : ↥(ModularCurve.modularFunctionFieldFull q) := ⟨ModularCurve.modularUnitSeries q, hmem⟩ with huF
  set wF : ↥(ModularCurve.modularFunctionFieldFull q) := (q : ↥(ModularCurve.modularFunctionFieldFull q)) ^ 12 * uF⁻¹ with hwF
  refine ⟨⟨Φ uF, hinC uF hu⟩, ?_, ?_, ?_⟩
  · exact hΦ uF
  · intro h0
    have h1 := congrArg (fun z : ↥K => (z : LaurentSeries L).coeff ((q * ℓ : ℕ) * (1 - (q : ℤ)))) h0
    simp only [hΦ, ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
    have hmon := (ModularCurve.isMonicOfOrder_modularUnitSeries q).qExpand (q * ℓ)
    have h2 : (ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q))).coeff
        ((q * ℓ : ℕ) * (1 - (q : ℤ))) = 1 := by
      have h3 : ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) =
          ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ (q * ℓ) (ModularCurve.modularUnitSeries q)) := by
        show _ = ModularCurve.coeffMap (algebraMap ℚ L) _
        rw [ModularCurve.coeffMap_qExpand]; rfl
      rw [h3, ModularCurve.coeffEmb_coeff, hmon.coeff_self, map_one]
    rw [h2] at h1
    exact one_ne_zero h1
  ·
    have hq0 : (q : A) ≠ 0 := by
      intro h
      have := congrArg (algebraMap A L) h
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
    have hϖ0 : ϖ ≠ 0 := by
      intro h
      apply hq0
      have : (q : A) ∈ maximalIdeal A := hAq
      rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl] at this
      exact Ideal.mem_bot.mp this
    have hirr : Irreducible ϖ := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hϖ
    obtain ⟨v, uA, hqv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (pow_ne_zero 12 hq0) hirr
    refine ⟨v, ⟨Φ wF, hinC wF hw⟩ * algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ((uA⁻¹ : Aˣ) : A), ?_⟩
    have huF0 : uF ≠ 0 := by
      intro h; have := congrArg Subtype.val h
      exact ModularCurve.modularUnitSeries_ne_zero q this
    have hprod : uF * wF = ((q : ℕ) : ↥(ModularCurve.modularFunctionFieldFull q)) ^ 12 := by
      rw [hwF, mul_comm, mul_assoc, inv_mul_cancel₀ huF0, mul_one]
    have hgw : (⟨Φ uF, hinC uF hu⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) * ⟨Φ wF, hinC wF hw⟩ = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ((q : A) ^ 12) := by
      apply Subtype.ext
      show Φ uF * Φ wF = ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ((q : A) ^ 12) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K)
      rw [← map_mul, hprod, map_pow, map_natCast, Subalgebra.coe_algebraMap, map_pow, map_natCast]
    rw [← mul_assoc, hgw, hqv, map_mul, map_pow, mul_comm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (uA : A)), mul_assoc, ← map_mul,
      Units.mul_inv, map_one, mul_one]

end S_ModularCurve_FullLevel_AuxLevel_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_coe_eq_qExpand_modularUnitSeries_mem_chartAlgFin_mul_eq_pow (solution)
