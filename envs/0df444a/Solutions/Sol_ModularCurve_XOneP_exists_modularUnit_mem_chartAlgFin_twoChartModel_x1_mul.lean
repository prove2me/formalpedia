-- Prove2me | solution 1 for ModularCurve.XOneP.exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/607da54e-d1d3-5446-9b42-156635c0b1d0

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ModularUnit

import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ u u' : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((u : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∧
      ((u' : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹ ∧
      u * u' = (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ^ 12 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  have hmem : (ModularCurve.modularUnitSeries p) ∈ ModularCurve.modularFunctionFieldFull p :=
    ModularCurve.modularFunctionField_le_full p (ModularCurve.modularUnitSeries_mem_modularFunctionField p)
  obtain ⟨hint, hint'⟩ := ModularCurve.modularUnitSeries_mem_chartAlgFin_int p hmem

  have hΓ : CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma0 p := by
    intro γ hγ
    have h0 := CongruenceSubgroup.Gamma1_in_Gamma0 (M * p) hγ
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0 ⊢
    exact (show (p : ℤ) ∣ ((M * p : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans h0
  have hle : ModularCurve.modularFunctionFieldFull p ≤ ModularCurve.x1FunctionField (M * p) := by
    rw [← ModularCurve.modularFunctionFieldFullC_rat]
    exact (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p).trans (ModularCurve.qExpFunctionFieldC_mono ℚ hΓ)

  have hKmem : ∀ x : ↥(ModularCurve.modularFunctionFieldFull p), ModularCurve.coeffEmb L (x : LaurentSeries ℚ) ∈ K := by
    intro x
    rw [hK]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L (hle x.2)
  let θ : ↥(ModularCurve.modularFunctionFieldFull p) →+* ↥K :=
    RingHom.codRestrict ((ModularCurve.coeffEmb L).comp (ModularCurve.modularFunctionFieldFull p).toSubring.subtype) K hKmem
  have hθ : ∀ x, ((θ x : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (x : LaurentSeries ℚ) := fun _ => rfl
  have hθj : θ (ModularCurve.IgusaScheme.jFull p) = j := by
    apply Subtype.ext
    rw [hθ, ModularCurve.IgusaScheme.coe_jFull, hj]

  let θℤ : ↥(ModularCurve.modularFunctionFieldFull p) →ₐ[ℤ] ↥K := θ.toIntAlgHom
  have hmapadj : ∀ x ∈ Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p)),
      θ x ∈ Algebra.adjoin A ({j} : Set ↥K) := by
    intro x hx
    have h1 : θℤ x ∈ (Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))).map θℤ :=
      Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin ℤ ({θℤ (ModularCurve.IgusaScheme.jFull p)} : Set ↥K) ≤ (Algebra.adjoin A ({j} : Set ↥K)).restrictScalars ℤ := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      show θ (ModularCurve.IgusaScheme.jFull p) ∈ Algebra.adjoin A ({j} : Set ↥K)
      rw [hθj]
      exact Algebra.subset_adjoin rfl
    exact h2 h1
  let φ : ↥(Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p))) →+*
      ↥(Algebra.adjoin A ({j} : Set ↥K)) :=
    RingHom.codRestrict (θ.comp (Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set _)).toSubring.subtype) _ (fun x => hmapadj x x.2)
  have hcomp : (algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K)) ↥K).comp φ =
      θ.comp (algebraMap ↥(Algebra.adjoin ℤ ({ModularCurve.IgusaScheme.jFull p} : Set ↥(ModularCurve.modularFunctionFieldFull p)))
        ↥(ModularCurve.modularFunctionFieldFull p)) := by
    ext x
    rfl
  have hI : ∀ {a : ↥(ModularCurve.modularFunctionFieldFull p)},
      a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (ModularCurve.IgusaScheme.jFull p) →
      θ a ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j := by
    intro a ha
    rw [ModularCurve.TwoChart.mem_chartAlg_iff]
    rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at ha
    exact ha.map_of_comp_eq φ θ hcomp

  have hne0 : (⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p)) ≠ 0 := by
    intro h
    exact ModularCurve.modularUnitSeries_ne_zero p (congrArg Subtype.val h)
  let uK : ↥K := θ ⟨ModularCurve.modularUnitSeries p, hmem⟩
  let u'K : ↥K := θ ((p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨ModularCurve.modularUnitSeries p, hmem⟩)⁻¹)
  have huK : uK ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j := hI hint
  have hu'K : u'K ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j := hI hint'
  refine ⟨⟨uK, huK⟩, ⟨u'K, hu'K⟩, ?_, ?_, ?_⟩
  · exact hθ _
  · show ((u'K : ↥K) : LaurentSeries L) = _
    rw [hθ]
    push_cast
    rw [map_mul, map_pow, map_inv₀, map_natCast]
  · apply Subtype.ext
    push_cast
    show θ _ * θ _ = (p : ↥K) ^ 12
    rw [← map_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hne0, mul_one, map_pow, map_natCast]

end S_ModularCurve_XOneP_exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul (solution)
