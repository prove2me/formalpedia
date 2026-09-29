-- Prove2me | solution 1 for ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e9b0431f-39ab-55bc-ab07-87d36e677a34

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_coeff_coeff_swapBivar
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_Polynomial_exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j' : ↥K) (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) [Fact (j' ≠ 0)] :
    j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ∧
    j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j' ∧
    (∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j', ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j,
      (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, s = 1 + j⁻¹ * a) ∧ s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ∧
    (∀ y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j, ∃ s ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j',
      (∃ a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j', s = 1 + j'⁻¹ * a) ∧ s * y ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j') := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  have hsymE : ModularCurve.EvalSymm data.Φ := ModularCurve.ModularPolynomialData.evalSymm_of_one_lt p hp.one_lt data
  have hswap : ModularCurve.swapBivar data.Φ = data.Φ := ModularCurve.swapBivar_eq_of_evalSymm hsymE
  have hsym : ∀ i k, (data.Φ.coeff i).coeff k = (data.Φ.coeff k).coeff i := by
    intro i k
    have := ModularCurve.coeff_coeff_swapBivar data.Φ i k
    rw [hswap] at this
    exact this.symm
  have hdeg : data.Φ.natDegree = p + 1 := by rw [data.natDegree_eq, ModularCurve.dedekindPsi_prime hp]
  let ΦA : Polynomial (Polynomial A) := data.Φ.map (Polynomial.mapRingHom (algebraMap ℤ A))
  have hmonA : ΦA.Monic := data.monic.map _
  have hdegA : ΦA.natDegree = p + 1 := by rw [data.monic.natDegree_map, hdeg]
  have hsymA : ∀ i k, (ΦA.coeff i).coeff k = (ΦA.coeff k).coeff i := by
    intro i k
    simp only [ΦA, Polynomial.coeff_map, Polynomial.coe_mapRingHom, hsym i k]
  obtain ⟨h, hh⟩ := Polynomial.exists_isIntegral_adjoin_inv_of_bivariate_eq_zero_of_monic_of_symm A ↥K p ΦA hmonA hdegA hsymA

  have hval : ∀ (a b : ↥K), ((ΦA.eval₂ (Polynomial.eval₂RingHom (algebraMap A ↥K) a) b : ↥K) : LaurentSeries L)
        = data.Φ.eval₂ (Polynomial.aeval (a : LaurentSeries L) : Polynomial ℤ →ₐ[ℤ] LaurentSeries L).toRingHom (b : LaurentSeries L) := by
    intro a b
    have hΦAdef : ΦA = data.Φ.map (Polynomial.mapRingHom (algebraMap ℤ A)) := rfl
    have e := Polynomial.hom_eval₂ ΦA (Polynomial.eval₂RingHom (algebraMap A ↥K) a) (algebraMap ↥K (LaurentSeries L)) b
    have hcomp : (((algebraMap ↥K (LaurentSeries L)).comp (Polynomial.eval₂RingHom (algebraMap A ↥K) a)).comp
        (Polynomial.mapRingHom (algebraMap ℤ A))) = (Polynomial.aeval (a : LaurentSeries L) : Polynomial ℤ →ₐ[ℤ] LaurentSeries L).toRingHom := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
    calc (((ΦA.eval₂ (Polynomial.eval₂RingHom (algebraMap A ↥K) a) b : ↥K) : LaurentSeries L))
          = ΦA.eval₂ ((algebraMap ↥K (LaurentSeries L)).comp (Polynomial.eval₂RingHom (algebraMap A ↥K) a)) (algebraMap ↥K (LaurentSeries L) b) := e
      _ = data.Φ.eval₂ (((algebraMap ↥K (LaurentSeries L)).comp (Polynomial.eval₂RingHom (algebraMap A ↥K) a)).comp
            (Polynomial.mapRingHom (algebraMap ℤ A))) (algebraMap ↥K (LaurentSeries L) b) := by rw [hΦAdef, Polynomial.eval₂_map]
      _ = _ := by rw [hcomp]; rfl
  have hemb : ∀ (x y : LaurentSeries ℚ), data.Φ.eval₂ (Polynomial.aeval (ModularCurve.coeffEmb L x) : Polynomial ℤ →ₐ[ℤ] LaurentSeries L).toRingHom
        (ModularCurve.coeffEmb L y) = ModularCurve.coeffEmb L (data.Φ.eval₂ (Polynomial.aeval x : Polynomial ℤ →ₐ[ℤ] LaurentSeries ℚ).toRingHom y) := by
    intro x y
    rw [Polynomial.hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
  have hΦ0 : data.Φ.eval₂ (Polynomial.aeval ModularCurve.jq : Polynomial ℤ →ₐ[ℤ] LaurentSeries ℚ).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 :=
    data.eval_eq_zero
  have heq : ΦA.eval₂ (Polynomial.eval₂RingHom (algebraMap A ↥K) j) j' = 0 := by
    apply Subtype.ext
    rw [hval, hj, hj', hemb, hΦ0, map_zero]; rfl
  have heq' : ΦA.eval₂ (Polynomial.eval₂RingHom (algebraMap A ↥K) j') j = 0 := by
    apply Subtype.ext
    rw [hval, hj, hj', hemb, ← hsymE, hΦ0, map_zero]; rfl

  have hint : ∀ (a b : ↥K), ΦA.eval₂ (Polynomial.eval₂RingHom (algebraMap A ↥K) a) b = 0 →
      IsIntegral ↥(Algebra.adjoin A ({a} : Set ↥K)) b := by
    intro a b hab
    let aS : ↥(Algebra.adjoin A ({a} : Set ↥K)) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
    refine ⟨ΦA.map (Polynomial.aeval aS).toRingHom, hmonA.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap ↥(Algebra.adjoin A ({a} : Set ↥K)) ↥K).comp (Polynomial.aeval aS).toRingHom
        = Polynomial.eval₂RingHom (algebraMap A ↥K) a := by
      refine Polynomial.ringHom_ext ?_ ?_
      · intro r
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_C, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_C]
        rfl
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_X]
        rfl
    rw [hc]
    exact hab
  have h1 : j' ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A ↥K j := hint j j' heq
  have h2 : j ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A ↥K j' := hint j' j heq'

  have hJt : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hJ't : Transcendental A j' := by
    intro halg
    haveI : Algebra.IsAlgebraic A ↥(Algebra.adjoin A ({j'} : Set ↥K)) :=
      (Subalgebra.isAlgebraic_iff _).mp (Algebra.isAlgebraic_adjoin_singleton_iff.mpr halg)
    exact hJt ((hint j' j heq').isAlgebraic.restrictScalars A)

  have hne : ∀ (a : ↥K), Transcendental A a → (1 + a⁻¹ * Polynomial.aeval a⁻¹ h) ≠ 0 := by
    intro a ha h0
    have ha0 : a ≠ 0 := fun hz => ha (hz ▸ isAlgebraic_zero)
    have hroot : Polynomial.aeval a⁻¹ (1 + Polynomial.X * h) = 0 := by
      rw [map_add, map_one, map_mul, Polynomial.aeval_X]; exact h0
    have hne' : (1 + Polynomial.X * h : Polynomial A) ≠ 0 := by
      intro hz
      have := congrArg (fun q : Polynomial A => q.coeff 0) hz
      simp at this
    have halg : IsAlgebraic A a⁻¹ := ⟨_, hne', hroot⟩
    exact ha (IsAlgebraic.inv_iff.mp halg)
  have hJ0 : j ≠ 0 := Fact.out
  have hJ'0 : j' ≠ 0 := Fact.out

  refine ⟨h1, h2, ?_, ?_⟩
  · refine AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem A ↥K j j'
      ⟨Polynomial.aeval j⁻¹ h, Polynomial.aeval_mem_adjoin_singleton A _,
        (1 + j⁻¹ * Polynomial.aeval j⁻¹ h)⁻¹, inv_mul_cancel₀ (hne _ hJt), ?_⟩
    exact hh _ _ _ hJ0 hJ'0 heq (inv_mul_cancel₀ (hne _ hJt))
  · refine AlgebraicCurve.TwoChartIntegralModel.forall_mem_chartAlgInf_exists_one_add_mul_and_mul_mem A ↥K j' j
      ⟨Polynomial.aeval j'⁻¹ h, Polynomial.aeval_mem_adjoin_singleton A _,
        (1 + j'⁻¹ * Polynomial.aeval j'⁻¹ h)⁻¹, inv_mul_cancel₀ (hne _ hJ't), ?_⟩
    exact hh _ _ _ hJ'0 hJ0 heq' (inv_mul_cancel₀ (hne _ hJ't))

end S_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand
end P2MW
export P2MW.S_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand (solution)
