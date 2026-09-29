-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/289dbb03-3114-51c1-b21d-9685d255d55d

import Mathlib
import Theorems.Thm_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv

p2m_open "NumberField P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv.NumberField NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv.NumberField.mixedEmbedding"
p2m_open_scoped "FourierTransform SchwartzMap NumberField P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv.NumberField NumberField.InfinitePlace.NumberField Classical"

namespace NumberField
p2m_export "NumberField" "mixedEmbedding.norm_apply mixedEmbedding mixedEmbedding.mixedSpace InfinitePlace mixedEmbedding.norm mixedEmbedding.norm_ne_zero_iff mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "norm_real normAtPlace mixedSpace normAtPlace_apply_of_isReal normAtPlace_apply_of_isComplex exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers"
p2m_open "NumberField.mixedEmbedding NumberField"

theorem abs_det_mulLeft (K : Type*) [Field K] [NumberField K] (a : mixedSpace K) :
    |LinearMap.det (LinearMap.mulLeft ℝ a)| = mixedEmbedding.norm a := by
  classical
  have h1 : (LinearMap.mulLeft ℝ a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.prodMap
        (LinearMap.pi fun w ↦ (LinearMap.mulLeft ℝ (a.1 w)).comp (LinearMap.proj w))
        (LinearMap.pi fun w ↦ ((LinearMap.mulLeft ℂ (a.2 w)).restrictScalars ℝ).comp
          (LinearMap.proj w)) := by
    refine LinearMap.ext fun x ↦ Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_) <;> rfl
  rw [h1, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_restrictScalars, LinearMap.det_ring, LinearMap.mulLeft_apply, mul_one,
    Algebra.norm_complex_apply]
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_apply_of_isReal w.prop, mult_isReal, pow_one, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [normAtPlace_apply_of_isComplex w.prop, mult_isComplex, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]

theorem vectorFourierIntegral_comp_mul_inv (K : Type*) [Field K] [NumberField K]
    (g : mixedSpace K → ℂ) (hg : Continuous g) (a : (mixedSpace K)ˣ) (w : mixedSpace K) :
    VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume (Algebra.traceForm ℝ (mixedSpace K))
        (fun x ↦ g (↑a⁻¹ * x)) w
      = ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) *
        VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume (Algebra.traceForm ℝ (mixedSpace K))
          g (↑a * w) := by
  classical
  set f : mixedSpace K →ₗ[ℝ] mixedSpace K := LinearMap.mulLeft ℝ (a : mixedSpace K) with hf_def
  have hdet : |LinearMap.det f| = mixedEmbedding.norm (a : mixedSpace K) := abs_det_mulLeft K _
  have hnorm0 : mixedEmbedding.norm (a : mixedSpace K) ≠ 0 := by
    rw [mixedEmbedding.norm_ne_zero_iff]
    intro w hw
    have : normAtPlace w ((a⁻¹ : (mixedSpace K)ˣ) * a : mixedSpace K) = 1 := by simp
    rw [map_mul, hw, mul_zero] at this
    exact zero_ne_one this
  have hdet0 : LinearMap.det f ≠ 0 := fun h ↦ hnorm0 (by rw [← hdet, h, abs_zero])

  set F : mixedSpace K → ℂ := fun x ↦
    (𝐞 (-(Algebra.traceForm ℝ (mixedSpace K) x w)) : ℂ) • g (↑a⁻¹ * x) with hF_def
  have hFc : Continuous F := by
    have h1 : Continuous fun x : mixedSpace K ↦ Algebra.traceForm ℝ (mixedSpace K) x w :=
      ((Algebra.traceForm ℝ (mixedSpace K)).flip w).continuous_of_finiteDimensional
    have h2 : Continuous fun x : mixedSpace K ↦ (𝐞 (-(Algebra.traceForm ℝ (mixedSpace K) x w)) : ℂ) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp h1.neg)
    exact h2.smul (hg.comp (continuous_const.mul continuous_id))

  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (MeasureTheory.volume : MeasureTheory.Measure (mixedSpace K)) hdet0
  have hcv : ∫ y, F (f y) = |LinearMap.det f|⁻¹ • ∫ x, F x := by
    rw [← MeasureTheory.integral_map f.continuous_of_finiteDimensional.aemeasurable
      hFc.aestronglyMeasurable, hmap, MeasureTheory.integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  have hint : ∫ x, F x = |LinearMap.det f| • ∫ y, F (f y) := by
    rw [hcv, smul_smul, mul_inv_cancel₀ (abs_ne_zero.mpr hdet0), one_smul]

  rw [VectorFourier.fourierIntegral, VectorFourier.fourierIntegral]
  change ∫ x, F x = _
  rw [hint, hdet, Complex.real_smul]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [hF_def, hf_def, LinearMap.mulLeft_apply, Units.inv_mul_cancel_left, Algebra.traceForm_apply,
    Circle.smul_def, smul_eq_mul]
  congr 4
  ring_nf

end NumberField.mixedEmbedding

theorem solution
    (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (g : 𝓢(NumberField.mixedEmbedding.mixedSpace K, ℂ))
        (a : (NumberField.mixedEmbedding.mixedSpace K)ˣ),
        1 ≤ NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K) →
          Summable (fun ξ : 𝓞 K ↦ ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K))
              (fun x ↦ g (↑a⁻¹ * x)) (NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K))
              (fun x ↦ g (↑a⁻¹ * x)) (NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖
            ≤ C * (s.sup (schwartzSeminormFamily ℝ (NumberField.mixedEmbedding.mixedSpace K) ℂ)) g *
                (NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K))⁻¹ ^ N := by
  classical
  obtain ⟨s, C, hC, hS2⟩ :=
    NumberField.mixedEmbedding.exists_bound_tsum_norm_vectorFourierIntegral_mul_ringOfIntegers K (N + 1)
  refine ⟨s, C, hC, fun g a ha ↦ ?_⟩
  have hpos : 0 < NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K) :=
    one_pos.trans_le ha
  obtain ⟨hsum, hb⟩ := hS2 g (a : NumberField.mixedEmbedding.mixedSpace K) ha
  simp_rw [NumberField.mixedEmbedding.vectorFourierIntegral_comp_mul_inv K g g.continuous a, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨hsum.mul_left _, ?_⟩
  rw [tsum_mul_left]
  calc NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K) *
        ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
              (Algebra.traceForm ℝ (NumberField.mixedEmbedding.mixedSpace K)) g
              ((a : NumberField.mixedEmbedding.mixedSpace K) * NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖
      ≤ NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K) *
          (C * (s.sup (schwartzSeminormFamily ℝ (NumberField.mixedEmbedding.mixedSpace K) ℂ)) g *
            (NumberField.mixedEmbedding.norm (a : NumberField.mixedEmbedding.mixedSpace K))⁻¹ ^ (N + 1)) :=
        mul_le_mul_of_nonneg_left hb hpos.le
    _ = _ := by
        rw [pow_succ]
        field_simp

end S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_vectorFourierIntegral_comp_mul_inv (solution)
