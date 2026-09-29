-- Prove2me | solution 1 for MeasureTheory.norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b1ad6edc-bfa8-5f94-85a5-03f0f0d11889

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod

set_option autoImplicit false

open MeasureTheory

namespace SUPFT9

open scoped FourierTransform RealInnerProductSpace

lemma continuous_w : Continuous fun t : ℝ => (1 + |t|)⁻¹ ^ 2 :=
  ((continuous_const.add continuous_abs).inv₀
    (fun t => (by have := abs_nonneg t; linarith : (1 : ℝ) + |t| ≠ 0))).pow 2

lemma integral_Ioi_w : ∫ t in Set.Ioi (0 : ℝ), (1 + t)⁻¹ ^ 2 = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun t : ℝ => -(1 + t)⁻¹) (g' := fun t => (1 + t)⁻¹ ^ 2)
    (a := 0) (l := 0) ?_ ?_ ?_ ?_
  · simpa using h
  · exact (((continuous_const.add continuous_id).continuousAt.inv₀ (by norm_num)).neg).continuousWithinAt
  · intro t ht
    have ht' : (1 : ℝ) + t ≠ 0 := by have := Set.mem_Ioi.mp ht; linarith
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
    have h2 := (h1.inv ht').neg
    convert h2 using 1
    · rfl
    · rfl
    · rfl
    field_simp
  · intro t _; positivity
  · have : Filter.Tendsto (fun t : ℝ => (1 + t)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa using this.neg

lemma integral_w : ∫ t : ℝ, (1 + |t|)⁻¹ ^ 2 = 2 := by
  have := integral_comp_abs (f := fun t => (1 + t)⁻¹ ^ 2)
  rw [this, integral_Ioi_w]; norm_num

lemma w_le (η : ℝ) : (1 + |η|)⁻¹ ^ 2 ≤ (1 + η ^ 2)⁻¹ := by
  rw [inv_pow]
  apply inv_anti₀ (by positivity)
  nlinarith [abs_nonneg η, sq_abs η]

lemma integrable_w : Integrable (fun η : ℝ => (1 + |η|)⁻¹ ^ 2) := by
  refine (integrable_inv_one_add_sq).mono' continuous_w.aestronglyMeasurable (ae_of_all _ fun η => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact w_le η

lemma integrable_P (r : ℕ) : Integrable (fun x : Fin r → ℝ => ∏ k, (1 + |x k|)⁻¹ ^ 2) := by
  have := Integrable.fintype_prod (ι := Fin r) (f := fun _ (t : ℝ) => (1 + |t|)⁻¹ ^ 2) (μ := fun _ => volume)
    (fun _ => integrable_w)
  simpa [volume_pi] using this

lemma integral_P (r : ℕ) : ∫ x : Fin r → ℝ, ∏ k, (1 + |x k|)⁻¹ ^ 2 = 2 ^ r := by
  rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => (1 + |t|)⁻¹ ^ 2), integral_w, Fintype.card_fin]

variable {r : ℕ}

lemma mp_toLp : MeasurePreserving (WithLp.toLp 2 : (Fin r → ℝ) → EuclideanSpace ℝ (Fin r)) :=
  PiLp.volume_preserving_toLp (Fin r)
lemma me_toLp : MeasurableEmbedding (WithLp.toLp 2 : (Fin r → ℝ) → EuclideanSpace ℝ (Fin r)) :=
  (MeasurableEquiv.toLp 2 (Fin r → ℝ)).measurableEmbedding
lemma mp_ofLp : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) :=
  PiLp.volume_preserving_ofLp (Fin r)
lemma me_ofLp : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) :=
  (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm.measurableEmbedding

lemma integrable_comp_ofLp {g : (Fin r → ℝ) → ℂ} (hg : Integrable g) :
    Integrable (fun v : EuclideanSpace ℝ (Fin r) => g (WithLp.ofLp v)) :=
  (mp_ofLp.integrable_comp_emb me_ofLp).mpr hg

lemma integrable_comp_ofLp_real {g : (Fin r → ℝ) → ℝ} (hg : Integrable g) :
    Integrable (fun v : EuclideanSpace ℝ (Fin r) => g (WithLp.ofLp v)) :=
  (mp_ofLp.integrable_comp_emb me_ofLp).mpr hg

lemma integral_comp_ofLp_real (g : (Fin r → ℝ) → ℝ) :
    ∫ v : EuclideanSpace ℝ (Fin r), g (WithLp.ofLp v) = ∫ y, g y :=
  mp_ofLp.integral_comp me_ofLp g

lemma fourier_transport (f : (Fin r → ℝ) → ℂ) (w : EuclideanSpace ℝ (Fin r)) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) w =
      ∫ y : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, (WithLp.ofLp w) k * y k : ℝ) : ℂ))) * f y := by
  rw [Real.fourier_eq', ← mp_toLp.integral_comp me_toLp]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [WithLp.ofLp_toLp, PiLp.inner_apply, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  simp only [RCLike.inner_apply, conj_trivial, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

lemma continuous_fourier {F : EuclideanSpace ℝ (Fin r) → ℂ} (hF : Integrable F) : Continuous (𝓕 F) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF

lemma norm_fourierInv_le {G : EuclideanSpace ℝ (Fin r) → ℂ} {B : EuclideanSpace ℝ (Fin r) → ℝ}
    (hG : Integrable G) (hB : Integrable B) (h : ∀ w, ‖G w‖ ≤ B w) (v : EuclideanSpace ℝ (Fin r)) :
    ‖𝓕⁻ G v‖ ≤ ∫ w, B w := by
  rw [Real.fourierInv_eq]
  calc ‖∫ w, 𝐞 ⟪w, v⟫ • G w‖ ≤ ∫ w, ‖𝐞 ⟪w, v⟫ • G w‖ := norm_integral_le_integral_norm _
    _ = ∫ w, ‖G w‖ := by simp_rw [Circle.norm_smul]
    _ ≤ ∫ w, B w := integral_mono hG.norm hB h

end SUPFT9

theorem solution
    {r : ℕ} (f : (Fin r → ℝ) → ℂ) (hf : Continuous f) (hfi : Integrable f) (C : ℝ)
    (hC : ∀ ξ : Fin r → ℝ,
      ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * f x‖ ≤ C * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)
    (x : Fin r → ℝ) :
    ‖f x‖ ≤ 2 ^ r * C := by
  have hFc : Continuous (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) := hf.comp (PiLp.continuous_ofLp 2 _)
  have hFi : Integrable (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) := SUPFT9.integrable_comp_ofLp hfi
  have hbd : ∀ w : EuclideanSpace ℝ (Fin r),
      ‖FourierTransform.fourier (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v)) w‖ ≤
        C * ∏ k, (1 + |(WithLp.ofLp w) k|)⁻¹ ^ 2 := by
    intro w; rw [SUPFT9.fourier_transport]; exact hC _
  have hPi : Integrable (fun w : EuclideanSpace ℝ (Fin r) => C * ∏ k, (1 + |(WithLp.ofLp w) k|)⁻¹ ^ 2) :=
    SUPFT9.integrable_comp_ofLp_real ((SUPFT9.integrable_P r).const_mul C)
  have hFTi : Integrable (FourierTransform.fourier (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v))) :=
    hPi.mono' (SUPFT9.continuous_fourier hFi).aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hinv := hFc.fourierInv_fourier_eq hFi hFTi
  have hx : f x = FourierTransformInv.fourierInv
      (FourierTransform.fourier (fun v : EuclideanSpace ℝ (Fin r) => f (WithLp.ofLp v))) (WithLp.toLp 2 x) := by
    rw [hinv]
  rw [hx]
  calc _ ≤ ∫ w : EuclideanSpace ℝ (Fin r), C * ∏ k, (1 + |(WithLp.ofLp w) k|)⁻¹ ^ 2 :=
        SUPFT9.norm_fourierInv_le hFTi hPi hbd _
    _ = C * ∫ y : Fin r → ℝ, ∏ k, (1 + |y k|)⁻¹ ^ 2 := by
        rw [integral_const_mul, ← SUPFT9.integral_comp_ofLp_real]
    _ = 2 ^ r * C := by rw [SUPFT9.integral_P, mul_comm]

end S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod
end P2MW
export P2MW.S_MeasureTheory_norm_le_two_pow_mul_of_forall_norm_integral_cexp_mul_le_prod (solution)
