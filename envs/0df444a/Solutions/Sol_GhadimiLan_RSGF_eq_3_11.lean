-- Prove2me | solution 1 for GhadimiLan.RSGF.eq_3_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:56:33.065825+00:00
-- url     : https://prove2.me/submissions/46ed1831-bfc0-4486-affd-8cd72f2e8fda

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem glr_descent_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (x v : E) (σ : ℝ) (hσ : |σ| = 1) :
    σ * (f (x + v) - f x - fderiv ℝ f x v) ≤ L / 2 * ‖v‖ ^ 2 := by
  set d := fderiv ℝ f x v with hd
  set φ : ℝ → ℝ := fun t => f (x + t • v) with hφ
  have hder : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ f (x + t • v) v) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hdiff (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
  set ψ : ℝ → ℝ := fun t => σ * (φ t - φ 0 - t * d) - L / 2 * t ^ 2 * ‖v‖ ^ 2 with hψ
  have hψder : ∀ t : ℝ, HasDerivAt ψ (σ * (fderiv ℝ f (x + t • v) v - d) - L * t * ‖v‖ ^ 2) t := by
    intro t
    have a1 := ((hder t).sub_const (φ 0)).sub ((hasDerivAt_id t).mul_const d)
    have a2 := a1.const_mul σ
    have a3 := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
    have h2 := a2.sub a3
    exact h2.congr_deriv (by rw [show (2:ℕ) - 1 = 1 from rfl]; simp only [Nat.cast_ofNat, pow_one]; ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψder t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψder t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψder t).deriv]
      have h3 : ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ ≤ L * (t * ‖v‖) := by
        have := hD (x + t • v) x
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le] at this
        exact this
      have h4 : |fderiv ℝ f (x + t • v) v - d| ≤ L * t * ‖v‖ ^ 2 := by
        have : fderiv ℝ f (x + t • v) v - d = (fderiv ℝ f (x + t • v) - fderiv ℝ f x) v := by
          simp [hd]
        rw [this]
        calc |(fderiv ℝ f (x + t • v) - fderiv ℝ f x) v|
            ≤ ‖(fderiv ℝ f (x + t • v) - fderiv ℝ f x) v‖ := by rw [← Real.norm_eq_abs]
          _ ≤ ‖fderiv ℝ f (x + t • v) - fderiv ℝ f x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ L * (t * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ = L * t * ‖v‖ ^ 2 := by ring
      have h5 : σ * (fderiv ℝ f (x + t • v) v - d) ≤ L * t * ‖v‖ ^ 2 := by
        calc σ * (fderiv ℝ f (x + t • v) v - d) ≤ |σ * (fderiv ℝ f (x + t • v) v - d)| := le_abs_self _
          _ = |fderiv ℝ f (x + t • v) v - d| := by rw [abs_mul, hσ, one_mul]
          _ ≤ _ := h4
      linarith
  have := hanti (Set.mem_Icc.2 ⟨le_refl 0, zero_le_one⟩) (Set.mem_Icc.2 ⟨zero_le_one, le_refl 1⟩) zero_le_one
  simp only [hψ, hφ] at this
  simp at this
  linarith

theorem glr_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (x v : E) :
    |f (x + v) - f x - fderiv ℝ f x v| ≤ L / 2 * ‖v‖ ^ 2 := by
  rw [abs_le]
  constructor
  · have := glr_descent_aux f L hL hdiff hD x v (-1) (by simp)
    linarith
  · have := glr_descent_aux f L hL hdiff hD x v 1 (by simp)
    linarith

theorem glr_integral_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 2 ∂(stdGaussian E) = (Module.finrank ℝ E : ℝ) := by
  set b := stdOrthonormalBasis ℝ E with hb
  have hint : ∀ i, Integrable (fun u : E => inner ℝ (b i) u ^ 2) (stdGaussian E) := by
    intro i
    have h2 : Integrable (fun u : E => ‖u‖ ^ 2) (stdGaussian E) :=
      (IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable_norm_pow (by norm_num)
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact (by fun_prop : Continuous fun u : E => inner ℝ (b i) u ^ 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := real_inner_le_norm (b i) u
      have h3 := abs_real_inner_le_norm (b i) u
      have h4 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [h4, one_mul] at h3
      calc inner ℝ (b i) u ^ 2 = |inner ℝ (b i) u| ^ 2 := (sq_abs _).symm
        _ ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hvar : ∀ i, ∫ u, inner ℝ (b i) u ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h1 := variance_dual_stdGaussian (E := E) (innerSL ℝ (b i))
    have h2 := integral_strongDual_stdGaussian (E := E) (innerSL ℝ (b i))
    have h4 := variance_eq_integral (μ := stdGaussian E) (innerSL ℝ (b i)).continuous.aemeasurable
    rw [h1, h2] at h4
    simp only [innerSL_apply_apply, sub_zero] at h4
    have h5 : ‖innerSL ℝ (b i)‖ = 1 := by
      rw [innerSL_apply_norm]; exact b.orthonormal.1 i
    rw [h5] at h4
    rw [← h4]; norm_num
  have : ∀ u : E, ‖u‖ ^ 2 = ∑ i, inner ℝ (b i) u ^ 2 := fun u => (b.sum_sq_inner_right u).symm
  simp_rw [this]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp [hvar]

theorem glr_integrable_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Integrable (fun u : E => ‖u‖) (stdGaussian E) :=
  (IsGaussian.integrable_id (μ := stdGaussian E)).norm

theorem glr_integrable_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Integrable (fun u : E => ‖u‖ ^ 2) (stdGaussian E) :=
  (IsGaussian.memLp_two_id (μ := stdGaussian E)).integrable_norm_pow (by norm_num)

theorem glr_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (μ : ℝ) (x : E) :
    HasFDerivAt (RandomGradFree.Shared.smoothing f μ)
      (∫ u, fderiv ℝ f (x + μ • u) ∂(stdGaussian E)) x := by
  have hfc : Continuous f := hdiff.continuous
  have hDc : Continuous (fderiv ℝ f) := by
    have : LipschitzWith ⟨L, hL⟩ (fderiv ℝ f) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [dist_eq_norm, dist_eq_norm]; exact hD a b
    exact this.continuous
  have hI1 := glr_integrable_norm (E := E)
  have hI2 := glr_integrable_norm_sq (E := E)
  show HasFDerivAt (fun x' => ∫ u, f (x' + μ • u) ∂(stdGaussian E)) _ x
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x' u => f (x' + μ • u)) (F' := fun x' u => fderiv ℝ f (x' + μ • u))
    (s := Metric.ball x 1) (bound := fun u => ‖fderiv ℝ f x‖ + L * (1 + |μ| * ‖u‖))
    (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x' =>
      (hfc.comp (by fun_prop : Continuous fun u : E => x' + μ • u)).aestronglyMeasurable
  · -- integrability of u ↦ f (x + μ u)
    have hb : Integrable (fun u : E => |f x| + ‖fderiv ℝ f x‖ * (|μ| * ‖u‖) + L / 2 * (|μ| ^ 2 * ‖u‖ ^ 2))
        (stdGaussian E) :=
      ((integrable_const _).add ((hI1.const_mul _).const_mul _)).add ((hI2.const_mul _).const_mul _)
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact (hfc.comp (by fun_prop : Continuous fun u : E => x + μ • u)).aestronglyMeasurable
    · have h1 := glr_descent f L hL hdiff hD x (μ • u)
      have h2 : |fderiv ℝ f x (μ • u)| ≤ ‖fderiv ℝ f x‖ * (|μ| * ‖u‖) := by
        rw [← Real.norm_eq_abs]
        calc ‖fderiv ℝ f x (μ • u)‖ ≤ ‖fderiv ℝ f x‖ * ‖μ • u‖ := ContinuousLinearMap.le_opNorm _ _
          _ = _ := by rw [norm_smul, Real.norm_eq_abs]
      have h3 : ‖μ • u‖ ^ 2 = |μ| ^ 2 * ‖u‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow]
      rw [Real.norm_eq_abs]
      have h4 : |f (x + μ • u)| ≤ |f x| + |f (x + μ • u) - f x - fderiv ℝ f x (μ • u)| + |fderiv ℝ f x (μ • u)| := by
        have := abs_add_three (f x) (f (x + μ • u) - f x - fderiv ℝ f x (μ • u)) (fderiv ℝ f x (μ • u))
        calc |f (x + μ • u)| = |f x + (f (x + μ • u) - f x - fderiv ℝ f x (μ • u)) + fderiv ℝ f x (μ • u)| := by ring_nf
          _ ≤ _ := this
      rw [h3] at h1
      linarith
  · exact (hDc.comp (by fun_prop : Continuous fun u : E => x + μ • u)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u x' hx' => ?_
    have h1 := hD (x' + μ • u) x
    have h2 : ‖x' + μ • u - x‖ ≤ 1 + |μ| * ‖u‖ := by
      have : x' + μ • u - x = (x' - x) + μ • u := by abel
      rw [this]
      calc ‖(x' - x) + μ • u‖ ≤ ‖x' - x‖ + ‖μ • u‖ := norm_add_le _ _
        _ ≤ 1 + |μ| * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          have : ‖x' - x‖ < 1 := by simpa [dist_eq_norm] using hx'
          linarith
    have h3 : ‖fderiv ℝ f (x' + μ • u)‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ f (x' + μ • u) - fderiv ℝ f x‖ := by
      calc ‖fderiv ℝ f (x' + μ • u)‖ = ‖fderiv ℝ f x + (fderiv ℝ f (x' + μ • u) - fderiv ℝ f x)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h4 : L * ‖x' + μ • u - x‖ ≤ L * (1 + |μ| * ‖u‖) := mul_le_mul_of_nonneg_left h2 hL
    linarith
  · exact (integrable_const _).add ((((integrable_const _).add (hI1.const_mul _)).const_mul _))
  · refine Filter.Eventually.of_forall fun u x' _ => ?_
    have := (hdiff (x' + μ • u)).hasFDerivAt.comp x' ((hasFDerivAt_id x').add_const (μ • u))
    simp only [ContinuousLinearMap.comp_id] at this
    exact this

theorem glr_grad_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x y : E) :
    ‖gradient f x - gradient f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem glr_key {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (μ : ℝ) (x : E) :
    ‖gradient (RandomGradFree.Shared.smoothing f μ) x - gradient f x‖ ≤
      |μ| * L * ((Module.finrank ℝ E : ℝ) + 1) / 2 := by
  have hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖ := fun a b => by
    rw [← glr_grad_norm]; exact hgrad a b
  have hfc : Continuous f := hdiff.continuous
  have hDc : Continuous (fderiv ℝ f) := by
    have : LipschitzWith ⟨L, hL⟩ (fderiv ℝ f) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [dist_eq_norm, dist_eq_norm]; exact hD a b
    exact this.continuous
  have hI1 := glr_integrable_norm (E := E)
  have hI2 := glr_integrable_norm_sq (E := E)
  have hsm := glr_hasFDerivAt f L hL hdiff hD μ x
  have hg1 : gradient (RandomGradFree.Shared.smoothing f μ) x =
      (InnerProductSpace.toDual ℝ E).symm (∫ u, fderiv ℝ f (x + μ • u) ∂(stdGaussian E)) := by
    unfold gradient; rw [hsm.fderiv]
  rw [hg1]
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hint : Integrable (fun u : E => fderiv ℝ f (x + μ • u)) (stdGaussian E) := by
    refine ((integrable_const ‖fderiv ℝ f x‖).add (hI1.const_mul (L * |μ|))).mono' ?_
      (Filter.Eventually.of_forall fun u => ?_)
    · exact (hDc.comp (by fun_prop : Continuous fun u : E => x + μ • u)).aestronglyMeasurable
    · have h1 := hD (x + μ • u) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h1
      have h3 : ‖fderiv ℝ f (x + μ • u)‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ f (x + μ • u) - fderiv ℝ f x‖ := by
        calc ‖fderiv ℝ f (x + μ • u)‖ = ‖fderiv ℝ f x + (fderiv ℝ f (x + μ • u) - fderiv ℝ f x)‖ := by
              congr 1; abel
          _ ≤ _ := norm_add_le _ _
      show ‖fderiv ℝ f (x + μ • u)‖ ≤ ‖fderiv ℝ f x‖ + L * |μ| * ‖u‖
      nlinarith
  have hc : ∫ u, fderiv ℝ f x ∂(stdGaussian E) = fderiv ℝ f x := by simp
  have hsub : (∫ u, fderiv ℝ f (x + μ • u) ∂(stdGaussian E)) - fderiv ℝ f x =
      ∫ u, (fderiv ℝ f (x + μ • u) - fderiv ℝ f x) ∂(stdGaussian E) := by
    rw [integral_sub hint (integrable_const _), hc]
  rw [hsub]
  have hbd : Integrable (fun u : E => |μ| * L / 2 * (1 + ‖u‖ ^ 2)) (stdGaussian E) :=
    ((integrable_const _).add hI2).const_mul _
  refine le_trans (norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall fun u => ?_)) ?_
  · have h1 := hD (x + μ • u) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h1
    show ‖fderiv ℝ f (x + μ • u) - fderiv ℝ f x‖ ≤ |μ| * L / 2 * (1 + ‖u‖ ^ 2)
    have hLm : 0 ≤ |μ| * L / 2 := by positivity
    nlinarith [mul_nonneg hLm (sq_nonneg (1 - ‖u‖)), norm_nonneg u, abs_nonneg μ]
  · rw [integral_const_mul, integral_add (integrable_const _) hI2, glr_integral_norm_sq]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    apply le_of_eq; ring

theorem glr_integrable_f {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (μ : ℝ) (x : E) :
    Integrable (fun u : E => f (x + μ • u)) (stdGaussian E) := by
  have hfc : Continuous f := hdiff.continuous
  have hI1 := glr_integrable_norm (E := E)
  have hI2 := glr_integrable_norm_sq (E := E)
  have hb : Integrable (fun u : E => |f x| + ‖fderiv ℝ f x‖ * (|μ| * ‖u‖) + L / 2 * (|μ| ^ 2 * ‖u‖ ^ 2))
      (stdGaussian E) :=
    ((integrable_const _).add ((hI1.const_mul _).const_mul _)).add ((hI2.const_mul _).const_mul _)
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (hfc.comp (by fun_prop : Continuous fun u : E => x + μ • u)).aestronglyMeasurable
  · have h1 := glr_descent f L hL hdiff hD x (μ • u)
    have h2 : |fderiv ℝ f x (μ • u)| ≤ ‖fderiv ℝ f x‖ * (|μ| * ‖u‖) := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ f x (μ • u)‖ ≤ ‖fderiv ℝ f x‖ * ‖μ • u‖ := ContinuousLinearMap.le_opNorm _ _
        _ = _ := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : ‖μ • u‖ ^ 2 = |μ| ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow]
    rw [Real.norm_eq_abs]
    have h4 : |f (x + μ • u)| ≤ |f x| + |f (x + μ • u) - f x - fderiv ℝ f x (μ • u)| + |fderiv ℝ f x (μ • u)| := by
      have := abs_add_three (f x) (f (x + μ • u) - f x - fderiv ℝ f x (μ • u)) (fderiv ℝ f x (μ • u))
      calc |f (x + μ • u)| = |f x + (f (x + μ • u) - f x - fderiv ℝ f x (μ • u)) + fderiv ℝ f x (μ • u)| := by ring_nf
        _ ≤ _ := this
    rw [h3] at h1
    linarith

theorem glr_approx {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hdiff : Differentiable ℝ f)
    (hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) (μ : ℝ) (x : E) :
    |RandomGradFree.Shared.smoothing f μ x - f x| ≤ μ ^ 2 / 2 * L * (Module.finrank ℝ E : ℝ) := by
  have hI1 := glr_integrable_norm (E := E)
  have hI2 := glr_integrable_norm_sq (E := E)
  have hf := glr_integrable_f f L hL hdiff hD μ x
  have hlin : Integrable (fun u : E => fderiv ℝ f x (μ • u)) (stdGaussian E) := by
    have : Integrable (fun u : E => μ * fderiv ℝ f x u) (stdGaussian E) :=
      ((fderiv ℝ f x).integrable_comp (IsGaussian.integrable_id (μ := stdGaussian E))).const_mul μ
    simpa using this
  have hlin0 : ∫ u, fderiv ℝ f x (μ • u) ∂(stdGaussian E) = 0 := by
    have : ∫ u, μ * fderiv ℝ f x u ∂(stdGaussian E) = 0 := by
      rw [integral_const_mul]
      have := integral_strongDual_stdGaussian (E := E) (fderiv ℝ f x)
      rw [this, mul_zero]
    simpa using this
  have hsub : RandomGradFree.Shared.smoothing f μ x - f x =
      ∫ u, (f (x + μ • u) - f x - fderiv ℝ f x (μ • u)) ∂(stdGaussian E) := by
    have e1 : ∫ u, (f (x + μ • u) - f x - fderiv ℝ f x (μ • u)) ∂(stdGaussian E) =
        (∫ u, (f (x + μ • u) - f x) ∂(stdGaussian E)) - ∫ u, fderiv ℝ f x (μ • u) ∂(stdGaussian E) :=
      integral_sub (hf.sub (integrable_const _)) hlin
    have e2 : ∫ u, (f (x + μ • u) - f x) ∂(stdGaussian E) =
        (∫ u, f (x + μ • u) ∂(stdGaussian E)) - ∫ u, f x ∂(stdGaussian E) :=
      integral_sub hf (integrable_const _)
    rw [e1, e2, hlin0]
    simp [RandomGradFree.Shared.smoothing]
  rw [hsub]
  have hbd : Integrable (fun u : E => L / 2 * (μ ^ 2 * ‖u‖ ^ 2)) (stdGaussian E) :=
    (hI2.const_mul _).const_mul _
  have := norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall fun u => by
    have h1 := glr_descent f L hL hdiff hD x (μ • u)
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h1
    show ‖f (x + μ • u) - f x - fderiv ℝ f x (μ • u)‖ ≤ L / 2 * (μ ^ 2 * ‖u‖ ^ 2)
    rw [Real.norm_eq_abs]; exact h1)
  rw [← Real.norm_eq_abs]
  refine le_trans this (le_of_eq ?_)
  rw [integral_const_mul, integral_const_mul, glr_integral_norm_sq]
  ring

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ f) (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (μs : ℝ) (hμs : 0 < μs) (fstar : ℝ) (hfstar : IsGLB (Set.range f) fstar)
    (fμstar : ℝ) (hfμstar : IsGLB (Set.range (RandomGradFree.Shared.smoothing f μs)) fμstar) :
    ∀ x, -(μs ^ 2 * L * (n : ℝ)) ≤
        (RandomGradFree.Shared.smoothing f μs x - fμstar) - (f x - fstar) ∧
      (RandomGradFree.Shared.smoothing f μs x - fμstar) - (f x - fstar) ≤ μs ^ 2 * L * (n : ℝ) := by
  have hD : ∀ x y, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖ := fun a b => by
    rw [← glr_grad_norm]; exact hgrad a b
  set c : ℝ := μs ^ 2 / 2 * L * (n : ℝ) with hc
  have hap : ∀ y, |RandomGradFree.Shared.smoothing f μs y - f y| ≤ c := by
    intro y
    have := glr_approx f L hL hdiff hD μs y
    rwa [finrank_euclideanSpace_fin] at this
  have h1 : fstar - c ≤ fμstar := by
    apply hfμstar.2
    rintro _ ⟨y, rfl⟩
    have := (abs_le.1 (hap y)).1
    have h2 : fstar ≤ f y := hfstar.1 ⟨y, rfl⟩
    linarith
  have h2 : fμstar - c ≤ fstar := by
    apply hfstar.2
    rintro _ ⟨y, rfl⟩
    have := (abs_le.1 (hap y)).2
    have h3 : fμstar ≤ RandomGradFree.Shared.smoothing f μs y := hfμstar.1 ⟨y, rfl⟩
    linarith
  intro x
  have h3 := abs_le.1 (hap x)
  have h4 : μs ^ 2 * L * (n : ℝ) = 2 * c := by rw [hc]; ring
  rw [h4]
  constructor <;> linarith
