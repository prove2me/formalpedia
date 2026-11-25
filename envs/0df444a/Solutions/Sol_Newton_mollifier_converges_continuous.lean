-- Prove2me | solution 1 for Newton.mollifier_converges_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:55.360687+00:00
-- url     : https://prove2.me/submissions/32b9d467-8e0d-4e49-8574-7866b6d8196a

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Theorems.Thm_Newton_scaledMollifier_nonneg
import Theorems.Thm_Newton_hasCompactSupport_scaledMollifier
import Theorems.Thm_Newton_tsupport_scaledMollifier_subset

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : (Fin n → ℝ) → ℂ)
    (ψ : (Fin n → ℝ) → ℝ)
    (hf_cont : Continuous f)
    (hf_compact : HasCompactSupport f)
    (hψ : IsApproximateIdentity ψ) :
    ∀ ε > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
      ∀ x, ‖f x - ∫ y, f (x - y) * (scaledMollifier ψ η y)‖ < ε := by
  -- Use uniform continuity of a compactly supported continuous function.
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ :=
    (Metric.uniformContinuous_iff.mp
      (hf_compact.uniformContinuous_of_continuous hf_cont)) (ε / 2)
      (by linarith)
  have hδ₀' : ∀ x y, ‖x - y‖ < δ₀ → ‖f x - f y‖ < ε / 2 := by
    intro x y hxy
    have hxy' : dist x y < δ₀ := by simpa [dist_eq_norm] using hxy
    have hε' : dist (f x) (f y) < ε / 2 := hδ₀ hxy'
    simpa [dist_eq_norm] using hε'
  -- We will choose δ ≤ δ₀ so that ‖y‖ < δ ⇒ ‖f x - f (x - y)‖ < ε/2.
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro η hη_pos hη_lt
  -- Abbreviations for the scaled mollifier and its scaling map.
  set mη : (Fin n → ℝ) → ℝ := fun y => scaledMollifier ψ η y with hmη
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η) • x with hg
  have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
  -- Change of variables: compute ∫ mη = 1 using hψ.normalized.
  have hψ_int : Integrable ψ volume :=
    (hψ.smooth.continuous.integrable_of_hasCompactSupport hψ.compact_support)
  -- Describe map (1/η)•id on volume.
  have h_map_scale :
      Measure.map g (volume : Measure (Fin n → ℝ))
        = ENNReal.ofReal ((|η|) ^ n) • (volume : Measure (Fin n → ℝ)) := by
    have h_det_ne :
        LinearMap.det ((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) ≠ 0 := by
      have hdet :
          LinearMap.det ((η⁻¹ : ℝ) •
              (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
            = (η⁻¹ : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by
        simp
      have hpow_ne : (η⁻¹ : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
        pow_ne_zero _ (inv_ne_zero hη_ne_zero)
      simpa [hdet] using hpow_ne
    have hg_lin :
        (fun x : (Fin n → ℝ) =>
          (((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
              (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) x)
          = g := by
      funext x; simp [g, one_div]
    simpa [hg_lin]
      using
        Real.map_linearMap_volume_pi_eq_smul_volume_pi
          (f := ((η⁻¹ : ℝ) •
            (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))) h_det_ne
  -- Evaluate ∫ ψ ∘ g by mapping along `g` and then using `integral_smul_measure`.
  have hg_meas : Measurable g := by
    -- g is linear, hence measurable
    simpa [g, hg]
      using ((continuous_const_smul (1 / η : ℝ)).measurable)
  have hg_aemeas : AEMeasurable g volume := hg_meas.aemeasurable
  have hψ_int_map : Integrable ψ (Measure.map g volume) := by
    -- Transfer integrability along the smul measure identity.
    have hc_ne_top : ENNReal.ofReal ((|η|) ^ n) ≠ ⊤ := by simp
    have hψ_memLp : MemLp ψ 1 volume :=
      (memLp_one_iff_integrable (μ := volume)).2 hψ_int
    have hψ_memLp_map : MemLp ψ 1 (Measure.map g volume) := by
      simpa [h_map_scale]
        using hψ_memLp.smul_measure hc_ne_top
    exact (memLp_one_iff_integrable (μ := Measure.map g volume)).1 hψ_memLp_map
  have h_integral_comp :
      ∫ x, ψ (g x) =
        (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
    -- integral over the pushforward = integral of the composition
    have h_map :
        ∫ y, ψ y ∂(Measure.map g volume) = ∫ x, ψ (g x) ∂volume := by
      simpa using
        (MeasureTheory.integral_map (μ := volume)
          hg_aemeas (hψ_int_map.aestronglyMeasurable))
    -- Evaluate integral with smul measure
    have h_smul :
        ∫ y, ψ y ∂(Measure.map g volume)
          = (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
      simp [h_map_scale, integral_smul_measure]
    exact h_map.symm.trans h_smul
  -- Compute the determinant factor: for g = (1/η)•id, toReal equals η^n.
  have h_det_toReal :
      (ENNReal.ofReal ((|η|) ^ n)).toReal = η ^ (n : ℝ) := by
    have h_pos : 0 < η := hη_pos
    have h_abs : |η| = η := by simp [abs_of_pos h_pos]
    have h_nonneg : 0 ≤ η ^ n := pow_nonneg (le_of_lt h_pos) _
    simp [h_abs, Real.rpow_natCast, h_nonneg]
  -- From the above, obtain ∫ mη = 1.
  have h_mη_integral_one : (∫ y, mη y) = (1 : ℝ) := by
    have h_eq : (∫ y, mη y)
        = (η ^ (-(n : ℝ))) * (∫ x, ψ (g x)) := by
      -- mη = η^{-n} · (ψ ∘ g)
      have : (fun y => mη y) = fun y => (η ^ (-(n : ℝ))) * ψ (g y) := by
        funext y
        have hg_apply : g y = (fun i => y i / η) := by
          funext i
          -- ((1/η) • y) i = (1/η) * y i = y i * η⁻¹ = y i / η
          simp [g, div_eq_mul_inv, mul_comm]
        simp [mη, scaledMollifier, hg_apply]
      simp [this, integral_const_mul]
    have h_norm := hψ.normalized
    have h_intψ : ∫ y, ψ y = 1 := h_norm
    -- Expand h_eq and use h_integral_comp followed by h_det_toReal
    have : (∫ y, mη y)
        = (η ^ (-(n : ℝ))) * ((ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y) := by
      simp [h_eq, h_integral_comp]
    -- Simplify (η^(-n)) * (η^n) = 1 and conclude using h_intψ
    have h_mul_one : (η ^ (-(n : ℝ))) * (η ^ (n : ℝ)) = (1 : ℝ) := by
      have h' : (η ^ (n : ℝ))⁻¹ * η ^ (n : ℝ) = (1 : ℝ) :=
        inv_mul_cancel₀ (by
          have hpos : 0 < η ^ (n : ℝ) := Real.rpow_pos_of_pos hη_pos _
          exact ne_of_gt hpos)
      simpa [Real.rpow_neg (le_of_lt hη_pos)] using h'
    -- Combine the equalities
    have : (∫ y, mη y)
        = ((η ^ (-(n : ℝ))) * (η ^ (n : ℝ))) * ∫ y, ψ y := by
      rw [h_det_toReal] at this
      linarith
    -- Replace the scalar product with 1 * ∫ ψ using inv_mul_cancel₀ on η^n
    have h_pow_ne_zero_nat : η ^ n ≠ 0 := pow_ne_zero _ hη_ne_zero
    have : (∫ y, mη y) = (1 : ℝ) * ∫ y, ψ y := by
      calc ∫ y, mη y
          = (η ^ (-(n : ℝ))) * (η ^ (n : ℝ)) * ∫ y, ψ y := this
        _ = (η ^ (n : ℝ))⁻¹ * (η ^ (n : ℝ)) * ∫ y, ψ y := by
            rw [Real.rpow_neg (le_of_lt hη_pos)]
        _ = (η ^ n)⁻¹ * (η ^ n) * ∫ y, ψ y := by
            simp only [Real.rpow_natCast]
        _ = 1 * ∫ y, ψ y := by
            rw [inv_mul_cancel₀ h_pow_ne_zero_nat]
    simpa [h_intψ]
  -- Main estimate: bound the difference by ε using uniform continuity and support of mη.
  intro x
  -- Rewrite the difference using ∫ mη = 1 then apply norm-integral ≤ integral-norm
  have h_const_integral :
      (∫ y, (f x) * (mη y)) = f x := by
    rw [integral_const_mul]
    have : (∫ (a : Fin n → ℝ), ((mη a) : ℂ)) = ↑(∫ (y : Fin n → ℝ), mη y) :=
      integral_ofReal
    rw [this, h_mη_integral_one, ofReal_one, mul_one]
  -- Define complex-valued version of the mollifier
  let mηC : (Fin n → ℝ) → ℂ := fun y => (mη y : ℝ)
  have h_mηC_compact : HasCompactSupport mηC := by
    have h_mη_compact := hasCompactSupport_scaledMollifier hψ.compact_support hη_pos
    -- Upgrade real-valued compact support to complex-valued via eventual equality
    rw [hasCompactSupport_iff_eventuallyEq] at h_mη_compact ⊢
    exact h_mη_compact.mono (by
      intro y hy
      simp only [mηC]
      have : mη y = scaledMollifier ψ η y := rfl
      rw [this, hy]
      simp)
  -- Continuity facts for the integrand pieces
  have h_div_cont : Continuous (fun y : (Fin n → ℝ) => fun i => y i / η) := by
    have :
        (fun y : (Fin n → ℝ) => fun i => y i / η)
          = fun y : (Fin n → ℝ) => (η⁻¹ : ℝ) • y := by
      funext y i; simp [div_eq_mul_inv, mul_comm]
    simpa [this] using (continuous_const_smul (η⁻¹ : ℝ))
  have h_mη_cont : Continuous mη :=
    continuous_const.mul (hψ.smooth.continuous.comp h_div_cont)
  have h_mηC_cont : Continuous mηC :=
    continuous_ofReal.comp h_mη_cont
  have h_transl_cont : Continuous (fun y : (Fin n → ℝ) => f (x - y)) := by
    have h_sub : Continuous (fun y : (Fin n → ℝ) => x - y) :=
      continuous_const.sub continuous_id
    exact hf_cont.comp h_sub
  -- Integrability of the convolution integrand via compact support
  have h_prod_cont :
      Continuous (fun y : (Fin n → ℝ) => f (x - y) * mηC y) :=
    h_transl_cont.mul h_mηC_cont
  have h_prod_compact :
      HasCompactSupport (fun y : (Fin n → ℝ) => f (x - y) * mηC y) :=
    h_mηC_compact.mul_left
  have h_prod_integrable :
      Integrable (fun y : (Fin n → ℝ) => f (x - y) * mηC y) volume :=
    h_prod_cont.integrable_of_hasCompactSupport h_prod_compact
  -- Also record integrability of the constant×mη term
  have h_const_mul_integrable :
      Integrable (fun y : (Fin n → ℝ) => (f x) * mηC y) volume := by
    -- (f x) • mηC is integrable since mηC has compact support
    have h_cont : Continuous (fun y : (Fin n → ℝ) => (f x) * mηC y) :=
      (continuous_const.mul h_mηC_cont)
    have h_compact :
        HasCompactSupport (fun y : (Fin n → ℝ) => (f x) * mηC y) :=
      h_mηC_compact.mul_left
    exact h_cont.integrable_of_hasCompactSupport h_compact
  -- Convert the difference to a single integral and bound it
  have h_diff_eq_integral :
      f x - ∫ y, f (x - y) * (mη y) =
        ∫ y, ((f x) * (mηC y) - (f (x - y) * mηC y)) := by
    -- Use h_const_integral and integral_sub
    have h_sub :=
      integral_sub h_const_mul_integrable h_prod_integrable
    -- Rearrange to obtain the desired equality
    simpa [mηC, h_const_integral, sub_eq_add_neg]
      using h_sub.symm
  have h_to_single :
      ∫ y, ((f x) * (mηC y) - (f (x - y) * mηC y))
        = ∫ y, ((f x - f (x - y)) * mηC y) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y; ring
  have h_nonneg_mη : ∀ y, 0 ≤ mη y :=
    scaledMollifier_nonneg hψ.nonneg (le_of_lt hη_pos)
  -- Pointwise bound: ‖(f x - f (x - y)) * mηC y‖ ≤ (ε/2) * mη y
  have h_pointwise_bound :
      ∀ᵐ y ∂volume,
        ‖(f x - f (x - y)) * mηC y‖ ≤ (ε / 2) * mη y := by
    refine Filter.Eventually.of_forall ?_
    intro y
    by_cases hy0 : mη y = 0
    · -- Both sides are zero
      simp [mηC, hy0]
    · -- On the (topological) support we have ‖y‖ ≤ η < δ₀, hence the UC bound
      have hy_support : y ∈ tsupport mη := by
        have : y ∈ Function.support mη := by
          simpa [Function.support] using hy0
        exact subset_tsupport _ this
      have hy_ball : y ∈ Metric.closedBall (0 : Fin n → ℝ) η :=
        tsupport_scaledMollifier_subset hψ hη_pos hy_support
      have hy_norm_le : ‖y‖ ≤ η := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy_ball
      have hy_norm_lt : ‖y‖ < δ₀ := lt_of_le_of_lt hy_norm_le hη_lt
      have hxy_norm : ‖x - (x - y)‖ < δ₀ := by
        -- ‖x - (x - y)‖ = ‖y‖
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using hy_norm_lt
      have h_uc := hδ₀' x (x - y) hxy_norm
      have h_uc_le : ‖f x - f (x - y)‖ ≤ ε / 2 := le_of_lt h_uc
      have h_norm_mηC : ‖mηC y‖ = mη y := by
        have hnn := h_nonneg_mη y
        simp [mηC, Real.norm_eq_abs, abs_of_nonneg hnn]
      have h_rhs_nonneg : 0 ≤ (ε / 2) * mη y :=
        mul_nonneg (by have := half_pos hε; exact (le_of_lt this))
          (h_nonneg_mη y)
      -- Now multiply the UC bound by ‖mηC y‖ = mη y
      have :
          ‖(f x - f (x - y)) * mηC y‖
            = ‖f x - f (x - y)‖ * ‖mηC y‖ := by
        simp
      have :
          ‖(f x - f (x - y)) * mηC y‖ ≤ (ε / 2) * ‖mηC y‖ := by
        simpa [this, mul_comm]
          using mul_le_mul_of_nonneg_right h_uc_le (by simp)
      simpa [h_norm_mηC]
        using this.trans_eq (by simp [h_norm_mηC, mul_comm])
  -- Convert to an integral bound
  have h_diff_mul_cont :
      Continuous (fun y : (Fin n → ℝ) => (f x - f (x - y)) * mηC y) := by
    have h_diff_cont : Continuous (fun y : (Fin n → ℝ) => f x - f (x - y)) :=
      (continuous_const.sub h_transl_cont)
    exact h_diff_cont.mul h_mηC_cont
  have h_diff_mul_compact :
      HasCompactSupport (fun y : (Fin n → ℝ) => (f x - f (x - y)) * mηC y) :=
    h_mηC_compact.mul_left
  have h_integrable_left :
      Integrable (fun y => ‖(f x - f (x - y)) * mηC y‖) volume := by
    have h_int : Integrable (fun y : (Fin n → ℝ) => (f x - f (x - y)) * mηC y) volume :=
      h_diff_mul_cont.integrable_of_hasCompactSupport h_diff_mul_compact
    simpa using h_int.norm
  have h_integrable_right :
      Integrable (fun y => (ε / 2) * mη y) volume := by
    -- mη is integrable (real), hence so is scaling by ε/2
    have h_div_cont :
        Continuous (fun x : (Fin n → ℝ) => fun i => x i / η) := by
      have :
          (fun x : (Fin n → ℝ) => fun i => x i / η)
            = fun x : (Fin n → ℝ) => (η⁻¹ : ℝ) • x := by
        funext x i; simp [div_eq_mul_inv, mul_comm]
      simpa [this] using (continuous_const_smul (η⁻¹ : ℝ))
    have h_cont : Continuous (scaledMollifier ψ η) :=
      continuous_const.mul (hψ.smooth.continuous.comp h_div_cont)
    have h_compact := hasCompactSupport_scaledMollifier hψ.compact_support hη_pos
    have h_mη_int : Integrable (fun x => scaledMollifier ψ η x) volume :=
      h_cont.integrable_of_hasCompactSupport h_compact
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using h_mη_int.mul_const (ε / 2)
  have h_int_norm_le :
      ∫ y, ‖(f x - f (x - y)) * mηC y‖
        ≤ ∫ y, (ε / 2) * mη y := by
    refine MeasureTheory.integral_mono_ae
        h_integrable_left h_integrable_right ?_
    exact h_pointwise_bound
  -- Combine everything
  have h_main_bound :
      ‖f x - ∫ y, f (x - y) * (mη y)‖ ≤ ε / 2 := by
    have h1 :
        ‖f x - ∫ y, f (x - y) * (mη y)‖
          = ‖∫ y, (f x - f (x - y)) * mηC y‖ := by
      simp [h_diff_eq_integral, h_to_single]
    have h2 :
        ‖∫ y, (f x - f (x - y)) * mηC y‖
          ≤ ∫ y, ‖(f x - f (x - y)) * mηC y‖ :=
      norm_integral_le_integral_norm _
    have h3 :
        ∫ y, (ε / 2) * mη y = (ε / 2) * ∫ y, mη y := by
      -- move the constant outside the integral
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using (integral_const_mul (μ := volume) (f := fun y => mη y) (ε / 2))
    have h4 : (ε / 2) * ∫ y, mη y = ε / 2 := by
      simp [h_mη_integral_one]
    have : ∫ y, ‖(f x - f (x - y)) * mηC y‖ ≤ ε / 2 := by
      simpa [h3, h4] using h_int_norm_le
    exact (h1 ▸ (le_trans h2 this))
  -- Conclude strict inequality using ε/2 < ε
  have hhalf_lt : ε / 2 < ε := by have := half_lt_self hε; simpa using this
  exact lt_of_le_of_lt h_main_bound hhalf_lt
end Newton
