-- Prove2me | solution 1 for Newton.integral_scaledMollifier_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:18.302231+00:00
-- url     : https://prove2.me/submissions/a9f23070-91ef-452f-8f03-3409f7c47f10

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity

set_option autoImplicit false
open MeasureTheory Complex NNReal SchwartzMap
open scoped ENNReal ContDiff Topology Pointwise
open Newton
variable {n : ℕ}
variable {ψ : (Fin n → ℝ) → ℝ}
namespace Newton
theorem _root_.solution
    (hψ : IsApproximateIdentity ψ) {η : ℝ} (hη_pos : 0 < η) :
    ∫ x, scaledMollifier ψ η x = (1 : ℝ) := by
  -- Scaling map g(x) = (1/η) • x
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η) • x with hg
  have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
  -- ψ is integrable as it is continuous with compact support
  have hψ_int : Integrable ψ volume :=
    (hψ.smooth.continuous.integrable_of_hasCompactSupport hψ.compact_support)
  -- Describe the pushforward of volume under the linear map g
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
  -- Transfer integrability under the pushforward measure
  have hg_meas : Measurable g := by
    -- Use continuity of the linear map x ↦ (1/η) • x
    simpa [g, hg]
      using ((continuous_const_smul (1 / η : ℝ)).measurable)
  have hg_aemeas : AEMeasurable g volume := hg_meas.aemeasurable
  have hψ_int_map : Integrable ψ (Measure.map g volume) := by
    have hc_ne_top : ENNReal.ofReal ((|η|) ^ n) ≠ ⊤ := by simp
    have hψ_memLp : MemLp ψ 1 volume :=
      (memLp_one_iff_integrable (μ := volume)).2 hψ_int
    have hψ_memLp_map : MemLp ψ 1 (Measure.map g volume) := by
      simpa [h_map_scale]
        using hψ_memLp.smul_measure hc_ne_top
    exact (memLp_one_iff_integrable (μ := Measure.map g volume)).1 hψ_memLp_map
  -- Evaluate ∫ ψ ∘ g via mapping and smul of measure
  have h_integral_comp :
      ∫ x, ψ (g x)
        = (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
    have h_map :
        ∫ y, ψ y ∂(Measure.map g volume) = ∫ x, ψ (g x) ∂volume := by
      simpa using
        (MeasureTheory.integral_map (μ := volume)
          hg_aemeas (hψ_int_map.aestronglyMeasurable))
    have h_smul :
        ∫ y, ψ y ∂(Measure.map g volume)
          = (ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y := by
      simp [h_map_scale, integral_smul_measure]
    exact h_map.symm.trans h_smul
  -- Compute the determinant factor: for g = (1/η)•id, toReal equals η^n
  have h_det_toReal :
      (ENNReal.ofReal ((|η|) ^ n)).toReal = η ^ (n : ℝ) := by
    have h_pos : 0 < η := hη_pos
    have h_abs : |η| = η := by simp [abs_of_pos h_pos]
    -- Rewrite to ofReal/toReal and use nonnegativity of η^n
    have h_nonneg : 0 ≤ η ^ n := pow_nonneg (le_of_lt h_pos) _
    simp [h_abs, Real.rpow_natCast, h_nonneg]
  -- Now compute the integral of the scaled mollifier
  have h_mη_as_comp :
      (fun y => scaledMollifier ψ η y)
        = fun y => (η ^ (-(n : ℝ))) * ψ (g y) := by
    funext y
    have hg_apply : g y = (fun i => y i / η) := by
      funext i
      -- ((1/η) • y) i = (1/η) * y i = y i * η⁻¹ = y i / η
      simp [g, div_eq_mul_inv, mul_comm]
    simp [scaledMollifier, hg_apply]
  calc
    ∫ x, scaledMollifier ψ η x
        = (η ^ (-(n : ℝ))) * ∫ x, ψ (g x) := by
          simp [h_mη_as_comp, integral_const_mul]
    _   = (η ^ (-(n : ℝ))) *
            ((ENNReal.ofReal ((|η|) ^ n)).toReal * ∫ y, ψ y) := by
          simp [h_integral_comp]
    _   = ((η ^ (-(n : ℝ))) * (η ^ (n : ℝ))) * ∫ y, ψ y := by
          rw [h_det_toReal]
          ring
    _   = (1 : ℝ) * ∫ y, ψ y := by
      -- Simplify (η^(-n)) * (η^n) = 1, then multiply both sides by ∫ ψ
      have hpow_ne_zero : η ^ (n : ℝ) ≠ 0 := by
        have hpos : 0 < η ^ (n : ℝ) := Real.rpow_pos_of_pos hη_pos _
        exact ne_of_gt hpos
      have hEq : (η ^ (-(n : ℝ))) * η ^ (n : ℝ) = (1 : ℝ) := by
        have h' : (η ^ (n : ℝ))⁻¹ * η ^ (n : ℝ) = (1 : ℝ) :=
          inv_mul_cancel₀ hpow_ne_zero
        simpa [Real.rpow_neg (le_of_lt hη_pos)] using h'
      have := congrArg (fun t : ℝ => t * ∫ y, ψ y) hEq
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    _   = (1 : ℝ) := by simp [hψ.normalized]
end Newton
