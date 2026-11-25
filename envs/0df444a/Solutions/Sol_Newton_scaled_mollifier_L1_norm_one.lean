-- Prove2me | solution 1 for Newton.scaled_mollifier_L1_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:34.455551+00:00
-- url     : https://prove2.me/submissions/33aa2b83-41cb-40ac-ac79-4b6587aa4501

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Definitions.Def_Newton_Analysis_Convolution_Minkowski
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Theorems.Thm_Newton_aemeasurable_smul_measure_of_aemeasurable

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal ContDiff Pointwise
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (ψ : (Fin n → ℝ) → ℝ)
    (η : ℝ)
    (hη : 0 < η)
    (hψ_int : Integrable ψ volume)
    (hψ_norm : ∫ x, ψ x = 1)
    (hψ_nonneg : ∀ x, 0 ≤ ψ x) :
    eLpNorm (fun (x : Fin n → ℝ) => η^(-(n : ℝ)) * ψ (fun i => x i / η)) 1 volume =
      ENNReal.ofReal 1 := by
  -- Define the scaled mollifier and the scaling map.
  set ψη : (Fin n → ℝ) → ℝ :=
    fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η) with hψη_def
  set g : (Fin n → ℝ) → (Fin n → ℝ) := fun x => (1 / η : ℝ) • x with hg_def
  -- Basic measurability for the scaling map
  have hg_meas : Measurable g := by
    simpa [hg_def] using (continuous_const_smul (1 / η : ℝ)).measurable
  -- Pointwise positivity of ψη due to ψ ≥ 0 and η > 0.
  have hψη_nonneg : ∀ x, 0 ≤ ψη x := by
    intro x
    have hx_arg : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    have hψ_nonneg_at : 0 ≤ ψ (g x) := hψ_nonneg (g x)
    have hηpos : 0 ≤ η^(-(n : ℝ)) := by
      have : 0 < η^(-(n : ℝ)) := by
        simpa using Real.rpow_pos_of_pos hη (-(n : ℝ))
      exact this.le
    -- Align ψ (g x) with ψ (fun i => x i / η) using hx_arg
    simpa [hψη_def, hg_def, one_div, div_eq_mul_inv, hx_arg, mul_comm, mul_left_comm, mul_assoc]
      using mul_nonneg hηpos hψ_nonneg_at
  -- Rewrite the L¹ seminorm as a nonnegative lintegral and factor out the constant η^{-n}.
  have h_step1 :
      eLpNorm ψη 1 volume
        = ENNReal.ofReal (η^(-(n : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := by
    -- Start from the L¹ formula for `eLpNorm` and rewrite the integrand.
    have hη_nonneg : 0 ≤ η^(-(n : ℝ)) := by
      have : 0 < η^(-(n : ℝ)) := by simpa using Real.rpow_pos_of_pos hη (-(n : ℝ))
      exact this.le
    have h_enorm_eq :
        ∀ᵐ x ∂volume,
          (‖ψη x‖ₑ : ℝ≥0∞)
            = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have hψgx_nonneg : 0 ≤ ψ (g x) := hψ_nonneg (g x)
      -- Align arguments: (η⁻¹) • x = fun i => x i * η⁻¹
      have hx_arg : (η⁻¹ : ℝ) • x = fun i => x i * η⁻¹ := by
        funext i; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      calc
        (‖ψη x‖ₑ : ℝ≥0∞)
            = ENNReal.ofReal ‖ψη x‖ := (ofReal_norm_eq_enorm (ψη x)).symm
        _   = ENNReal.ofReal (ψη x) := by
              simp [Real.norm_eq_abs, abs_of_nonneg (hψη_nonneg x)]
        _   = ENNReal.ofReal (η^(-(n : ℝ)) * ψ (g x)) := by
              simp [hψη_def, hg_def, div_eq_mul_inv, hx_arg, mul_comm]
        _   = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) := by
              -- Use `ENNReal.ofReal_mul` (one nonneg proof argument) and specify `p`, `q`.
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using (ENNReal.ofReal_mul
                  (p := η^(-(n : ℝ))) (q := ψ (g x)) hη_nonneg)
    -- Pull the constant out of the lintegral using the `c ≠ ∞` variant.
    have h_c_ne_top : ENNReal.ofReal (η^(-(n : ℝ))) ≠ ⊤ := by simp
    calc
      eLpNorm ψη 1 volume
          = ∫⁻ x, ‖ψη x‖ₑ ∂volume := by
                simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      _   = ∫⁻ x, ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (ψ (g x)) ∂volume := by
                simpa using lintegral_congr_ae h_enorm_eq
      _   = ENNReal.ofReal (η^(-(n : ℝ))) * ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := by
                simpa [mul_comm, mul_left_comm, mul_assoc]
                  using
                    (lintegral_const_mul' (μ := volume)
                      (ENNReal.ofReal (η^(-(n : ℝ))))
                      (fun x : (Fin n → ℝ) => ENNReal.ofReal (ψ (g x)))
                      h_c_ne_top)
  -- Compute the pushforward of Lebesgue measure under the linear scaling map x ↦ (1/η)·x.
  have h_map_scale :
      Measure.map g volume
        = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)) • volume := by
    -- This is a standard Jacobian formula for linear maps on ℝ^n.
    have h_eq_fn : (⇑((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) : (Fin n → ℝ) → (Fin n → ℝ)) = g := by
      funext y; simp [g]
    rw [← h_eq_fn]
    exact Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (f := ( (1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ))
        (by
          -- Show det ≠ 0 via the explicit determinant formula and η ≠ 0.
          have hne : (1 / η : ℝ) ≠ 0 := one_div_ne_zero (ne_of_gt hη)
          have hdet :
              LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
                = (1 / η : ℝ) ^ Module.finrank ℝ (Fin n → ℝ) := by
            simp
          have hpow2 : (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) ≠ 0 :=
            pow_ne_zero (Module.finrank ℝ (Fin n → ℝ)) hne
          simpa [hdet] using hpow2)
  -- Change variables: express the lintegral of ψ ∘ g via the pushforward measure.
  have h_change :
      ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume
        = ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
            * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
    -- Build AEMeasurable for the integrand under the pushforward measure.
    have hψ_aemeas : AEMeasurable ψ volume :=
      hψ_int.aestronglyMeasurable.aemeasurable
    have h_ofReal_aemeas_map :
        AEMeasurable (fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
          (Measure.map g volume) := by
      -- Use the helper to transport a.e.-measurability across the scalar multiple
      -- given by `h_map_scale`.
      have h_ofReal_aemeas_vol :
          AEMeasurable (fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y)) volume :=
        hψ_aemeas.ennreal_ofReal
      -- `Measure.map g volume = c • volume` where `c = ofReal |det g|⁻¹`.
      -- Hence a.e.-measurability transfers from `volume` to `Measure.map g volume`.
      simpa [h_map_scale]
        using aemeasurable_smul_measure_of_aemeasurable
          (f := fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
          (μ := volume)
          (c := ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
          h_ofReal_aemeas_vol
    -- Change of variables for lintegral via `lintegral_map'`.
    have h_map_eq :=
      lintegral_map' (μ := volume)
        (f := fun y : (Fin n → ℝ) => ENNReal.ofReal (ψ y))
        (g := g) h_ofReal_aemeas_map
        (aemeasurable_id'.comp_measurable hg_meas)
    -- Pull out the scaling factor from the pushforward measure using `lintegral_smul_measure`.
    have h_pull_const :
        ∫⁻ y, ENNReal.ofReal (ψ y) ∂(Measure.map g volume)
          = ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
              * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
      simp [h_map_scale, lintegral_smul_measure]
    simpa [h_map_eq] using h_pull_const
  -- Convert the remaining lintegral to a real integral using nonnegativity of ψ.
  have hψ_nonneg_ae : 0 ≤ᵐ[volume] fun y => ψ y :=
    Filter.Eventually.of_forall hψ_nonneg
  have hψ_lintegral :
      ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume
        = ENNReal.ofReal (∫ y, ψ y ∂volume) := by
    -- Use the standard bridge between lintegral and integral for nonnegative integrable ψ.
    simpa using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψ_int hψ_nonneg_ae).symm
  have h_det_simp :
      ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
        = ENNReal.ofReal (η ^ (n : ℝ)) := by
    -- Evaluate the determinant and simplify using η > 0.
    have hdet :
        LinearMap.det ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
          = (1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ)) := by simp
    have hfinrank : (Module.finrank ℝ (Fin n → ℝ)) = n := by simp
    -- Since η > 0, ((1/η)^n)⁻¹ = η^n and is nonnegative, so its absolute value equals itself.
    have h_pow_inv : ((1 / η : ℝ) ^ n)⁻¹ = η ^ n := by
      -- Use (a^n)⁻¹ = (a⁻¹)^n with a = 1/η and (1/η)⁻¹ = η.
      simp [one_div, inv_inv]
    have h_nonneg : 0 ≤ ((1 / η : ℝ) ^ n)⁻¹ := by
      -- Positivity from η > 0.
      have hpos : 0 < (1 / η : ℝ) := by
        simpa [one_div] using (inv_pos.mpr hη)
      exact inv_nonneg.mpr (le_of_lt (pow_pos hpos n))
    have h_abs_eq : abs (((1 / η : ℝ) ^ n)⁻¹) = ((1 / η : ℝ) ^ n)⁻¹ :=
      abs_of_nonneg h_nonneg
    -- Translate nat-power to real-power.
    have h_nat_to_real : (η ^ n : ℝ) = η ^ (n : ℝ) := by simp
    calc
      ENNReal.ofReal (abs ((LinearMap.det
          ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
          = ENNReal.ofReal (abs (((1 / η : ℝ) ^ (Module.finrank ℝ (Fin n → ℝ))) )⁻¹) := by
            simp
      _ = ENNReal.ofReal (abs (((1 / η : ℝ) ^ n)⁻¹)) := by simp [hfinrank]
      _ = ENNReal.ofReal (((1 / η : ℝ) ^ n)⁻¹) := by simp [abs_of_pos hη]
      _ = ENNReal.ofReal (η ^ n) := by simp
      _ = ENNReal.ofReal (((η : ℝ) ^ (n : ℝ))) := by
        exact congrArg ENNReal.ofReal h_nat_to_real
  -- Combine all equalities and simplify using ∫ ψ = 1 and rpow rules.
  have h_prod :
      ENNReal.ofReal (η^(-(n : ℝ)))
        * (ENNReal.ofReal (abs ((LinearMap.det
            ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
        = ENNReal.ofReal 1 := by
    -- Use multiplicativity of ofReal and rpow addition.
    have hη_pos_real : 0 ≤ η^(-(n : ℝ)) :=
      (Real.rpow_pos_of_pos hη (-(n : ℝ))).le
    have hη_pow_pos : 0 ≤ η ^ (n : ℝ) :=
      (Real.rpow_pos_of_pos hη (n : ℝ)).le
    have h_mul_ofReal :
        ENNReal.ofReal (η^(-(n : ℝ)) * η ^ (n : ℝ))
          = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (η ^ (n : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc]
        using (ENNReal.ofReal_mul (p := η^(-(n : ℝ))) (q := η ^ (n : ℝ)) hη_pos_real)
    -- Simplify the product inside ofReal using rpow_add.
    have h_rpow : η^(-(n : ℝ)) * η ^ (n : ℝ) = (η : ℝ) ^ (0 : ℝ) := by
      have h_add := Real.rpow_add hη (-(n : ℝ)) (n : ℝ)
      -- x^(a+b) = x^a * x^b ⇒ x^a * x^b = x^(a+b)
      -- Here a = -n, b = n, so a + b = 0.
      have hsum : (-(n : ℝ)) + (n : ℝ) = 0 := by simp
      simpa [hsum, Real.rpow_zero] using h_add.symm
    -- Conclude the product equals 1.
    have h_one : ENNReal.ofReal ((η : ℝ) ^ (0 : ℝ)) = ENNReal.ofReal 1 := by
      simp
    calc
      ENNReal.ofReal (η^(-(n : ℝ)))
          * ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹))
          = ENNReal.ofReal (η^(-(n : ℝ))) * ENNReal.ofReal (η ^ (n : ℝ)) := by
                simp [abs_of_pos hη]
      _ = ENNReal.ofReal (η^(-(n : ℝ)) * η ^ (n : ℝ)) := by
                -- Use the earlier multiplicativity lemma tailored to rpow terms.
                simpa using h_mul_ofReal.symm
      _ = ENNReal.ofReal ((η : ℝ) ^ (0 : ℝ)) := by
        simpa using h_rpow
      _ = ENNReal.ofReal 1 := h_one
  -- Final assembly: start from `h_step1`, apply the change-of-variables `h_change`,
  -- convert the remaining lintegral using `hψ_lintegral`, and simplify with `hψ_norm`.
  calc
    eLpNorm ψη 1 volume
        = ENNReal.ofReal (η^(-(n : ℝ))) *
            ∫⁻ x, ENNReal.ofReal (ψ (g x)) ∂volume := h_step1
    _ = (ENNReal.ofReal (η^(-(n : ℝ))) *
            ENNReal.ofReal (abs ((LinearMap.det
              ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
            * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            congrArg (fun z => ENNReal.ofReal (η^(-(n : ℝ))) * z) h_change
    _ = ENNReal.ofReal 1 * ENNReal.ofReal (∫ y, ψ y ∂volume) := by
          -- First, multiply the constant factor equality `h_prod` by the lintegral.
          have hconst_mul :
              (ENNReal.ofReal (η^(-(n : ℝ))) *
                ENNReal.ofReal (abs ((LinearMap.det
                  ((1 / η : ℝ) • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) )⁻¹)))
                * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume
                = ENNReal.ofReal 1 * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              congrArg (fun c => c * ∫⁻ y, ENNReal.ofReal (ψ y) ∂volume) h_prod
          -- Then convert the lintegral using `hψ_lintegral`.
          simpa [hψ_lintegral] using hconst_mul
    _ = ENNReal.ofReal 1 := by simp [hψ_norm]
end Newton
