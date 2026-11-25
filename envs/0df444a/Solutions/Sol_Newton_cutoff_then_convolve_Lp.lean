-- Prove2me | solution 1 for Newton.cutoff_then_convolve_Lp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:26.008439+00:00
-- url     : https://prove2.me/submissions/61039f19-e5ba-41f4-bb15-3a54f8cd1687

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Definitions.Def_Newton_Analysis_Distribution_SchwartzDensity
import Theorems.Thm_Newton_exists_smooth_cutoff
import Theorems.Thm_Newton_exists_mollifier_scale
import Theorems.Thm_Newton_cutoff_L1_bound
import Theorems.Thm_Newton_cutoff_L2_bound
import Theorems.Thm_Newton_convolution_support_ball_subset
import Theorems.Thm_Newton_smooth_compactSupport_to_schwartz


set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 volume)
    (hf_L2 : MemLp f 2 volume)
    (R : ℝ) (hR : 0 < R)
    {ε ε_cut₁ ε_cut₂ ε_tail₁ ε_tail₂ : ℝ}
    (hε : 0 < ε)
    (hcut₁ : 0 < ε_cut₁) (hcut₂ : 0 < ε_cut₂)
    (htail₁ : 0 < ε_tail₁) (htail₂ : 0 < ε_tail₂)
    (h_budget_L1 : ε_cut₁ + ε_tail₁ < ε)
    (h_budget_L2 : ε_cut₂ + ε_tail₂ < ε)
    (hf_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁)
    (hf_tail_L2 :
      eLpNorm (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ENNReal.ofReal ε_tail₂) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 3) ∧
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by
  have hR_lt : R < R + 1 := by linarith
  obtain ⟨χ, hχ_smooth, hχ_one, hχ_bounds, hχ_compact, hχ_support⟩ :=
    exists_smooth_cutoff (n := n) R (R + 1) hR hR_lt
  have hχ_nonneg : ∀ x, 0 ≤ χ x := fun x => (hχ_bounds x).1
  have hχ_le_one : ∀ x, χ x ≤ 1 := fun x => (hχ_bounds x).2
  set f_cut : (Fin n → ℝ) → ℂ := fun x => (χ x : ℂ) * f x with hf_cut_def
  have h_diff_zero_inside :
      ∀ {x : (Fin n → ℝ)}, ‖x‖ ≤ R → f x - f_cut x = 0 := by
    intro x hx
    have hχx : χ x = 1 := hχ_one x hx
    simp [hf_cut_def, hχx]
  have h_diff_norm_le : ∀ x, ‖f x - f_cut x‖ ≤ ‖f x‖ := by
    intro x
    have hx_nonneg : 0 ≤ χ x := hχ_nonneg x
    have hx_le_one : χ x ≤ 1 := hχ_le_one x
    have habs_le : |1 - χ x| ≤ (1 : ℝ) := by
      have hdiff_nonneg : 0 ≤ 1 - χ x := by linarith
      have hdiff_le : 1 - χ x ≤ 1 := by linarith
      have habs_eq : |1 - χ x| = 1 - χ x := abs_of_nonneg hdiff_nonneg
      simpa [habs_eq] using hdiff_le
    have hmul_le : |1 - χ x| * ‖f x‖ ≤ 1 * ‖f x‖ := by
      have hnorm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_right habs_le hnorm_nonneg
    have hnorm_eq :
        ‖f x - f_cut x‖ = |1 - χ x| * ‖f x‖ := by
      have hfactor : f x - f_cut x = f x * (1 - (χ x : ℂ)) := by
        have := (mul_sub (f x) (1 : ℂ) (χ x : ℂ))
        simpa [hf_cut_def, one_mul, mul_comm] using this.symm
      calc
        ‖f x - f_cut x‖
            = ‖f x * (1 - (χ x : ℂ))‖ := by simp [hfactor]
        _ = ‖f x‖ * ‖1 - (χ x : ℂ)‖ := norm_mul _ _
        _ = ‖f x‖ * |1 - χ x| := by
          have hnormχ : ‖1 - (χ x : ℂ)‖ = |1 - χ x| := by
            simpa [Complex.ofReal_sub] using (RCLike.norm_ofReal (K := ℂ) (1 - χ x))
          simp [hnormχ]
        _ = |1 - χ x| * ‖f x‖ := by ring
    calc
      ‖f x - f_cut x‖ = |1 - χ x| * ‖f x‖ := hnorm_eq
      _ ≤ 1 * ‖f x‖ := hmul_le
      _ = ‖f x‖ := by simp
  have h_diff_support :
      Function.support (fun x => f x - f_cut x)
        ⊆ {x : (Fin n → ℝ) | R < ‖x‖} := by
    intro x hx
    by_contra hnot
    have hx_le : ‖x‖ ≤ R := le_of_not_gt hnot
    have hx_ne : f x - f_cut x ≠ 0 := by
      simpa [Function.support] using hx
    have hzero : f x - f_cut x = 0 := h_diff_zero_inside hx_le
    exact hx_ne hzero
  have h_cutoff_L1 :
      eLpNorm (fun x => f x - f_cut x) 1 volume ≤ ENNReal.ofReal ε_tail₁ :=
    cutoff_L1_bound f f_cut hf_L1 χ R ε_tail₁ hχ_nonneg hχ_le_one
      hf_cut_def h_diff_zero_inside hf_tail_L1 htail₁
  have h_cutoff_L2 :
      eLpNorm (fun x => f x - f_cut x) 2 volume ≤ ENNReal.ofReal ε_tail₂ :=
    cutoff_L2_bound f f_cut χ R ε_tail₂ hχ_nonneg hχ_le_one
      hf_cut_def h_diff_zero_inside hf_tail_L2
  -- Mollify the truncated function and combine the error budgets.
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  let χℂ : (Fin n → ℝ) → ℂ := fun x => (χ x : ℂ)
  have hχℂ_cont : Continuous χℂ := Complex.continuous_ofReal.comp hχ_cont
  have hχℂ_meas : AEStronglyMeasurable χℂ volume := hχℂ_cont.aestronglyMeasurable
  have hf_cut_meas : AEStronglyMeasurable f_cut volume := by
    have hf_meas : AEStronglyMeasurable f volume := hf_L1.aestronglyMeasurable
    have h_mul : f_cut = fun x => χℂ x * f x := by
      funext x; simp [hf_cut_def, χℂ, mul_comm]
    rw [h_mul]; exact hχℂ_meas.mul hf_meas
  have h_cut_norm_le : ∀ x, ‖f_cut x‖ ≤ ‖f x‖ := by
    intro x
    have hnorm : ‖f_cut x‖ = |χ x| * ‖f x‖ := by
      have h_mul : f_cut x = (χ x : ℂ) * f x := by
        simp [hf_cut_def, mul_comm]
      have hnorm' : ‖(χ x : ℂ) * f x‖ = ‖(χ x : ℂ)‖ * ‖f x‖ := norm_mul _ _
      have habs : ‖(χ x : ℂ)‖ = |χ x| := by
        simp
      simp [h_mul]
    have habs_le : |χ x| ≤ 1 := by
      have hnonneg : 0 ≤ χ x := hχ_nonneg x
      have hle_one : χ x ≤ 1 := hχ_le_one x
      have habs : |χ x| = χ x := abs_of_nonneg hnonneg
      simpa [habs] using hle_one
    have hnonneg : 0 ≤ ‖f x‖ := norm_nonneg _
    have hmul_le : |χ x| * ‖f x‖ ≤ ‖f x‖ :=
      by
        have := mul_le_of_le_one_left hnonneg habs_le
        simpa using this
    simpa [hnorm]
  have h_cut_sq_le : ∀ x, ‖f_cut x‖ ^ (2 : ℝ) ≤ ‖f x‖ ^ (2 : ℝ) := by
    intro x
    exact Real.rpow_le_rpow (norm_nonneg _) (h_cut_norm_le x) (by norm_num)
  have hf_integrable : Integrable f volume :=
    (memLp_one_iff_integrable).1 hf_L1
  have hf_cut_integrable : Integrable f_cut volume := by
    refine Integrable.mono' hf_integrable.norm hf_cut_meas ?_
    exact Filter.Eventually.of_forall fun x => h_cut_norm_le x
  have hf_cut_L1 : MemLp f_cut 1 volume :=
    (memLp_one_iff_integrable).2 hf_cut_integrable
  have hf_sq_integrable : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) volume := by
    simpa [one_div] using
      (hf_L2.integrable_norm_rpow (μ := volume)
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp))
  have hf_cut_sq_meas :
      AEStronglyMeasurable (fun x => ‖f_cut x‖ ^ (2 : ℝ)) volume :=
    ((hf_cut_meas.norm.aemeasurable.pow_const (2 : ℝ)).aestronglyMeasurable)
  have hf_cut_sq_integrable : Integrable (fun x => ‖f_cut x‖ ^ (2 : ℝ)) volume := by
    have h_cut_sq_le_abs : ∀ x, |‖f_cut x‖ ^ (2 : ℝ)| ≤ ‖f x‖ ^ (2 : ℝ) := by
      intro x
      have h_nonneg : 0 ≤ ‖f_cut x‖ ^ (2 : ℝ) :=
        Real.rpow_nonneg (norm_nonneg _) _
      simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_cut_sq_le x
    refine Integrable.mono' hf_sq_integrable hf_cut_sq_meas ?_
    exact Filter.Eventually.of_forall h_cut_sq_le_abs
  have hf_cut_L2 : MemLp f_cut 2 volume := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by simp
    have hf_cut_sq_memLp :
        MemLp (fun x => ‖f_cut x‖ ^ ((2 : ℝ≥0∞).toReal))
          ((2 : ℝ≥0∞) / (2 : ℝ≥0∞)) volume := by
      simpa [ENNReal.toReal_ofNat, ENNReal.div_self, hp0]
        using (memLp_one_iff_integrable).2 hf_cut_sq_integrable
    exact
      (memLp_norm_rpow_iff (μ := volume) (q := (2 : ℝ≥0∞))
          (p := (2 : ℝ≥0∞)) hf_cut_meas hp0 hp_top).1 hf_cut_sq_memLp
  have h_support_eq : Function.support χℂ = Function.support χ := by
    ext x; simp [χℂ, Function.support]
  have h_tsupp_eq : tsupport χℂ = tsupport χ := by
    simp [tsupport, h_support_eq]
  have hf_cut_support_subset :
      tsupport f_cut ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
    have hf_subset : tsupport f_cut ⊆ tsupport χℂ := by
      have h_mul : f_cut = fun x => f x * χℂ x := by
        funext x; simp [hf_cut_def, χℂ, mul_comm]
      simpa [h_mul]
        using
          (tsupport_mul_subset_right
            (f := fun x : (Fin n → ℝ) => f x)
            (g := χℂ))
    have hχ_subset : tsupport χℂ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1) := by
      simpa [χℂ, h_tsupp_eq] using hχ_support
    exact hf_subset.trans hχ_subset
  have hχ_supportℂ : HasCompactSupport χℂ := by
    rw [hasCompactSupport_iff_eventuallyEq] at hχ_compact ⊢
    exact hχ_compact.mono (by intro x hx; simp [χℂ, hx] )
  have hf_cut_support : HasCompactSupport f_cut := by
    have h_mul : f_cut = fun x => χℂ x * f x := by
      funext x; simp [hf_cut_def, χℂ, mul_comm]
    have h_mul_support :
        HasCompactSupport (fun x : (Fin n → ℝ) => χℂ x * f x) :=
      HasCompactSupport.mul_right (f := χℂ) (f' := fun x : (Fin n → ℝ) => f x) hχ_supportℂ
    simpa [h_mul]
      using h_mul_support
  obtain ⟨η, hη_pos, hη_le_one, ψ₀, hψ₀_smooth, hψ₀_compact, hψ₀_integral, hψ₀_nonneg,
      hψ₀_support, hφ_data⟩ :=
    exists_mollifier_scale f_cut hf_cut_L1 hf_cut_L2
      ε_cut₁ ε_cut₂ hcut₁ hcut₂
  set ψ_η : (Fin n → ℝ) → ℝ := fun y => η^(-(n : ℝ)) * ψ₀ (fun i => y i / η) with hψη_def
  set ψ_ηℂ : (Fin n → ℝ) → ℂ := fun y => (ψ_η y : ℝ) with hψηC_def
  set φ₀ : (Fin n → ℝ) → ℂ :=
    fun x => ∫ y, f_cut (x - y) * ψ_ηℂ y with hφ₀_def
  have hφ₀_L1_cut :
      eLpNorm (fun x => f_cut x - φ₀ x) 1 volume < ENNReal.ofReal ε_cut₁ := by
    have := (hφ_data.1)
    simpa [ψ_η, ψ_ηℂ, hψη_def, hψηC_def, φ₀, hφ₀_def]
      using this
  have hφ₀_L2_cut :
      eLpNorm (fun x => f_cut x - φ₀ x) 2 volume < ENNReal.ofReal ε_cut₂ := by
    have := (hφ_data.2)
    simpa [ψ_η, ψ_ηℂ, hψη_def, hψηC_def, φ₀, hφ₀_def]
      using this
  have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
  have hψη_eq_mul :
      ψ_η
        = (fun _ : (Fin n → ℝ) => (η ^ n : ℝ)⁻¹)
            * fun y : (Fin n → ℝ) => ψ₀ ((η⁻¹ : ℝ) • y) := by
    funext y
    have hfun : (fun i => y i / η) = fun i => (η⁻¹ : ℝ) * y i := by
      funext i; simp [div_eq_mul_inv, mul_comm]
    have hsmul : (η⁻¹ : ℝ) • y = fun i => (η⁻¹ : ℝ) * y i := by
      funext i; simp [Pi.smul_apply]
    simp [ψ_η, hfun, hsmul, Pi.mul_apply]
  have hψη_compact : HasCompactSupport ψ_η := by
    have h_comp : HasCompactSupport (fun y : (Fin n → ℝ) => ψ₀ ((η⁻¹ : ℝ) • y)) := by
      simpa [one_div]
        using
          (HasCompactSupport.comp_smul (α := (Fin n → ℝ)) (β := ℝ) (G₀ := ℝ)
            hψ₀_compact (inv_ne_zero hη_ne_zero))
    have h_mul :=
      HasCompactSupport.mul_left
        (f := fun _ : (Fin n → ℝ) => (η ^ n : ℝ)⁻¹)
        (f' := fun y : (Fin n → ℝ) => ψ₀ ((η⁻¹ : ℝ) • y)) h_comp
    simpa [hψη_eq_mul]
      using h_mul
  have hψηℂ_compact : HasCompactSupport ψ_ηℂ := by
    rw [hasCompactSupport_iff_eventuallyEq] at hψη_compact ⊢
    exact hψη_compact.mono (by intro x hx; simp [ψ_ηℂ, hx])
  -- Remaining work: control the support of `φ₀`, upgrade to a Schwartz function,
  -- and combine the L¹/L² error budgets.
  have hψη_support_subset :
      tsupport ψ_η ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
    have h_support_subset :
        Function.support ψ_η ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
      intro y hy
      have hyψ : ψ_η y ≠ 0 := by
        simpa [Function.support] using hy
      have hη_nonneg : 0 ≤ η := hη_pos.le
      have hcalc : ψ_η y = η ^ (-(n : ℝ)) * ψ₀ ((η⁻¹ : ℝ) • y) := by
        have hfun : (fun i => y i / η) = fun i => (η⁻¹ : ℝ) * y i := by
          funext i; simp [div_eq_mul_inv, mul_comm]
        have hsmul : (η⁻¹ : ℝ) • y = fun i => (η⁻¹ : ℝ) * y i := by
          funext i; simp [Pi.smul_apply]
        simp [ψ_η, hfun, hsmul]
      have hψ₀_ne : ψ₀ ((η⁻¹ : ℝ) • y) ≠ 0 := by
        intro hzero
        apply hyψ
        simp [hcalc, hzero]
      have hy_support : (η⁻¹ : ℝ) • y ∈ Function.support ψ₀ := by
        simpa [Function.support] using hψ₀_ne
      have hy_tsupp : (η⁻¹ : ℝ) • y ∈ tsupport ψ₀ :=
        subset_tsupport _ hy_support
      have hy_ball : (η⁻¹ : ℝ) • y ∈
          Metric.closedBall (0 : Fin n → ℝ) 1 :=
        hψ₀_support hy_tsupp
      have hy_norm_le : ‖(η⁻¹ : ℝ) • y‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy_ball
      have hy_norm_eq :
          ‖(η⁻¹ : ℝ) • y‖ = (η⁻¹ : ℝ) * ‖y‖ := by
        have hnorm : ‖(η⁻¹ : ℝ)‖ = (η⁻¹ : ℝ) := by
          have hpos : 0 < (η⁻¹ : ℝ) := inv_pos.mpr hη_pos
          simpa [Real.norm_eq_abs, abs_of_pos hpos]
        simp [norm_smul, hnorm]
      have h_mul_le : (η⁻¹ : ℝ) * ‖y‖ ≤ 1 := by
        simpa [hy_norm_eq] using hy_norm_le
      have hy_le : ‖y‖ ≤ η := by
        have h_mul := mul_le_mul_of_nonneg_right h_mul_le hη_nonneg
        have h_left : ((η⁻¹ : ℝ) * ‖y‖) * η = ‖y‖ := by
          calc
            ((η⁻¹ : ℝ) * ‖y‖) * η
                = ‖y‖ * ((η⁻¹ : ℝ) * η) := by
                  simp [mul_comm, mul_assoc]
            _ = ‖y‖ * (1 : ℝ) := by
                  simp [hη_ne_zero, mul_comm]
            _ = ‖y‖ := by simp
        have h_right : (1 : ℝ) * η = η := by simp
        simpa [h_left, h_right] using h_mul
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy_le
    have h_closed : IsClosed (Metric.closedBall (0 : Fin n → ℝ) η) :=
      Metric.isClosed_closedBall
    have h_closure_subset := closure_minimal h_support_subset h_closed
    simpa [tsupport] using h_closure_subset
  have hψηℂ_support_subset :
      tsupport ψ_ηℂ ⊆ Metric.closedBall (0 : Fin n → ℝ) η := by
    have h_support_eq : Function.support ψ_ηℂ = Function.support ψ_η := by
      ext y; simp [ψ_ηℂ, ψ_η, Function.support]
    have h_tsupp_eq : tsupport ψ_ηℂ = tsupport ψ_η := by
      simp [tsupport, h_support_eq]
    simpa [h_tsupp_eq]
      using hψη_support_subset
  have hψηℂ_support_subset_unit :
      tsupport ψ_ηℂ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    intro x hx
    have hx' := hψηℂ_support_subset hx
    have hx_norm_le : ‖x‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
    have hx_norm_le_one : ‖x‖ ≤ (1 : ℝ) := hx_norm_le.trans hη_le_one
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx_norm_le_one
  have hφ₀_support_subset :
      tsupport φ₀ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 2) := by
    have h_conv :=
      convolution_support_ball_subset
        (f := f_cut) (g := ψ_ηℂ) (R := R + 1) (δ := 1)
        hf_cut_support_subset hψηℂ_support_subset_unit
    have h_add : (R + 1 : ℝ) + 1 = R + 2 := by ring
    simpa [φ₀, hφ₀_def, add_comm, add_left_comm, add_assoc, h_add, one_add_one_eq_two]
      using h_conv
  have hφ₀_support : HasCompactSupport φ₀ := by
    have hconv := HasCompactSupport.convolution (μ := MeasureSpace.volume)
      (L := ContinuousLinearMap.mul ℝ ℂ) hψηℂ_compact hf_cut_support
    have heq : (ψ_ηℂ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f_cut) = φ₀ := by
      funext x; simp [MeasureTheory.convolution_def, φ₀, hφ₀_def, mul_comm]
    rwa [heq] at hconv
  have hψη_cont : Continuous ψ_η := by
    have h_const : Continuous fun _ : (Fin n → ℝ) => (η ^ n : ℝ)⁻¹ :=
      continuous_const
    have h_scale : Continuous fun y : (Fin n → ℝ) => (η⁻¹ : ℝ) • y :=
      continuous_const_smul (η⁻¹ : ℝ)
    have h_comp : Continuous fun y : (Fin n → ℝ) => ψ₀ ((η⁻¹ : ℝ) • y) :=
      hψ₀_smooth.continuous.comp h_scale
    simpa [hψη_eq_mul] using h_const.mul h_comp
  have hψηℂ_cont : Continuous ψ_ηℂ :=
    Complex.continuous_ofReal.comp hψη_cont
  have hf_cut_locInt : LocallyIntegrable f_cut volume :=
    hf_cut_integrable.locallyIntegrable
  have h_conv_cont : Continuous fun x =>
      (f_cut ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψ_ηℂ) x := by
    have := hψηℂ_compact.continuous_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
      hf_cut_locInt hψηℂ_cont
    simpa using this
  have h_conv_eq :
      (fun x =>
        (f_cut ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψ_ηℂ) x)
        = φ₀ := by
    funext x
    have hswap :=
      convolution_mul_swap (μ := volume) (G := Fin n → ℝ)
        (f := f_cut) (g := ψ_ηℂ) (x := x)
    have h_eq : (f_cut ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψ_ηℂ) x =
        (f_cut ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ψ_ηℂ) x := by
      simp [MeasureTheory.convolution_def]
    rw [h_eq]; exact hswap
  have hφ₀_cont : Continuous φ₀ := by
    simpa [h_conv_eq] using h_conv_cont
  have hφ₀_meas : AEStronglyMeasurable φ₀ volume := hφ₀_cont.aestronglyMeasurable
  -- φ₀ is smooth because convolution with a smooth compactly supported kernel
  -- preserves smoothness.
  have hψη_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ_η := by
    have h_const : ContDiff ℝ (∞ : WithTop ℕ∞)
        (fun _ : (Fin n → ℝ) => (η ^ n : ℝ)⁻¹) := contDiff_const
    have h_scale :
        ContDiff ℝ (∞ : WithTop ℕ∞)
          (fun y : (Fin n → ℝ) => (η⁻¹ : ℝ) • y) := by
      have h_const' : ContDiff ℝ (∞ : WithTop ℕ∞)
          (fun _ : (Fin n → ℝ) => (η⁻¹ : ℝ)) := contDiff_const
      have h_id : ContDiff ℝ (∞ : WithTop ℕ∞)
          (fun y : (Fin n → ℝ) => y) := contDiff_id
      exact h_const'.smul h_id
    have h_comp :
        ContDiff ℝ (∞ : WithTop ℕ∞)
          (fun y : (Fin n → ℝ) => ψ₀ ((η⁻¹ : ℝ) • y)) :=
      hψ₀_smooth.comp h_scale
    have h_mul :
        ContDiff ℝ (∞ : WithTop ℕ∞)
          (fun y : (Fin n → ℝ) =>
            (η ^ n : ℝ)⁻¹ * ψ₀ ((η⁻¹ : ℝ) • y)) :=
      h_const.mul h_comp
    have h_eq :
        (fun y : (Fin n → ℝ) =>
            (η ^ n : ℝ)⁻¹ * ψ₀ ((η⁻¹ : ℝ) • y)) = ψ_η := by
      exact hψη_eq_mul.symm
    simpa [h_eq] using h_mul
  have hψηℂ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ_ηℂ := by
    have h_comp := Complex.ofRealCLM.contDiff.comp hψη_smooth
    have h_eq :
        (fun y : (Fin n → ℝ) =>
            Complex.ofRealCLM (ψ_η y)) = ψ_ηℂ := by
      funext y
      simp [ψ_ηℂ]
    rw [← h_eq]; exact h_comp
  have hφ₀_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ₀ := by
    have h_contDiff :=
      hψηℂ_compact.contDiff_convolution_right
        (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
        (hf := hf_cut_locInt) (hg := hψηℂ_smooth)
    simpa [h_conv_eq]
      using h_contDiff
  obtain ⟨φ, hφ_eq⟩ :=
    smooth_compactSupport_to_schwartz φ₀ hφ₀_smooth hφ₀_support
  have hφ_support_subset_R2 :
      tsupport (φ : (Fin n → ℝ) → ℂ)
        ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 2) := by
    simpa [hφ_eq]
      using hφ₀_support_subset
  have hφ_support_subset :
      tsupport (φ : (Fin n → ℝ) → ℂ)
        ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 3) := by
    have h_le : R + 2 ≤ R + 3 := by linarith
    exact hφ_support_subset_R2.trans
      (Metric.closedBall_subset_closedBall h_le)
  have hφ_cut_L1 :
      eLpNorm (fun x => f_cut x - φ x) 1 volume
        < ENNReal.ofReal ε_cut₁ := by
    simpa [hφ_eq]
      using hφ₀_L1_cut
  have hφ_cut_L2 :
      eLpNorm (fun x => f_cut x - φ x) 2 volume
        < ENNReal.ofReal ε_cut₂ := by
    simpa [hφ_eq]
      using hφ₀_L2_cut
  have hφ_meas : AEStronglyMeasurable
      (fun x => φ x) volume := by
    simpa [hφ_eq]
      using hφ₀_meas
  have hf_meas : AEStronglyMeasurable f volume :=
    hf_integrable.aestronglyMeasurable
  have h_diff1_meas : AEStronglyMeasurable
      (fun x => f x - f_cut x) volume :=
    hf_meas.sub hf_cut_meas
  have h_diff2_meas : AEStronglyMeasurable
      (fun x => f_cut x - φ x) volume :=
    hf_cut_meas.sub hφ_meas
  have h_triangle_L1 :
      eLpNorm (fun x => f x - φ x) 1 volume
        ≤ eLpNorm (fun x => f x - f_cut x) 1 volume
            + eLpNorm (fun x => f_cut x - φ x) 1 volume := by
    have h_fun_eq :
        (fun x => f x - φ x)
          = (fun x => f x - f_cut x)
              + fun x => f_cut x - φ x := by
      funext x
      simp [sub_eq_add_neg, add_left_comm, add_assoc]
    simpa [h_fun_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := (1 : ℝ≥0∞))
          h_diff1_meas h_diff2_meas le_rfl)
  have h_triangle_L2 :
      eLpNorm (fun x => f x - φ x) 2 volume
        ≤ eLpNorm (fun x => f x - f_cut x) 2 volume
            + eLpNorm (fun x => f_cut x - φ x) 2 volume := by
    have h_fun_eq :
        (fun x => f x - φ x)
          = (fun x => f x - f_cut x)
              + fun x => f_cut x - φ x := by
      funext x
      simp [sub_eq_add_neg, add_left_comm, add_assoc]
    simpa [h_fun_eq]
      using
        (eLpNorm_add_le (μ := volume) (p := (2 : ℝ≥0∞))
          h_diff1_meas h_diff2_meas (by norm_num : 1 ≤ (2 : ℝ≥0∞)))
  have h_sum_lt_L1 :
      eLpNorm (fun x => f x - f_cut x) 1 volume
          + eLpNorm (fun x => f_cut x - φ x) 1 volume
        < ENNReal.ofReal ε := by
    have h_add_le :=
      add_le_add h_cutoff_L1 hφ_cut_L1.le
    have h_tail_nonneg : 0 ≤ ε_tail₁ := le_of_lt htail₁
    have h_cut_nonneg : 0 ≤ ε_cut₁ := le_of_lt hcut₁
    have h_sum_eq :
        ENNReal.ofReal ε_tail₁ + ENNReal.ofReal ε_cut₁
          = ENNReal.ofReal (ε_tail₁ + ε_cut₁) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using (ENNReal.ofReal_add h_tail_nonneg h_cut_nonneg).symm
    have h_budget' :
        ENNReal.ofReal (ε_tail₁ + ε_cut₁)
          < ENNReal.ofReal ε := by
      have h_sum_lt : ε_tail₁ + ε_cut₁ < ε := by
        simpa [add_comm]
          using h_budget_L1
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 h_sum_lt
    refine lt_of_le_of_lt ?_ h_budget'
    simpa [h_sum_eq] using h_add_le
  have h_sum_lt_L2 :
      eLpNorm (fun x => f x - f_cut x) 2 volume
          + eLpNorm (fun x => f_cut x - φ x) 2 volume
        < ENNReal.ofReal ε := by
    have h_add_le :=
      add_le_add h_cutoff_L2 hφ_cut_L2.le
    have h_tail_nonneg : 0 ≤ ε_tail₂ := le_of_lt htail₂
    have h_cut_nonneg : 0 ≤ ε_cut₂ := le_of_lt hcut₂
    have h_sum_eq :
        ENNReal.ofReal ε_tail₂ + ENNReal.ofReal ε_cut₂
          = ENNReal.ofReal (ε_tail₂ + ε_cut₂) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using (ENNReal.ofReal_add h_tail_nonneg h_cut_nonneg).symm
    have h_budget' :
        ENNReal.ofReal (ε_tail₂ + ε_cut₂)
          < ENNReal.ofReal ε := by
      have h_sum_lt : ε_tail₂ + ε_cut₂ < ε := by
        simpa [add_comm]
          using h_budget_L2
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 h_sum_lt
    refine lt_of_le_of_lt ?_ h_budget'
    simpa [h_sum_eq] using h_add_le
  refine ⟨φ, hφ_support_subset, ?_, ?_⟩
  · exact lt_of_le_of_lt h_triangle_L1 h_sum_lt_L1
  · exact lt_of_le_of_lt h_triangle_L2 h_sum_lt_L2
end Newton
