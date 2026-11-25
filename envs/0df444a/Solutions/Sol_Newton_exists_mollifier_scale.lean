-- Prove2me | solution 1 for Newton.exists_mollifier_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:01:53.989657+00:00
-- url     : https://prove2.me/submissions/182cda39-5056-4405-94a7-f64e25913835

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
import Theorems.Thm_Newton_triangle_inequality_aux
import Theorems.Thm_Newton_continuous_compactSupport_dense_Lp
import Theorems.Thm_Newton_mollifier_compactSupport_Lp_approx
import Theorems.Thm_Newton_mollifier_converges_Lp
import Theorems.Thm_Newton_mollifier_convolution_diff_L1


set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f₀ : (Fin n → ℝ) → ℂ)
    (hf₀_L1 : MemLp f₀ 1 volume)
    (hf₀_L2 : MemLp f₀ 2 volume)
    (ε₁ ε₂ : ℝ) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ (η : ℝ) (_ : 0 < η) (_ : η ≤ 1) (ψ : (Fin n → ℝ) → ℝ),
      ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      (∫ x, ψ x = 1) ∧
      (∀ x, 0 ≤ ψ x) ∧
      tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 ∧
      (let ψ_η := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
       let φ := fun x => ∫ y, f₀ (x - y) * ψ_η y
       eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ ∧
       eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂) := by
  -- Construct a basic mollifier using ContDiffBump
  -- We use a bump function supported in the unit ball
  let ψ_base : ContDiffBump (0 : Fin n → ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  -- The mollifier needs to be normalized so that ∫ ψ = 1
  -- For a ContDiffBump, the integral is positive and finite
  have h_integral_pos : 0 < ∫ x, ψ_base x := by
    -- Lean's bundled bump functions know their integral is positive on any
    -- open-positive measure (here, Lebesgue measure on ℝⁿ).
    simpa using
      (ContDiffBump.integral_pos (μ := (volume : Measure (Fin n → ℝ))) (f := ψ_base))
  have h_integral_finite : Integrable (fun x => ψ_base x) volume := by
    -- The bump function has compact support and is continuous, so it's integrable
    apply Continuous.integrable_of_hasCompactSupport
    · exact ψ_base.continuous
    · exact ψ_base.hasCompactSupport
  -- Define the normalization constant
  let C := ∫ x, ψ_base x
  have hC_pos : 0 < C := h_integral_pos
  have hC_ne_zero : C ≠ 0 := ne_of_gt hC_pos
  -- Normalized mollifier
  let ψ : (Fin n → ℝ) → ℝ := fun x => (1 / C) * ψ_base x
  -- Verify properties of ψ
  have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ := by
    apply ContDiff.mul
    · exact contDiff_const
    · exact ψ_base.contDiff
  have hψ_compact : HasCompactSupport ψ := by
    apply HasCompactSupport.mul_left
    exact ψ_base.hasCompactSupport
  have hψ_integral_one : ∫ x, ψ x = 1 := by
    simp only [ψ, C]
    have : ∫ x, (1 / ∫ x, ψ_base x) * ψ_base x = 1 := by
      rw [integral_const_mul]
      field_simp [ne_of_gt h_integral_pos]
    convert this using 1
  have hψ_nonneg : ∀ x, 0 ≤ ψ x := by
    intro x
    simp only [ψ]
    apply mul_nonneg
    · exact div_nonneg zero_le_one (le_of_lt hC_pos)
    · exact ψ_base.nonneg' x
  have hψ_support : tsupport ψ ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    have h_subset_base :
        tsupport ψ ⊆ tsupport (fun x : Fin n → ℝ => ψ_base x) := by
      -- Scaling by a constant does not enlarge the (topological) support.
      simpa [ψ, C, Pi.mul_def] using
        (tsupport_mul_subset_right
          (f := fun _ : (Fin n → ℝ) => (1 / C))
          (g := fun x : (Fin n → ℝ) => ψ_base x))
    have h_tsupp_base :
        tsupport (fun x : Fin n → ℝ => ψ_base x) =
          Metric.closedBall (0 : Fin n → ℝ) 1 := by
      simpa using ψ_base.tsupport_eq
    exact h_subset_base.trans <| by simp [h_tsupp_base]
  set ε := min ε₁ ε₂
  have hε_pos : 0 < ε := lt_min hε₁ hε₂
  have hε_le₁ : ε ≤ ε₁ := min_le_left _ _
  have hε_le₂ : ε ≤ ε₂ := min_le_right _ _
  have h_exists_eta : ∃ η_min > 0, ∀ η, 0 < η → η < η_min →
      ∃ φ : (Fin n → ℝ) → ℂ,
        (let ψ_η := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
         φ = fun x => ∫ y, f₀ (x - y) * ψ_η y) ∧
        eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε ∧
        eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε := by
    have h_conv_L1 : ∀ ε' > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
        eLpNorm (fun x => f₀ x -
          ∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) 1 volume
            < ENNReal.ofReal ε' := by
      intro ε' hε'
      have h_exists_cont : ∃ g : (Fin n → ℝ) → ℂ,
          Continuous g ∧ HasCompactSupport g ∧
          eLpNorm (fun x => f₀ x - g x) 1 volume < ENNReal.ofReal (ε' / 4) := by
        -- Apply the density theorem for continuous compactly supported functions
        have hε'_fourth : 0 < ε' / 4 := by linarith
        obtain ⟨g, hg_cont, hg_compact, hg_memLp, hg_close⟩ :=
          continuous_compactSupport_dense_Lp 1 (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
            f₀ hf₀_L1 hε'_fourth
        use g
        exact ⟨hg_cont, hg_compact, hg_close⟩
      obtain ⟨g, hg_cont, hg_compact, hg_approx⟩ := h_exists_cont
      -- For the continuous function g, find a smooth approximation
      -- Apply mollifier_compactSupport_Lp_approx to g
      have h_smooth_exists := mollifier_compactSupport_Lp_approx 1 le_rfl g hg_cont hg_compact
        (by linarith : 0 < ε' / 4)
      obtain ⟨φ_g, hφ_g_smooth, hφ_g_close, _⟩ := h_smooth_exists
      -- For the goal, we need to estimate the convolution
      -- The key insight is that for any fixed functions, we can choose δ small enough
      -- We appeal to the quantitative convergence result for mollifiers.
      have hψ_AI : IsApproximateIdentity ψ :=
        ⟨hψ_smooth, hψ_compact, by simpa using hψ_integral_one, hψ_nonneg, hψ_support⟩
      have hg_integrable : Integrable g volume :=
        hg_cont.integrable_of_hasCompactSupport hg_compact
      have hg_memLp : MemLp g 1 volume := (memLp_one_iff_integrable (μ := volume)).2 hg_integrable
      have h_one_le_one : (1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := le_refl _
      have h_one_ne_top : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
      obtain ⟨δ₀, hδ₀_pos, hδ₀_bound⟩ :=
        (mollifier_converges_Lp g ψ 1 h_one_le_one h_one_ne_top hg_memLp hψ_AI)
          (ε' / 4) (by linarith)
      use min δ₀ 1
      constructor
      · exact lt_min hδ₀_pos (by norm_num)
      · intro η hη_pos hη_lt
        have hη_lt_δ₀ : η < δ₀ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have hη_lt_one : η < 1 := lt_of_lt_of_le hη_lt (min_le_right _ _)
        -- We need to show that the convolution is close to f₀
        have h_g_conv_bound_integral :
            eLpNorm (fun x => g x - ∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ))
              1 volume < ENNReal.ofReal (ε' / 4) := by
          -- Apply the quantitative L¹ convergence of mollifiers for continuous data.
          have := hδ₀_bound η hη_pos hη_lt_δ₀
          simpa [scaledMollifier] using this
        -- Convolution is linear, so
        -- ‖g*ψ_η - f₀*ψ_η‖₁ = ‖(g - f₀)*ψ_η‖₁ ≤ ‖g - f₀‖₁ · ‖ψ_η‖₁
        -- by Young's inequality
        have h_conv_diff_bound_integral :
            eLpNorm (fun x =>
              (∫ y, g (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) -
              (∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)))
              1 volume < ENNReal.ofReal (ε' / 4) := by
          have hg_minus_f0_lt :
              eLpNorm (fun x => g x - f₀ x) 1 volume < ENNReal.ofReal (ε' / 4) := by
            have h_symm :
                eLpNorm (fun x => g x - f₀ x) 1 volume =
                  eLpNorm (fun x => f₀ x - g x) 1 volume := by
              have hneg_pointwise :
                  (fun x => g x - f₀ x) = fun x => -(f₀ x - g x) := by
                funext x
                simp [sub_eq_add_neg]
              have hneg_ae :
                  (fun x => g x - f₀ x) =ᵐ[volume] fun x => -(f₀ x - g x) :=
                Filter.Eventually.of_forall <| by
                  intro x
                  simp [sub_eq_add_neg]
              have hneg_eq :=
                eLpNorm_congr_ae (μ := volume) (p := (1 : ℝ≥0∞)) hneg_ae
              have hneg_symm :=
                eLpNorm_neg (f := fun x => f₀ x - g x) (p := (1 : ℝ≥0∞)) (μ := volume)
              exact hneg_eq.trans hneg_symm
            simpa [h_symm] using hg_approx
          have hf₀_integrable : Integrable f₀ volume := by
            simpa [memLp_one_iff_integrable] using hf₀_L1
          have h_bound := mollifier_convolution_diff_L1 (g := g) (f₀ := f₀) (ψ := ψ)
              hg_integrable hf₀_integrable hψ_nonneg hψ_integral_one
          have h_conv_diff_le := h_bound η hη_pos hη_lt_one
          exact lt_of_le_of_lt h_conv_diff_le hg_minus_f0_lt
        -- Combine the three bounds using the auxiliary inequality.
        set ψη : (Fin n → ℝ) → ℝ := fun y => (η ^ n : ℝ)⁻¹ * ψ (fun i => y i / η)
        let ψηC : (Fin n → ℝ) → ℂ := fun y => (ψη y : ℝ)
        let conv_g : (Fin n → ℝ) → ℂ :=
          fun x => ∫ y, g (x - y) * ψηC y
        let conv_f₀ : (Fin n → ℝ) → ℂ :=
          fun x => ∫ y, f₀ (x - y) * ψηC y
        have hη_ne_zero : (η : ℝ) ≠ 0 := ne_of_gt hη_pos
        have hψη_eq :
            ψη =
              (fun _ : Fin n → ℝ => (η ^ n : ℝ)⁻¹) * fun y : Fin n → ℝ => ψ (η⁻¹ • y) := by
          funext y
          have hfun :
              (fun i => y i / η) = fun i => (η⁻¹ : ℝ) * y i := by
            funext i
            simp [div_eq_mul_inv, mul_comm]
          have hsmul :
              (η⁻¹ • y) = fun i => (η⁻¹ : ℝ) * y i := by
            funext i
            simp [Pi.smul_apply]
          simp [ψη, hfun, hsmul, Pi.mul_apply]
        have hψη_compact : HasCompactSupport ψη := by
          have h_comp : HasCompactSupport (fun y : Fin n → ℝ => ψ ((1 / η) • y)) := by
            simpa [one_div] using
              (HasCompactSupport.comp_smul (α := Fin n → ℝ) (β := ℝ) (G₀ := ℝ)
                hψ_compact (inv_ne_zero hη_ne_zero))
          have h_mul :=
            HasCompactSupport.mul_left
              (f := fun _ : Fin n → ℝ => (η ^ n : ℝ)⁻¹)
              (f' := fun y : Fin n → ℝ => ψ ((1 / η) • y)) h_comp
          simpa [hψη_eq] using h_mul
        have hψη_cont : Continuous ψη := by
          have h_const : Continuous fun _ : Fin n → ℝ => (η ^ n : ℝ)⁻¹ :=
            continuous_const
          have h_scale : Continuous fun y : Fin n → ℝ => (1 / η : ℝ) • y :=
            continuous_const_smul (1 / η : ℝ)
          have h_comp : Continuous fun y : Fin n → ℝ => ψ ((1 / η) • y) :=
            hψ_smooth.continuous.comp h_scale
          simpa [hψη_eq] using h_const.mul h_comp
        have hψηC_compact : HasCompactSupport ψηC := by
          rw [hasCompactSupport_iff_eventuallyEq] at hψη_compact ⊢
          exact hψη_compact.mono (by intro x hx; simp [ψηC, hx])
        have hψηC_cont : Continuous ψηC :=
          continuous_ofReal.comp hψη_cont
        have hη_pow_ne_zero : (η ^ n : ℝ) ≠ 0 := by
          simpa using pow_ne_zero n hη_ne_zero
        have hψηC_rewrite :
            ψηC = fun y : Fin n → ℝ => ((↑η : ℂ) ^ n)⁻¹ * ↑(ψ fun i => y i / η) := by
          funext y
          simp [ψηC, ψη, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
            div_eq_mul_inv]
        have hg_locInt : LocallyIntegrable g volume :=
          hg_integrable.locallyIntegrable
        have hf₀_integrable : Integrable f₀ volume := by
          simpa [memLp_one_iff_integrable] using hf₀_L1
        have hf₀_locInt : LocallyIntegrable f₀ volume :=
          hf₀_integrable.locallyIntegrable
        have h_conv_g_eq :
            conv_g =
              fun x => (g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψηC) x := by
          funext x
          have hconv :=
            convolution_mul_swap (μ := volume) (G := Fin n → ℝ)
              (f := g) (g := ψηC) (x := x)
          have h_eq : (g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψηC) x =
              (g ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ψηC) x := by
            simp [MeasureTheory.convolution_def]
          rw [h_eq]; exact hconv.symm
        have h_conv_f₀_eq :
            conv_f₀ =
              fun x => (f₀ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψηC) x := by
          funext x
          have hconv :=
            convolution_mul_swap (μ := volume) (G := Fin n → ℝ)
              (f := f₀) (g := ψηC) (x := x)
          have h_eq : (f₀ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψηC) x =
              (f₀ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ψηC) x := by
            simp [MeasureTheory.convolution_def]
          rw [h_eq]; exact hconv.symm
        have h_conv_g_cont : Continuous conv_g := by
          have := hψηC_compact.continuous_convolution_right
            (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
            hg_locInt hψηC_cont
          simpa [conv_g, h_conv_g_eq] using this
        have h_conv_f₀_cont : Continuous conv_f₀ := by
          have := hψηC_compact.continuous_convolution_right
            (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
            hf₀_locInt hψηC_cont
          simpa [conv_f₀, h_conv_f₀_eq] using this
        have h_conv_f₀_integrand :
            conv_f₀ =
              fun x : Fin n → ℝ =>
                ∫ y, f₀ (x - y) * (((↑η : ℂ) ^ n)⁻¹ * ↑(ψ fun i => y i / η)) := by
          funext x
          simp [conv_f₀, hψηC_rewrite]
        have hf₀_aesm : AEStronglyMeasurable f₀ volume :=
          hf₀_L1.aestronglyMeasurable
        have hf_diff_meas :
            AEStronglyMeasurable (fun x => f₀ x - g x) volume :=
          hf₀_aesm.sub hg_cont.aestronglyMeasurable
        have hg_diff_meas :
            AEStronglyMeasurable (fun x => g x - conv_g x) volume :=
          AEStronglyMeasurable.sub hg_cont.aestronglyMeasurable h_conv_g_cont.aestronglyMeasurable
        have hh_diff_meas :
            AEStronglyMeasurable (fun x => conv_g x - conv_f₀ x) volume :=
          h_conv_g_cont.aestronglyMeasurable.sub h_conv_f₀_cont.aestronglyMeasurable
        have h_g_conv_bound :
            eLpNorm (fun x => g x - conv_g x) 1 volume < ENNReal.ofReal (ε' / 4) := by
          simpa [conv_g, ψηC, ψη, Pi.mul_apply, Pi.smul_apply, one_div, div_eq_mul_inv,
            mul_comm, mul_left_comm, mul_assoc, integral_const_mul] using
            h_g_conv_bound_integral
        have h_conv_diff_bound :
            eLpNorm (fun x => conv_g x - conv_f₀ x) 1 volume < ENNReal.ofReal (ε' / 4) := by
          simpa [conv_g, conv_f₀, ψηC, ψη, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc, Pi.mul_apply, Pi.smul_apply, one_div, div_eq_mul_inv, mul_comm,
            mul_left_comm, mul_assoc]
            using h_conv_diff_bound_integral
        have h_triangle :=
          triangle_inequality_aux
            (f := fun x => f₀ x - g x)
            (g := fun x => g x - conv_g x)
            (h := fun x => conv_g x - conv_f₀ x)
            (hf_meas := hf_diff_meas)
            (hg_meas := hg_diff_meas)
            (hh_meas := hh_diff_meas)
            (ε := ε') (ε₁ := ε' / 4) (ε₂ := ε' / 4) (ε₃ := ε' / 4)
            hg_approx h_g_conv_bound h_conv_diff_bound (by nlinarith)
        have h_decomp :
            (fun x => f₀ x - conv_f₀ x)
              = fun x =>
                (f₀ x - g x)
                + (g x - conv_g x)
                + (conv_g x - conv_f₀ x) := by
          funext x
          simp [conv_g, conv_f₀, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        simpa [conv_g, h_conv_f₀_integrand, h_decomp]
          using h_triangle
    have h_conv_L2 : ∀ ε' > 0, ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ →
        eLpNorm (fun x => f₀ x -
          ∫ y, f₀ (x - y) * (↑(η^(-(n : ℝ)) * ψ (fun i => y i / η)) : ℂ)) 2 volume
            < ENNReal.ofReal ε' := by
      intro ε' hε'
      -- Similar strategy to L¹ case, but for L²
      -- Get a continuous approximation in L²
      have h_exists_cont : ∃ g : (Fin n → ℝ) → ℂ,
          Continuous g ∧ HasCompactSupport g ∧
          eLpNorm (fun x => f₀ x - g x) 2 volume < ENNReal.ofReal (ε' / 4) := by
        -- Apply the density theorem for continuous compactly supported functions
        have hε'_fourth : 0 < ε' / 4 := by linarith
        obtain ⟨g, hg_cont, hg_compact, hg_memLp, hg_close⟩ :=
          continuous_compactSupport_dense_Lp (2 : ℝ≥0∞) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
            f₀ hf₀_L2 hε'_fourth
        use g
        exact ⟨hg_cont, hg_compact, hg_close⟩
      obtain ⟨g, hg_cont, hg_compact, hg_approx⟩ := h_exists_cont
      -- For the continuous function g, find a smooth approximation in L²
      have h_smooth_exists := mollifier_compactSupport_Lp_approx (2 : ℝ≥0∞)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) g hg_cont hg_compact (by linarith : 0 < ε' / 4)
      obtain ⟨φ_g, hφ_g_smooth, hφ_g_close, _⟩ := h_smooth_exists
      have hψ_AI : IsApproximateIdentity ψ :=
        ⟨hψ_smooth, hψ_compact, by simpa using hψ_integral_one, hψ_nonneg, hψ_support⟩
      -- Obtain quantitative convergence from the L² mollifier theorem
      have h_one_two : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
      have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      obtain ⟨δ₀, hδ₀_pos, hδ₀_bound⟩ :=
        (mollifier_converges_Lp f₀ ψ 2 h_one_two h_two_ne_top hf₀_L2 hψ_AI) ε' hε'
      use min δ₀ 1
      constructor
      · exact lt_min hδ₀_pos (by norm_num)
      · intro η hη_pos hη_lt
        have hη_lt_δ₀ : η < δ₀ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have h_bound := hδ₀_bound η hη_pos hη_lt_δ₀
        -- The integral appearing in `hδ₀_bound` matches the goal after unfolding
        -- the definition of `scaledMollifier`.
        simpa [scaledMollifier] using h_bound
    obtain ⟨δ₁, hδ₁_pos, h₁⟩ := h_conv_L1 ε hε_pos
    obtain ⟨δ₂, hδ₂_pos, h₂⟩ := h_conv_L2 ε hε_pos
    -- Take η_min to be the minimum of δ₁ and δ₂
    use min δ₁ δ₂
    constructor
    · exact lt_min hδ₁_pos hδ₂_pos
    · intro η hη_pos hη_lt
      -- Define the convolution
      let ψ_η : (Fin n → ℝ) → ℝ := fun x => η^(-(n : ℝ)) * ψ (fun i => x i / η)
      let φ : (Fin n → ℝ) → ℂ := fun x => ∫ y, f₀ (x - y) * (↑(ψ_η y) : ℂ)
      use φ
      constructor
      · -- Show φ equals the convolution
        rfl
      constructor
      · -- L¹ bound
        have hη_lt₁ : η < δ₁ := lt_of_lt_of_le hη_lt (min_le_left _ _)
        have := h₁ η hη_pos hη_lt₁
        convert this using 2
      · -- L² bound
        have hη_lt₂ : η < δ₂ := lt_of_lt_of_le hη_lt (min_le_right _ _)
        have := h₂ η hη_pos hη_lt₂
        convert this using 2
  -- Extract a specific η from the existence result
  obtain ⟨η_min, hη_min_pos, h_forall_eta⟩ := h_exists_eta
  -- Choose η = min(η_min/2, 1/2) to ensure η ≤ 1
  set η := min (η_min / 2) (1 / 2) with hη_def
  have hη_pos : 0 < η := by
    rw [hη_def]
    apply lt_min
    · exact half_pos hη_min_pos
    · norm_num
  have hη_le_one : η ≤ 1 := by
    rw [hη_def]
    calc min (η_min / 2) (1 / 2)
        ≤ 1 / 2 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hη_lt : η < η_min := by
    rw [hη_def]
    calc min (η_min / 2) (1 / 2)
        ≤ η_min / 2 := min_le_left _ _
      _ < η_min := half_lt_self hη_min_pos
  obtain ⟨φ, hφ_def, hφ_L1, hφ_L2⟩ := h_forall_eta η hη_pos hη_lt
  use η, hη_pos, hη_le_one, ψ
  constructor
  · exact hψ_smooth
  constructor
  · exact hψ_compact
  constructor
  · exact hψ_integral_one
  constructor
  · exact hψ_nonneg
  constructor
  · exact hψ_support
  · -- Show the approximation properties
    -- Since ε = min(ε₁, ε₂), we have ε ≤ ε₁ and ε ≤ ε₂
    -- Thus ENNReal.ofReal ε ≤ ENNReal.ofReal ε₁ and ENNReal.ofReal ε ≤ ENNReal.ofReal ε₂
    have hε₁_bound : ENNReal.ofReal ε ≤ ENNReal.ofReal ε₁ := by
      apply ENNReal.ofReal_le_ofReal
      exact hε_le₁
    have hε₂_bound : ENNReal.ofReal ε ≤ ENNReal.ofReal ε₂ := by
      apply ENNReal.ofReal_le_ofReal
      exact hε_le₂
    have hφ_L1' :
        eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ :=
      lt_of_lt_of_le hφ_L1 hε₁_bound
    have hφ_L2' :
        eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂ :=
      lt_of_lt_of_le hφ_L2 hε₂_bound
    have h_pair :
        eLpNorm (fun x => f₀ x - φ x) 1 volume < ENNReal.ofReal ε₁ ∧
        eLpNorm (fun x => f₀ x - φ x) 2 volume < ENNReal.ofReal ε₂ :=
      ⟨hφ_L1', hφ_L2'⟩
    simpa [hφ_def] using h_pair
end Newton
