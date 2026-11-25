-- Prove2me | solution 1 for Newton.schwartz_dense_L1_L2_simultaneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:53.099372+00:00
-- url     : https://prove2.me/submissions/a84aaea5-d475-437c-aad3-4447ca956ef8

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
import Theorems.Thm_Newton_cutoff_then_convolve_Lp
import Theorems.Thm_Newton_integrable_tail_small
import Theorems.Thm_Newton_tail_bound_mono


set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f : (Fin n → ℝ) → ℂ)
    (hf_L1 : MemLp f 1 (volume : Measure (Fin n → ℝ)))
    (hf_L2 : MemLp f 2 (volume : Measure (Fin n → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
  ∃ φ : 𝓢((Fin n → ℝ), ℂ),
      eLpNorm (fun x => f x - φ x) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun x => f x - φ x) 2 volume < ENNReal.ofReal ε := by
  let ε_cut₁ : ℝ := ε / 4
  let ε_tail₁ : ℝ := ε / 4
  let ε_cut₂ : ℝ := ε / 4
  let ε_tail₂ : ℝ := ε / 4
  have hε_cut₁_pos : 0 < ε_cut₁ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_cut₁] using div_pos hε hden
  have hε_tail₁_pos : 0 < ε_tail₁ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_tail₁] using div_pos hε hden
  have hε_cut₂_pos : 0 < ε_cut₂ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_cut₂] using div_pos hε hden
  have hε_tail₂_pos : 0 < ε_tail₂ := by
    have hden : (0 : ℝ) < 4 := by norm_num
    simpa [ε_tail₂] using div_pos hε hden
  have h_budget_L1 : ε_cut₁ + ε_tail₁ < ε := by
    have h_half : ε / 2 < ε := half_lt_self hε
    have h_sum₀ : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_sum : ε_cut₁ + ε_tail₁ = ε / 2 := by
      simpa [ε_cut₁, ε_tail₁] using h_sum₀
    simpa [h_sum] using h_half
  have h_budget_L2 : ε_cut₂ + ε_tail₂ < ε := by
    have h_half : ε / 2 < ε := half_lt_self hε
    have h_sum₀ : ε / 4 + ε / 4 = ε / 2 := by ring
    have h_sum : ε_cut₂ + ε_tail₂ = ε / 2 := by
      simpa [ε_cut₂, ε_tail₂] using h_sum₀
    simpa [h_sum] using h_half
  -- Tail control in L¹.
  obtain ⟨R₁, hR₁_pos, hR₁_tail⟩ :=
    integrable_tail_small (f := f) hf_L1 (ε := ε_tail₁) hε_tail₁_pos
  -- Tail control in L² is obtained by applying the tail lemma to the function
  -- `‖f‖²`, and then converting the bound to an `L²`-norm bound.
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hf_sq_integrable : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) volume := by
    simpa [one_div] using
      (hf_L2.integrable_norm_rpow (μ := volume) hp0 hp_top)
  -- The function `‖f‖²` is non-negative, so we can apply the tail lemma to it.
  have hε_tail₂_sq_pos : 0 < ε_tail₂ ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hε_tail₂_pos _
  obtain ⟨R₂, hR₂_pos, hR₂_tail_sq⟩ :=
    integrable_tail_small
      (f := fun x => Complex.ofReal (‖f x‖ ^ (2 : ℝ)))
      (by
        -- Show that `‖f‖²` considered as a complex-valued function is in `L¹`.
        have h_int_complex :
            Integrable (fun x => Complex.ofReal (‖f x‖ ^ (2 : ℝ))) volume := by
          simpa using hf_sq_integrable.ofReal (μ := volume) (𝕜 := ℂ)
        simpa using (memLp_one_iff_integrable).2 h_int_complex)
      (ε := ε_tail₂ ^ (2 : ℝ)) hε_tail₂_sq_pos
  -- Combine the L¹ and L² tail bounds by taking the larger radius.
  set R : ℝ := max R₁ R₂ with hR_def
  have hR_pos : 0 < R := by
    have hR₁_le : R₁ ≤ R := by
      simp [R]
    exact lt_of_lt_of_le hR₁_pos hR₁_le
  -- Monotonicity lets us transfer the tail bounds to the radius `R`.
  have h_tail_L1 :
      ∫ x, ‖f x‖ ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ε_tail₁ := by
    have h_nonneg : ∀ x, 0 ≤ ‖f x‖ := fun _ => norm_nonneg _
    have h_int := (memLp_one_iff_integrable).1 hf_L1
    have h_int_tail :=
      (h_int.norm.restrict (s := {x : (Fin n → ℝ) | R₁ ≤ ‖x‖}))
    have hR_le : R₁ ≤ R := by
      simp [R]
    simpa [R, hR_def] using
      tail_bound_mono (F := fun x => ‖f x‖)
        (R₁ := R₁) (R₂ := R) hR_le h_nonneg h_int_tail hR₁_tail
  have h_tail_L2_sq :
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖})
        < ε_tail₂ ^ (2 : ℝ) := by
    have h_nonneg : ∀ x, 0 ≤ ‖f x‖ ^ (2 : ℝ) := fun x =>
      Real.rpow_nonneg (norm_nonneg _) _
    have h_int_tail :=
      (hf_sq_integrable.restrict (s := {x : (Fin n → ℝ) | R₂ ≤ ‖x‖}))
    have hR₂_le : R₂ ≤ R := by
      simp [R]
    have hR₂_tail_sq_real :
        ∫ x, ‖f x‖ ^ (2 : ℝ)
            ∂(volume.restrict {x : (Fin n → ℝ) | R₂ ≤ ‖x‖})
          < ε_tail₂ ^ (2 : ℝ) := by
      have h_nonneg_val : ∀ x, 0 ≤ ‖f x‖ ^ (2 : ℝ) :=
        fun x => Real.rpow_nonneg (norm_nonneg _) _
      have h_abs_eq :
          (fun x => ‖Complex.ofReal (‖f x‖ ^ (2 : ℝ))‖)
            = fun x => ‖f x‖ ^ (2 : ℝ) := by
        funext x
        simp [Complex.norm_real]
      simpa [h_abs_eq] using hR₂_tail_sq
    simpa [R, hR_def] using
      tail_bound_mono (F := fun x => ‖f x‖ ^ (2 : ℝ))
        (R₁ := R₂) (R₂ := R) hR₂_le h_nonneg h_int_tail hR₂_tail_sq_real
  -- Convert the integral bound on `‖f‖²` into an `L²` bound.
  have h_tail_L2 :
      eLpNorm (fun x => f x) 2
          (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) < ENNReal.ofReal ε_tail₂ := by
    -- On the restricted measure we have membership in L².
    have hf_restrict :
        MemLp (fun x => f x) 2 (volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) :=
      hf_L2.restrict (μ := volume) _
    have h_eq :=
      hf_restrict.eLpNorm_eq_integral_rpow_norm hp0 hp_top
    have h_nonneg :
        0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hε_tail₂_nonneg : 0 ≤ ε_tail₂ := le_of_lt hε_tail₂_pos
    set I :=
        ∫ x, ‖f x‖ ^ (2 : ℝ)
            ∂(volume.restrict {x : (Fin n → ℝ) | R ≤ ‖x‖}) with hI_def
    have hI_nonneg : 0 ≤ I := by simpa [I, hI_def] using h_nonneg
    have hI_lt_sq : I < ε_tail₂ ^ 2 := by
      have h_lt := h_tail_L2_sq
      simpa [I, hI_def, Real.rpow_natCast] using h_lt
    set A : ℝ := Real.sqrt I with hA_def
    have hA_lt : A < ε_tail₂ := by
      have h_sq_lt := (Real.sqrt_lt hI_nonneg hε_tail₂_nonneg).2 hI_lt_sq
      simpa [A, hA_def] using h_sq_lt
    have hA_eq : A = I ^ (1 / 2 : ℝ) := by
      simpa [A, hA_def] using Real.sqrt_eq_rpow I
    have h_pow_lt : I ^ (1 / 2 : ℝ) < ε_tail₂ := by
      simpa [hA_eq] using hA_lt
    have h_ofReal_lt :
        ENNReal.ofReal (I ^ (1 / 2 : ℝ)) < ENNReal.ofReal ε_tail₂ :=
      (ENNReal.ofReal_lt_ofReal_iff hε_tail₂_pos).2 h_pow_lt
    simpa [h_eq, I, hI_def] using h_ofReal_lt
  obtain ⟨φ, hφ_support, hφ_L1, hφ_L2⟩ :=
    cutoff_then_convolve_Lp (n := n) f hf_L1 hf_L2 R hR_pos
      (ε := ε) (ε_cut₁ := ε_cut₁) (ε_cut₂ := ε_cut₂)
      (ε_tail₁ := ε_tail₁) (ε_tail₂ := ε_tail₂)
      hε hε_cut₁_pos hε_cut₂_pos hε_tail₁_pos hε_tail₂_pos
      h_budget_L1 h_budget_L2 h_tail_L1 h_tail_L2
  exact ⟨φ, hφ_L1, hφ_L2⟩
end Newton
