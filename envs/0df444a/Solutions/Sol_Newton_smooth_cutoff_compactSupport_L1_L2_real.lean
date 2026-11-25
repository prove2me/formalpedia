-- Prove2me | solution 1 for Newton.smooth_cutoff_compactSupport_L1_L2_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:18.294819+00:00
-- url     : https://prove2.me/submissions/e5201d4b-0f01-4cb9-b7c8-f7277a160916

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
import Theorems.Thm_Newton_cutoff_L1_bound
import Theorems.Thm_Newton_cutoff_L2_bound
import Theorems.Thm_Newton_integrable_tail_small
import Theorems.Thm_Newton_tail_bound_mono


set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (φ : ℝ → ℂ)
    (hφ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φ)
    (hφ_memLp₁ : MemLp φ 1 volume)
    (hφ_memLp₂ : MemLp φ 2 volume)
    {R : ℝ} (hR_pos : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ (∞ : WithTop ℕ∞) g ∧
      HasCompactSupport g ∧
      MemLp g 2 volume ∧
      eLpNorm (fun t => φ t - g t) 1 volume < ENNReal.ofReal ε ∧
      eLpNorm (fun t => φ t - g t) 2 volume < ENNReal.ofReal ε := by
  -- Identify ℝ with the one-dimensional Euclidean space `(Fin 1 → ℝ)`.
  have hn : 0 < (1 : ℕ) := by decide
  let E : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ :=
    { toLinearEquiv :=
        { toFun := fun x => x 0
          invFun := fun t _ => t
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl
          left_inv := by
            intro x
            funext i
            have : i = (0 : Fin 1) := Subsingleton.elim _ _
            simp [this]
          right_inv := by intro t; rfl }
      norm_map' := by
        intro x
        have hx_const : x = fun _ : Fin 1 => x 0 := by
          funext i
          have : i = (0 : Fin 1) := Subsingleton.elim _ _
          simp [this]
        have hx_norm' : ‖fun _ : Fin 1 => x 0‖ = ‖x‖ := by
          simpa using congrArg norm hx_const.symm
        have hx_norm'' : ‖fun _ : Fin 1 => x 0‖ = ‖x 0‖ := by
          simp
        have hx_norm : ‖x‖ = ‖x 0‖ := by
          simpa [hx_norm''] using hx_norm'.symm
        simp [hx_norm.symm] }
  -- Transport φ to `(Fin 1 → ℝ)`.
  let φF : (Fin 1 → ℝ) → ℂ := fun x => φ (E x)
  have hφF_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) φF :=
    hφ_smooth.comp (E.toLinearIsometry.contDiff)
  have h_pres_forward :
      MeasurePreserving (fun x : (Fin 1 → ℝ) => E x) := by
    simpa [E] using (volume_preserving_piUnique fun _ : Fin 1 => ℝ)
  have h_pres_symm : MeasurePreserving (fun t : ℝ => E.symm t) := by
    have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
    have h_eq : (fun t : ℝ => E.symm t) = ⇑(MeasurableEquiv.piUnique fun _ : Fin 1 => ℝ).symm := by
      funext t i; fin_cases i; rfl
    rw [h_eq]; exact h
  have hφF_memLp₁ : MemLp φF 1 volume :=
    hφ_memLp₁.comp_measurePreserving h_pres_forward
  have hφF_memLp₂ : MemLp φF 2 volume :=
    hφ_memLp₂.comp_measurePreserving h_pres_forward
  -- Reduce to constructing the approximation on `(Fin 1 → ℝ)`.
  suffices
      ∃ ψ : (Fin 1 → ℝ) → ℂ,
        ContDiff ℝ (∞ : WithTop ℕ∞) ψ ∧
        HasCompactSupport ψ ∧
        MemLp ψ 2 volume ∧
        eLpNorm (fun x => φF x - ψ x) 1 volume < ENNReal.ofReal ε ∧
        eLpNorm (fun x => φF x - ψ x) 2 volume < ENNReal.ofReal ε by
    obtain ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hψ_L1, hψ_L2⟩ := this
    let g : ℝ → ℂ := fun t => ψ (E.symm t)
    have hg_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) g :=
      hψ_smooth.comp (E.symm.toLinearIsometry.contDiff)
    have hg_support : HasCompactSupport g :=
      hψ_support.comp_homeomorph (E.symm.toHomeomorph)
    have hg_memLp : MemLp g 2 volume :=
      hψ_memLp.comp_measurePreserving h_pres_symm
    -- Compare L¹ and L² errors via measure preservation.
    have hφψ_meas₁ :
        AEStronglyMeasurable (fun x : (Fin 1 → ℝ) => φF x - ψ x) volume :=
      (hφF_smooth.continuous.aestronglyMeasurable.sub
        hψ_smooth.continuous.aestronglyMeasurable)
    have hφψ_meas₂ :
        AEStronglyMeasurable (fun x : (Fin 1 → ℝ) => φF x - ψ x) volume :=
      hφψ_meas₁
    have hφg_L1_eq :
        eLpNorm (fun t : ℝ => φ t - g t) (1 : ℝ≥0∞) volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => φF x - ψ x)
              (1 : ℝ≥0∞) volume := by
      have h_eq :=
          eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
            (p := (1 : ℝ≥0∞))
            (f := fun t : ℝ => E.symm t)
            (g := fun x : (Fin 1 → ℝ) => φF x - ψ x)
            hφψ_meas₁ h_pres_symm
      simpa [Function.comp_def, φF, g, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    have hφg_L2_eq :
        eLpNorm (fun t : ℝ => φ t - g t) (2 : ℝ≥0∞) volume
          = eLpNorm (fun x : (Fin 1 → ℝ) => φF x - ψ x)
              (2 : ℝ≥0∞) volume := by
      have h_eq :=
          eLpNorm_comp_measurePreserving (μ := volume) (ν := volume)
            (p := (2 : ℝ≥0∞))
            (f := fun t : ℝ => E.symm t)
            (g := fun x : (Fin 1 → ℝ) => φF x - ψ x)
            hφψ_meas₂ h_pres_symm
      simpa [Function.comp_def, φF, g, Pi.sub_def, sub_eq_add_neg]
        using h_eq
    refine ⟨g, hg_smooth, hg_support, hg_memLp, ?_, ?_⟩
    · have := hψ_L1
      simpa [hφg_L1_eq] using this
    · have := hψ_L2
      simpa [hφg_L2_eq] using this
  -- Split the error budget evenly for the tail bounds.
  let ε_tail : ℝ := ε / 2
  have hε_tail_pos : 0 < ε_tail :=
    by
      have : (0 : ℝ) < 2 := by norm_num
      simpa [ε_tail] using div_pos hε this
  have hε_tail_lt : ENNReal.ofReal ε_tail < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (by
      have : ε_tail < ε := by
        have h_half : ε / 2 < ε := half_lt_self hε
        simpa [ε_tail] using h_half
      exact this)
  -- Tail control in L¹ for `φF`.
  obtain ⟨R₁, hR₁_pos, hR₁_tail⟩ :=
    integrable_tail_small (f := φF) hφF_memLp₁ (ε := ε_tail) hε_tail_pos
  -- Tail control in L² comes from the squared norm.
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hφF_sq_integrable : Integrable (fun x => ‖φF x‖ ^ (2 : ℝ)) volume := by
    simpa [one_div]
      using
        (hφF_memLp₂.integrable_norm_rpow (μ := volume) hp0 hp_top)
  have hε_tail_sq_pos : 0 < ε_tail ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hε_tail_pos _
  obtain ⟨R₂, hR₂_pos, hR₂_tail_sq⟩ :=
    integrable_tail_small
      (f := fun x : (Fin 1 → ℝ) => Complex.ofReal (‖φF x‖ ^ (2 : ℝ)))
      (by
        have h_int_complex :
            Integrable (fun x : (Fin 1 → ℝ) =>
                Complex.ofReal (‖φF x‖ ^ (2 : ℝ))) volume := by
          simpa using hφF_sq_integrable.ofReal (μ := volume) (𝕜 := ℂ)
        simpa using (memLp_one_iff_integrable (μ := volume)).2 h_int_complex)
      (ε := ε_tail ^ (2 : ℝ)) hε_tail_sq_pos
  -- Use a radius dominating the prescribed `R` and both tail bounds.
  set Rtail : ℝ := max R₁ R₂ with hRtail_def
  set Rcut : ℝ := max R Rtail with hRcut_def
  have hRcut_pos : 0 < Rcut := by
    have hR_le : R ≤ Rcut := by simp [Rcut]
    exact lt_of_lt_of_le hR_pos hR_le
  have hR₁_le_Rcut : R₁ ≤ Rcut := by
    have hR₁_le_Rtail : R₁ ≤ Rtail := by simp [Rtail]
    have hRtail_le_Rcut : Rtail ≤ Rcut := by simp [Rcut]
    exact le_trans hR₁_le_Rtail hRtail_le_Rcut
  have hR₂_le_Rcut : R₂ ≤ Rcut := by
    have hR₂_le_Rtail : R₂ ≤ Rtail := by simp [Rtail]
    have hRtail_le_Rcut : Rtail ≤ Rcut := by simp [Rcut]
    exact le_trans hR₂_le_Rtail hRtail_le_Rcut
  -- Transfer tail bounds to the common radius `Rcut`.
  have h_tail_L1 :
      ∫ x, ‖φF x‖ ∂(volume.restrict {x : (Fin 1 → ℝ) | Rcut ≤ ‖x‖})
        < ε_tail := by
    have h_nonneg : ∀ x, 0 ≤ ‖φF x‖ := fun _ => norm_nonneg _
    have h_int := (memLp_one_iff_integrable (μ := volume)).1 hφF_memLp₁
    have h_int_tail :=
      (h_int.norm.restrict (s := {x : (Fin 1 → ℝ) | R₁ ≤ ‖x‖}))
    have hR₁_le : R₁ ≤ Rcut := hR₁_le_Rcut
    simpa [Rcut, hRcut_def]
      using
        tail_bound_mono (F := fun x : (Fin 1 → ℝ) => ‖φF x‖)
          (R₁ := R₁) (R₂ := Rcut) hR₁_le h_nonneg h_int_tail hR₁_tail
  have h_tail_L2_sq :
      ∫ x, ‖φF x‖ ^ (2 : ℝ)
          ∂(volume.restrict {x : (Fin 1 → ℝ) | Rcut ≤ ‖x‖})
        < ε_tail ^ (2 : ℝ) := by
    have h_nonneg : ∀ x, 0 ≤ ‖φF x‖ ^ (2 : ℝ) := fun x =>
      Real.rpow_nonneg (norm_nonneg _) _
    have h_int_tail :=
      (hφF_sq_integrable.restrict
        (s := {x : (Fin 1 → ℝ) | R₂ ≤ ‖x‖}))
    have hR₂_le : R₂ ≤ Rcut := hR₂_le_Rcut
    have hR₂_tail_sq_real :
        ∫ x, ‖φF x‖ ^ (2 : ℝ)
            ∂(volume.restrict {x : (Fin 1 → ℝ) | R₂ ≤ ‖x‖})
          < ε_tail ^ (2 : ℝ) := by
      have h_nonneg_val : ∀ x, 0 ≤ ‖φF x‖ ^ (2 : ℝ) :=
        fun x => Real.rpow_nonneg (norm_nonneg _) _
      have h_abs_eq :
          (fun x => ‖Complex.ofReal (‖φF x‖ ^ (2 : ℝ))‖)
            = fun x => ‖φF x‖ ^ (2 : ℝ) := by
        funext x
        simp [Complex.norm_real]
      simpa [h_abs_eq] using hR₂_tail_sq
    simpa [Rcut, hRcut_def]
      using
        tail_bound_mono (F := fun x => ‖φF x‖ ^ (2 : ℝ))
          (R₁ := R₂) (R₂ := Rcut) hR₂_le h_nonneg h_int_tail hR₂_tail_sq_real
  -- Convert the integral bound into an L² tail bound.
  have h_tail_L2 :
      eLpNorm (fun x => φF x) 2
          (volume.restrict {x : (Fin 1 → ℝ) | Rcut ≤ ‖x‖})
        < ENNReal.ofReal ε_tail := by
    have hφF_restrict :
        MemLp (fun x => φF x) 2
          (volume.restrict {x : (Fin 1 → ℝ) | Rcut ≤ ‖x‖}) :=
      hφF_memLp₂.restrict (μ := volume) _
    have h_eq :=
      hφF_restrict.eLpNorm_eq_integral_rpow_norm hp0 hp_top
    have h_nonneg :
        0 ≤ ∫ x, ‖φF x‖ ^ (2 : ℝ)
              ∂(volume.restrict {x : (Fin 1 → ℝ) | Rcut ≤ ‖x‖}) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have hε_tail_nonneg : 0 ≤ ε_tail := le_of_lt hε_tail_pos
    set I :=
        ∫ x, ‖φF x‖ ^ (2 : ℝ)
            ∂(volume.restrict {x : (Fin 1 → ℝ) | Rcut ≤ ‖x‖}) with hI_def
    have hI_nonneg : 0 ≤ I := by simpa [I, hI_def] using h_nonneg
    have hI_lt_sq : I < ε_tail ^ 2 := by
      have h_lt := h_tail_L2_sq
      simpa [I, hI_def, Real.rpow_natCast] using h_lt
    set A : ℝ := Real.sqrt I with hA_def
    have hA_lt : A < ε_tail := by
      have h_sq_lt := (Real.sqrt_lt hI_nonneg hε_tail_nonneg).2 hI_lt_sq
      simpa [A, hA_def] using h_sq_lt
    have hA_eq : A = I ^ (1 / 2 : ℝ) := by
      simpa [A, hA_def] using Real.sqrt_eq_rpow I
    have h_pow_lt : I ^ (1 / 2 : ℝ) < ε_tail := by
      simpa [hA_eq] using hA_lt
    have h_ofReal_lt :
        ENNReal.ofReal (I ^ (1 / 2 : ℝ)) < ENNReal.ofReal ε_tail :=
      (ENNReal.ofReal_lt_ofReal_iff hε_tail_pos).2 h_pow_lt
    simpa [h_eq, I, hI_def] using h_ofReal_lt
  -- Construct the smooth cutoff.
  have hR_lt : Rcut < Rcut + 1 := by linarith
  obtain ⟨χ, hχ_smooth, hχ_one, hχ_bounds, hχ_compact, hχ_support⟩ :=
    exists_smooth_cutoff (n := 1) Rcut (Rcut + 1) hRcut_pos hR_lt
  have hχ_nonneg : ∀ x, 0 ≤ χ x := fun x => (hχ_bounds x).1
  have hχ_le_one : ∀ x, χ x ≤ 1 := fun x => (hχ_bounds x).2
  -- Define the truncated function.
  set ψ : (Fin 1 → ℝ) → ℂ := fun x => (χ x : ℝ) • φF x with hψ_def
  have hψ_mul : ψ = fun x => (χ x : ℂ) * φF x := by
    funext x
    simp [ψ]
  -- Inside the radius `Rcut`, the cutoff does not change the function.
  have h_diff_zero_inside :
      ∀ {x : (Fin 1 → ℝ)}, ‖x‖ ≤ Rcut → φF x - ψ x = 0 := by
    intro x hx
    have hχx : χ x = 1 := hχ_one x hx
    simp [hψ_def, hχx]
  -- Bounds on the L¹/L² errors produced by the cutoff.
  have h_cutoff_L1_le :
      eLpNorm (fun x => φF x - ψ x) 1 volume
        ≤ ENNReal.ofReal ε_tail := by
    simpa [hψ_mul] using
      cutoff_L1_bound (n := 1)
        (f := φF) (f_cut := fun x => (χ x : ℂ) * φF x)
        hφF_memLp₁ χ Rcut ε_tail
        hχ_nonneg hχ_le_one rfl h_diff_zero_inside h_tail_L1 hε_tail_pos
  have h_cutoff_L2_le :
      eLpNorm (fun x => φF x - ψ x) 2 volume
        ≤ ENNReal.ofReal ε_tail := by
    simpa [hψ_mul] using
      cutoff_L2_bound (n := 1)
        (f := φF) (f_cut := fun x => (χ x : ℂ) * φF x)
        χ Rcut ε_tail
        hχ_nonneg hχ_le_one rfl h_diff_zero_inside h_tail_L2
  have hψ_L1 :
      eLpNorm (fun x => φF x - ψ x) 1 volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt h_cutoff_L1_le hε_tail_lt
  have hψ_L2 :
      eLpNorm (fun x => φF x - ψ x) 2 volume < ENNReal.ofReal ε :=
    lt_of_le_of_lt h_cutoff_L2_le hε_tail_lt
  -- Regularity of the truncated function.
  have hψ_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) ψ :=
    (hχ_smooth.smul hφF_smooth)
  -- Compact support.
  have hψ_support : HasCompactSupport ψ := by
    refine HasCompactSupport.intro
        (K := Metric.closedBall (0 : Fin 1 → ℝ) (Rcut + 1))
        (isCompact_closedBall _ _) ?_
    intro x hx
    have hx_not_ball : x ∉ Metric.closedBall (0 : Fin 1 → ℝ) (Rcut + 1) := hx
    have hx_not_tsupport : x ∉ tsupport χ := by
      intro hx_mem
      exact hx_not_ball (hχ_support hx_mem)
    have hx_zero : χ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_tsupport
    simp [ψ, hx_zero]
  -- `ψ` lies in L² because it is continuous with compact support.
  have hψ_memLp : MemLp ψ 2 volume := by
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    exact hψ_cont.memLp_of_hasCompactSupport hψ_support
  exact ⟨ψ, hψ_smooth, hψ_support, hψ_memLp, hψ_L1, hψ_L2⟩
end Newton
