-- Prove2me | solution 1 for MathematicsOfWater.pipeFlow_eq_poiseuilleProfile
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T16:33:15.650989+00:00
-- url     : https://prove2.me/submissions/8cd23fc1-e62d-4144-a138-d35908e16959

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow

set_option autoImplicit false

open MathematicsOfWater Real in
theorem radial_gen_sol_aux (η L Δp R : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hR : 0 < R)
    (hv : SatisfiesRadialStokesODE η L Δp R v) :
    ∃ C₁ C₂ : ℝ, ∀ r ∈ Set.Ioo 0 R,
      v r = -(Δp / (η * L)) * r ^ 2 / 4 + C₁ * Real.log r + C₂ := by
  have hG : ∀ r ∈ Set.Ioo (0:ℝ) R,
      HasDerivAt (fun s => s * deriv v s) (-(Δp / (η * L)) * r) r := by
    intro r hr
    obtain ⟨_, hd, he⟩ := hv r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have hdr : deriv (fun s => s * deriv v s) r = -(Δp / (η * L)) * r := by
      have e1 : deriv (fun s => s * deriv v s) r =
          r * ((1 / r) * deriv (fun s => s * deriv v s) r) := by
        rw [← mul_assoc, mul_one_div_cancel hr0, one_mul]
      rw [e1, he]
      ring
    rw [← hdr]
    exact hd.hasDerivAt
  have hH : ∀ r ∈ Set.Ioo (0:ℝ) R,
      HasDerivAt (fun s => s * deriv v s + Δp / (η * L) / 2 * s ^ 2) 0 r := by
    intro r hr
    have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have h2 := (hG r hr).add (hp.const_mul (Δp / (η * L) / 2))
    exact h2.congr_deriv (by ring)
  obtain ⟨C₁, hC₁⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hH r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hH r hr).deriv)
  have hF : ∀ r ∈ Set.Ioo (0:ℝ) R,
      HasDerivAt (fun s => v s - (-(Δp / (η * L)) * s ^ 2 / 4 + C₁ * Real.log s)) 0 r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    obtain ⟨hvd, _, _⟩ := hv r hr
    have h1 : r * deriv v r + Δp / (η * L) / 2 * r ^ 2 = C₁ := hC₁ r hr
    have e : r * deriv v r = C₁ - Δp / (η * L) / 2 * r ^ 2 := by linarith
    have hdv : deriv v r = C₁ / r - Δp / (η * L) * r / 2 := by
      calc deriv v r = (r * deriv v r) / r := (mul_div_cancel_left₀ _ hr0).symm
        _ = (C₁ - Δp / (η * L) / 2 * r ^ 2) / r := by rw [e]
        _ = C₁ / r - Δp / (η * L) * r / 2 := by field_simp <;> ring
    have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have hq : HasDerivAt (fun s => -(Δp / (η * L)) * s ^ 2 / 4 + C₁ * Real.log s)
        (-(Δp / (η * L)) * (2 * r) / 4 + C₁ * r⁻¹) r :=
      ((hp.const_mul (-(Δp / (η * L)))).div_const 4).add
        ((Real.hasDerivAt_log hr0).const_mul C₁)
    have h3 := hvd.hasDerivAt.sub hq
    refine h3.congr_deriv ?_
    rw [hdv]
    ring
  obtain ⟨C₂, hC₂⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hF r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hF r hr).deriv)
  refine ⟨C₁, C₂, fun r hr => ?_⟩
  have h4 : v r - (-(Δp / (η * L)) * r ^ 2 / 4 + C₁ * Real.log r) = C₂ := hC₂ r hr
  linarith

open MathematicsOfWater Real Filter Topology in
theorem solution (η L Δp d : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d)
    (hv : IsPipeFlow η L Δp d v) :
    ∀ r ∈ Set.Ioc 0 (d / 2), v r = poiseuilleProfile η L Δp d r := by
  obtain ⟨hode, ⟨B, hB⟩, hcont, hwall⟩ := hv
  have hd2 : 0 < d / 2 := by linarith
  obtain ⟨C₁, C₂, hsol⟩ := radial_gen_sol_aux η L Δp (d / 2) v hη hL hd2 hode
  have hd4mem : d / 4 ∈ Set.Ioo 0 (d / 2) := ⟨by linarith, by linarith⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB _ hd4mem)
  -- the logarithmic coefficient vanishes, since `v` is bounded near the axis
  have hC1 : C₁ = 0 := by
    by_contra hne
    have hpos : 0 < |C₁| := abs_pos.mpr hne
    have hK0 : 0 ≤ B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂| := by positivity
    have hT0 : 0 ≤ (B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂|) / |C₁| := by positivity
    have hkey : |C₁| * ((B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂|) / |C₁| + 1 +
        |Real.log (d / 4)|) > B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂| := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hpos.ne']
      have := abs_nonneg (Real.log (d / 4))
      nlinarith
    have hTlog : -((B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂|) / |C₁| + 1 +
        |Real.log (d / 4)|) ≤ Real.log (d / 4) := by
      have := neg_abs_le (Real.log (d / 4))
      linarith
    have hrlt : Real.exp (-((B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂|) / |C₁| + 1 +
        |Real.log (d / 4)|)) < d / 2 := by
      calc _ ≤ Real.exp (Real.log (d / 4)) := Real.exp_le_exp.mpr hTlog
        _ = d / 4 := Real.exp_log (by linarith)
        _ < d / 2 := by linarith
    have hmem : Real.exp (-((B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂|) / |C₁| + 1 +
        |Real.log (d / 4)|)) ∈ Set.Ioo 0 (d / 2) := ⟨Real.exp_pos _, hrlt⟩
    have hs := hsol _ hmem
    have hb := hB _ hmem
    rw [Real.log_exp] at hs
    set T := (B + |Δp / (η * L)| * (d / 2) ^ 2 / 4 + |C₂|) / |C₁| + 1 + |Real.log (d / 4)|
      with hT
    set r := Real.exp (-T) with hr
    have hr2 : r ^ 2 ≤ (d / 2) ^ 2 := pow_le_pow_left₀ hmem.1.le hmem.2.le 2
    have hkr : |Δp / (η * L) * r ^ 2| ≤ |Δp / (η * L)| * (d / 2) ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
      exact mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    obtain ⟨hk1, hk2⟩ := abs_le.mp hkr
    have hc1 := neg_abs_le C₂
    have hc2 := le_abs_self C₂
    rcases lt_or_gt_of_ne hne with hneg | hposC
    · rw [abs_of_neg hneg] at hkey
      nlinarith
    · rw [abs_of_pos hposC] at hkey
      nlinarith
  -- on the open interval the profile is the parabola `φ`
  have hIoo : ∀ r ∈ Set.Ioo 0 (d / 2), v r = -(Δp / (η * L)) * r ^ 2 / 4 + C₂ := by
    intro r hr
    rw [hsol r hr, hC1, zero_mul, add_zero]
  -- the wall value fixes `C₂`
  have hφc : Continuous (fun r : ℝ => -(Δp / (η * L)) * r ^ 2 / 4 + C₂) := by fun_prop
  have hev : v =ᶠ[𝓝[<] (d / 2)] (fun r : ℝ => -(Δp / (η * L)) * r ^ 2 / 4 + C₂) := by
    filter_upwards [Ioo_mem_nhdsLT hd2] with r hr using hIoo r hr
  have hlim1 : Tendsto (fun r : ℝ => -(Δp / (η * L)) * r ^ 2 / 4 + C₂) (𝓝[<] (d / 2))
      (𝓝 (v (d / 2))) := (hcont.tendsto).congr' hev
  have hlim2 : Tendsto (fun r : ℝ => -(Δp / (η * L)) * r ^ 2 / 4 + C₂) (𝓝[<] (d / 2))
      (𝓝 (-(Δp / (η * L)) * (d / 2) ^ 2 / 4 + C₂)) :=
    (hφc.tendsto (d / 2)).mono_left nhdsWithin_le_nhds
  have hC2 : -(Δp / (η * L)) * (d / 2) ^ 2 / 4 + C₂ = 0 := by
    rw [← hwall]
    exact tendsto_nhds_unique hlim2 hlim1
  intro r hr
  have hvr : v r = -(Δp / (η * L)) * r ^ 2 / 4 + C₂ := by
    rcases lt_or_eq_of_le hr.2 with hlt | heq
    · exact hIoo r ⟨hr.1, hlt⟩
    · rw [heq, hwall, hC2]
  rw [hvr]
  unfold poiseuilleProfile
  linear_combination hC2
