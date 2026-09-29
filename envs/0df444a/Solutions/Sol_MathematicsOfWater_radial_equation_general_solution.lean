-- Prove2me | solution 1 for MathematicsOfWater.radial_equation_general_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T16:33:13.047182+00:00
-- url     : https://prove2.me/submissions/1beb3a30-fdb7-4944-bf70-f7fe9b84df57

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow

set_option autoImplicit false

open MathematicsOfWater Real in
theorem solution (η L Δp R : ℝ) (v : ℝ → ℝ)
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
