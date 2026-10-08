-- Prove2me | solution 1 for HryniewiczCriterion.ellipsoid_trajectory_rotation
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:19:40.581142+00:00
-- url     : https://prove2.me/submissions/79b8682a-ebae-4e4b-a3e0-8e9758b18c6c

import Definitions.Def_HryniewiczCriterion_Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open scoped ContDiff

namespace HryniewiczCriterion

noncomputable section

/-- The ellipsoid Hamiltonian `|z₁|²/r₁² + |z₂|²/r₂²`. -/
def ellipsoidH (r₁ r₂ : ℝ) : R4 → ℝ :=
  fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2

theorem ellipsoidH_hamiltonianVectorField (r₁ r₂ : ℝ) (x : R4) :
    hamiltonianVectorField (ellipsoidH r₁ r₂) x =
      ![-(2 * x 1 / r₁ ^ 2), 2 * x 0 / r₁ ^ 2, -(2 * x 3 / r₂ ^ 2), 2 * x 2 / r₂ ^ 2] := by
  have hd : HasFDerivAt (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) * (r₁ ^ 2)⁻¹ +
      (x 2 ^ 2 + x 3 ^ 2) * (r₂ ^ 2)⁻¹) _ x :=
    have hp : ∀ i : Fin 4, HasFDerivAt (fun y : R4 => y i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x :=
      fun i => hasFDerivAt_apply i x
    ((((hp 0).pow 2).add ((hp 1).pow 2)).mul_const _).add
      ((((hp 2).pow 2).add ((hp 3).pow 2)).mul_const _)
  have he : ellipsoidH r₁ r₂ = fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) * (r₁ ^ 2)⁻¹ +
      (x 2 ^ 2 + x 3 ^ 2) * (r₂ ^ 2)⁻¹ := by
    funext y; simp [ellipsoidH, div_eq_mul_inv]
  rw [he]
  ext i
  fin_cases i <;>
    simp [hamiltonianVectorField, partialDeriv, hd.fderiv, Pi.single_apply] <;> ring

/-- Solutions of the planar rotation ODE `a' = -w b`, `b' = w a` are rotations. -/
theorem planar_rotation_ode_eq (a b : ℝ → ℝ) (w : ℝ)
    (ha : ∀ t, HasDerivAt a (-(w * b t)) t) (hb : ∀ t, HasDerivAt b (w * a t) t) (t : ℝ) :
    a t = Real.cos (w * t) * a 0 - Real.sin (w * t) * b 0 ∧
      b t = Real.sin (w * t) * a 0 + Real.cos (w * t) * b 0 := by
  have hc : ∀ s, HasDerivAt (fun s => Real.cos (w * s)) (-Real.sin (w * s) * w) s := by
    intro s
    have := ((hasDerivAt_id s).const_mul w).cos
    simpa [mul_comm] using this
  have hs : ∀ s, HasDerivAt (fun s => Real.sin (w * s)) (Real.cos (w * s) * w) s := by
    intro s
    have := ((hasDerivAt_id s).const_mul w).sin
    simpa [mul_comm] using this
  set F : ℝ → ℝ := fun s => Real.cos (w * s) * a s + Real.sin (w * s) * b s
  set G : ℝ → ℝ := fun s => -(Real.sin (w * s) * a s) + Real.cos (w * s) * b s
  have hF : ∀ s, HasDerivAt F 0 s := by
    intro s
    have := ((hc s).mul (ha s)).add ((hs s).mul (hb s))
    exact this.congr_deriv (by ring)
  have hG : ∀ s, HasDerivAt G 0 s := by
    intro s
    have := (((hs s).mul (ha s)).neg).add ((hc s).mul (hb s))
    exact this.congr_deriv (by ring)
  have hF0 : F t = F 0 := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  have hG0 : G t = G 0 := is_const_of_deriv_eq_zero (fun s => (hG s).differentiableAt)
    (fun s => (hG s).deriv) t 0
  simp only [F, G, mul_zero, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero,
    neg_zero, zero_add] at hF0 hG0
  have hcs := Real.sin_sq_add_cos_sq (w * t)
  constructor
  · linear_combination Real.cos (w * t) * hF0 - Real.sin (w * t) * hG0 - a t * hcs
  · linear_combination Real.sin (w * t) * hF0 + Real.cos (w * t) * hG0 - b t * hcs

/-- Explicit flow of the ellipsoid: both planes rotate. -/
theorem ellipsoid_trajectory_eq {r₁ r₂ : ℝ} {y : ℝ → R4}
    (hy : IsTrajectory (ellipsoidH r₁ r₂) y) (t : ℝ) :
    (y t 0 = Real.cos (2 / r₁ ^ 2 * t) * y 0 0 - Real.sin (2 / r₁ ^ 2 * t) * y 0 1 ∧
      y t 1 = Real.sin (2 / r₁ ^ 2 * t) * y 0 0 + Real.cos (2 / r₁ ^ 2 * t) * y 0 1) ∧
    (y t 2 = Real.cos (2 / r₂ ^ 2 * t) * y 0 2 - Real.sin (2 / r₂ ^ 2 * t) * y 0 3 ∧
      y t 3 = Real.sin (2 / r₂ ^ 2 * t) * y 0 2 + Real.cos (2 / r₂ ^ 2 * t) * y 0 3) := by
  have hc : ∀ (i : Fin 4) s, HasDerivAt (fun s => y s i)
      (hamiltonianVectorField (ellipsoidH r₁ r₂) (y s) i) s :=
    fun i s => hasDerivAt_pi.1 (hy.1 s) i
  simp only [ellipsoidH_hamiltonianVectorField] at hc
  constructor
  · refine planar_rotation_ode_eq (fun s => y s 0) (fun s => y s 1) _ (fun s => ?_)
      (fun s => ?_) t
    · convert hc 0 s using 1; simp; ring
    · convert hc 1 s using 1; simp; ring
  · refine planar_rotation_ode_eq (fun s => y s 2) (fun s => y s 3) _ (fun s => ?_)
      (fun s => ?_) t
    · convert hc 2 s using 1; simp; ring
    · convert hc 3 s using 1; simp; ring

/-- Every unit vector is `(cos 2πt, sin 2πt)`. -/
theorem exists_cos_sin_eq (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ t : ℝ, Real.cos (2 * Real.pi * t) = a ∧ Real.sin (2 * Real.pi * t) = b := by
  set z : ℂ := ⟨a, b⟩
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [z, ← sq, h]
  have hz : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact zero_ne_one hn
  refine ⟨Complex.arg z / (2 * Real.pi), ?_, ?_⟩
  · rw [mul_div_cancel₀ _ (by positivity), Complex.cos_arg hz, hn, div_one]
  · rw [mul_div_cancel₀ _ (by positivity), Complex.sin_arg, hn, div_one]

/-- Angles in `[0, 1)` with the same cosine and sine are equal. -/
theorem eq_of_cos_sin_eq {θ θ' : ℝ} (hθ : θ ∈ Set.Ico (0 : ℝ) 1) (hθ' : θ' ∈ Set.Ico (0 : ℝ) 1)
    (hc : Real.cos (2 * Real.pi * θ) = Real.cos (2 * Real.pi * θ'))
    (hs : Real.sin (2 * Real.pi * θ) = Real.sin (2 * Real.pi * θ')) : θ = θ' := by
  have h1 : Real.cos (2 * Real.pi * (θ - θ')) = 1 := by
    rw [mul_sub, Real.cos_sub, hc, hs]
    linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * θ')
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
  have hn' : (n : ℝ) = θ - θ' := by
    have := Real.pi_pos
    field_simp at hn
    linarith
  have hlt : -1 < (n : ℝ) ∧ (n : ℝ) < 1 := by
    obtain ⟨_, _⟩ := hθ; obtain ⟨_, _⟩ := hθ'; constructor <;> linarith
  have : n = 0 := by
    obtain ⟨h1, h2⟩ := hlt
    have : (-1 : ℤ) < n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega
  subst this
  simp at hn'
  linarith

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution {r₁ r₂ : ℝ} {y : ℝ → R4}
    (hy : IsTrajectory (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2) y) (t : ℝ) :
    (y t 0 = Real.cos (2 / r₁ ^ 2 * t) * y 0 0 - Real.sin (2 / r₁ ^ 2 * t) * y 0 1 ∧
      y t 1 = Real.sin (2 / r₁ ^ 2 * t) * y 0 0 + Real.cos (2 / r₁ ^ 2 * t) * y 0 1) ∧
    (y t 2 = Real.cos (2 / r₂ ^ 2 * t) * y 0 2 - Real.sin (2 / r₂ ^ 2 * t) * y 0 3 ∧
      y t 3 = Real.sin (2 / r₂ ^ 2 * t) * y 0 2 + Real.cos (2 / r₂ ^ 2 * t) * y 0 3) :=
  ellipsoid_trajectory_eq hy t
