-- Prove2me | solution 1 for HryniewiczCriterion.ellipsoid_axes_bind_adapted_open_books
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:12:28.451699+00:00
-- url     : https://prove2.me/submissions/4d94af5b-150a-461c-88ff-0e6202e5d787

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

namespace HryniewiczCriterion

noncomputable section

/-- A prime periodic orbit of the ellipsoid flow lying in the axis `z₂ = 0` has period
`π r₁²`, and starts on the circle of radius `r₁`. -/
theorem ellipsoid_axis_orbit_period {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (P : PeriodicOrbit (ellipsoidH r₁ r₂)) (hP : P.IsPrime)
    (hax : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0}) :
    P.T = Real.pi * r₁ ^ 2 ∧ P.x 0 0 ^ 2 + P.x 0 1 ^ 2 = r₁ ^ 2 := by
  have hax' : ∀ t, P.x t 2 = 0 ∧ P.x t 3 = 0 := fun t => hax ⟨t, rfl⟩
  have hE : P.x 0 0 ^ 2 + P.x 0 1 ^ 2 = r₁ ^ 2 := by
    have h := P.trajectory.2 0
    simp only [ellipsoidH, (hax' 0).1, (hax' 0).2] at h
    have h' : (P.x 0 0 ^ 2 + P.x 0 1 ^ 2) / r₁ ^ 2 = 1 := by simpa using h
    exact (div_eq_one_iff_eq (by positivity)).1 h'
  have hr : (0 : ℝ) < r₁ ^ 2 := by positivity
  refine ⟨?_, hE⟩
  set a := P.x 0 0
  set b := P.x 0 1
  have hflow := fun t => (ellipsoid_trajectory_eq P.trajectory t).1
  -- `x(T) = x(0)` forces `cos(2T/r₁²) = 1`
  have hT := P.periodic 0
  rw [zero_add] at hT
  have hc1 : Real.cos (2 / r₁ ^ 2 * P.T) = 1 := by
    have e0 := (hflow P.T).1
    have e1 := (hflow P.T).2
    rw [hT] at e0 e1
    have : (Real.cos (2 / r₁ ^ 2 * P.T) - 1) * (a ^ 2 + b ^ 2) = 0 := by
      linear_combination (-a) * e0 - b * e1
    rw [hE] at this
    have := (mul_eq_zero.1 this).resolve_right hr.ne'
    linarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc1
  have hTn : P.T = n * (Real.pi * r₁ ^ 2) := by
    rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hr.ne'] at hn
    linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have hpos : (0 : ℝ) < n := by
      have := P.T_pos
      rw [hTn] at this
      exact pos_of_mul_pos_left this (by positivity)
    have : (0 : ℤ) < n := by exact_mod_cast hpos
    exact_mod_cast this
  have hge : Real.pi * r₁ ^ 2 ≤ P.T := by
    have := mul_le_mul_of_nonneg_right hn1 (le_of_lt hr)
    have := mul_le_mul_of_nonneg_right this Real.pi_pos.le
    rw [hTn]; nlinarith [Real.pi_pos]
  rcases hge.lt_or_eq with hlt | heq
  · exfalso
    refine hP (Real.pi * r₁ ^ 2) (by positivity) hlt ?_
    have hk : 2 / r₁ ^ 2 * (Real.pi * r₁ ^ 2) = 2 * Real.pi := by field_simp
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [(hflow _).1, hk, Real.cos_two_pi, Real.sin_two_pi]; ring
    · simp only [Fin.mk_one, Fin.isValue]
      rw [(hflow _).2, hk, Real.cos_two_pi, Real.sin_two_pi]; ring
    · show P.x _ 2 = P.x 0 2
      rw [(hax' _).1, (hax' _).1]
    · show P.x _ 3 = P.x 0 3
      rw [(hax' _).2, (hax' _).2]
  · exact heq.symm

/-- The stereographic page of the axis `z₂ = 0` at angle `θ`: in complex notation
`(r₁ c · 2w/(1+|w|²), r₂ (1-|w|²)/(1+|w|²) e^{2πiθ})`, `c = c₀ + i c₁`. -/
def ellPage (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) : R4 :=
  ![r₁ * (c₀ * (2 * u 0 / (1 + u 0 ^ 2 + u 1 ^ 2)) - c₁ * (2 * u 1 / (1 + u 0 ^ 2 + u 1 ^ 2))),
    r₁ * (c₀ * (2 * u 1 / (1 + u 0 ^ 2 + u 1 ^ 2)) + c₁ * (2 * u 0 / (1 + u 0 ^ 2 + u 1 ^ 2))),
    r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) * Real.cos (2 * Real.pi * θ),
    r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) * Real.sin (2 * Real.pi * θ)]

theorem stereo_denom_pos (u : Plane) : 0 < 1 + u 0 ^ 2 + u 1 ^ 2 := by positivity

theorem ellPage_contDiff (r₁ r₂ c₀ c₁ : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Plane => ellPage r₁ r₂ c₀ c₁ z.1 z.2) := by
  have hN : ContDiff ℝ ∞ (fun z : ℝ × Plane => (1 + z.2 0 ^ 2 + z.2 1 ^ 2)⁻¹) :=
    (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ × Plane => 1 + z.2 0 ^ 2 + z.2 1 ^ 2)).inv
      (fun z => (stereo_denom_pos z.2).ne')
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [ellPage, div_eq_mul_inv] <;> simp <;> fun_prop

theorem ellPage_energy {r₁ r₂ c₀ c₁ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) (u : Plane) :
    ellipsoidH r₁ r₂ (ellPage r₁ r₂ c₀ c₁ θ u) = 1 := by
  have hN := (stereo_denom_pos u).ne'
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
  simp only [ellipsoidH, ellPage]
  simp
  field_simp
  linear_combination (4 * (u 0 ^ 2 + u 1 ^ 2) * hc +
    (1 - u 0 ^ 2 - u 1 ^ 2) ^ 2 * hcs) * 0 + 0 * hc + 0 * hcs +
    (4 * (u 0 ^ 2 + u 1 ^ 2)) * hc + (1 - u 0 ^ 2 - u 1 ^ 2) ^ 2 * hcs

/-- The `z₂`-component of a page is the real multiple `r₂ g` of `e^{2πiθ}`. -/
theorem ellPage_radial (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) :
    ellPage r₁ r₂ c₀ c₁ θ u 2 * Real.cos (2 * Real.pi * θ) +
      ellPage r₁ r₂ c₀ c₁ θ u 3 * Real.sin (2 * Real.pi * θ) =
        r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) := by
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
  simp [ellPage]
  linear_combination r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) * hcs

theorem ellPage_perp (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) :
    ellPage r₁ r₂ c₀ c₁ θ u 2 * Real.sin (2 * Real.pi * θ) -
      ellPage r₁ r₂ c₀ c₁ θ u 3 * Real.cos (2 * Real.pi * θ) = 0 := by
  simp [ellPage]; ring

/-- The `z₁`-component, rotated back by `c̄`, is `r₁ · 2u/(1+|u|²)`. -/
theorem ellPage_z1 {r₁ r₂ c₀ c₁ : ℝ} (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) (u : Plane) :
    (c₀ * ellPage r₁ r₂ c₀ c₁ θ u 0 + c₁ * ellPage r₁ r₂ c₀ c₁ θ u 1 =
        r₁ * (2 * u 0 / (1 + u 0 ^ 2 + u 1 ^ 2))) ∧
      (c₀ * ellPage r₁ r₂ c₀ c₁ θ u 1 - c₁ * ellPage r₁ r₂ c₀ c₁ θ u 0 =
        r₁ * (2 * u 1 / (1 + u 0 ^ 2 + u 1 ^ 2))) := by
  simp [ellPage]
  constructor
  · linear_combination r₁ * (2 * u 0 / (1 + u 0 ^ 2 + u 1 ^ 2)) * hc
  · linear_combination r₁ * (2 * u 1 / (1 + u 0 ^ 2 + u 1 ^ 2)) * hc

/-- Left inverse of a page (inverse stereographic projection), smooth near the page. -/
def ellPageInv (r₁ r₂ c₀ c₁ θ : ℝ) (y : R4) : Plane :=
  ![((c₀ * y 0 + c₁ * y 1) / r₁) /
      (1 + (y 2 * Real.cos (2 * Real.pi * θ) + y 3 * Real.sin (2 * Real.pi * θ)) / r₂),
    ((c₀ * y 1 - c₁ * y 0) / r₁) /
      (1 + (y 2 * Real.cos (2 * Real.pi * θ) + y 3 * Real.sin (2 * Real.pi * θ)) / r₂)]

theorem ellPage_inv_denom {r₁ r₂ c₀ c₁ : ℝ} (h₂ : r₂ ≠ 0) (θ : ℝ) (u : Plane) :
    1 + (ellPage r₁ r₂ c₀ c₁ θ u 2 * Real.cos (2 * Real.pi * θ) +
      ellPage r₁ r₂ c₀ c₁ θ u 3 * Real.sin (2 * Real.pi * θ)) / r₂ =
        2 / (1 + u 0 ^ 2 + u 1 ^ 2) := by
  rw [ellPage_radial]
  have hN := (stereo_denom_pos u).ne'
  field_simp
  ring

theorem ellPageInv_ellPage {r₁ r₂ c₀ c₁ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) (u : Plane) :
    ellPageInv r₁ r₂ c₀ c₁ θ (ellPage r₁ r₂ c₀ c₁ θ u) = u := by
  have hN := (stereo_denom_pos u).ne'
  have hz := ellPage_z1 (r₁ := r₁) (r₂ := r₂) hc θ u
  ext i
  fin_cases i
  · show ((c₀ * _ + c₁ * _) / r₁) / (1 + (_ * _ + _ * _) / r₂) = u 0
    rw [ellPage_inv_denom h₂, hz.1]
    field_simp
  · show ((c₀ * _ - c₁ * _) / r₁) / (1 + (_ * _ + _ * _) / r₂) = u 1
    rw [ellPage_inv_denom h₂, hz.2]
    field_simp

theorem ellPage_injective {r₁ r₂ c₀ c₁ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) : Function.Injective (ellPage r₁ r₂ c₀ c₁ θ) := by
  intro u v h
  rw [← ellPageInv_ellPage h₁ h₂ hc θ u, h, ellPageInv_ellPage h₁ h₂ hc θ v]

theorem ellPage_circlePoint (r₁ r₂ c₀ c₁ θ t : ℝ) :
    ellPage r₁ r₂ c₀ c₁ θ (circlePoint t) =
      ![r₁ * (c₀ * Real.cos (2 * Real.pi * t) - c₁ * Real.sin (2 * Real.pi * t)),
        r₁ * (c₀ * Real.sin (2 * Real.pi * t) + c₁ * Real.cos (2 * Real.pi * t)), 0, 0] := by
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  have h2 : 1 + Real.cos (2 * Real.pi * t) ^ 2 + Real.sin (2 * Real.pi * t) ^ 2 = 2 := by
    linarith
  have h0 : 1 - Real.cos (2 * Real.pi * t) ^ 2 - Real.sin (2 * Real.pi * t) ^ 2 = 0 := by
    linarith
  ext i
  fin_cases i <;> simp [ellPage, circlePoint, h2, h0] <;> ring

/-- Every point of the energy surface whose `z₂` is a nonnegative multiple of
`e^{2πiθ}` lies on the page `θ`; in the open disk when the multiple is positive. -/
theorem ellPage_surj {r₁ r₂ c₀ c₁ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ s : ℝ) (hs : 0 ≤ s) (y : R4)
    (hy : ellipsoidH r₁ r₂ y = 1) (hy2 : y 2 = r₂ * s * Real.cos (2 * Real.pi * θ))
    (hy3 : y 3 = r₂ * s * Real.sin (2 * Real.pi * θ)) :
    ∃ u : Plane, u ∈ closedUnitDisk ∧ (0 < s → u ∈ openUnitDisk) ∧
      ellPage r₁ r₂ c₀ c₁ θ u = y := by
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
  set w₀ := (c₀ * y 0 + c₁ * y 1) / r₁
  set w₁ := (c₀ * y 1 - c₁ * y 0) / r₁
  have e1 : w₀ ^ 2 + w₁ ^ 2 = (y 0 ^ 2 + y 1 ^ 2) / r₁ ^ 2 := by
    simp only [w₀, w₁]
    rw [div_pow, div_pow, ← add_div]
    congr 1
    linear_combination (y 0 ^ 2 + y 1 ^ 2) * hc
  have e2 : ((r₂ * s * Real.cos (2 * Real.pi * θ)) ^ 2 +
      (r₂ * s * Real.sin (2 * Real.pi * θ)) ^ 2) / r₂ ^ 2 = s ^ 2 := by
    rw [div_eq_iff (by positivity)]
    linear_combination r₂ ^ 2 * s ^ 2 * hcs
  have hw : w₀ ^ 2 + w₁ ^ 2 = 1 - s ^ 2 := by
    simp only [ellipsoidH, hy2, hy3] at hy
    rw [e2] at hy
    rw [e1]; linarith
  have hs1 : 0 < 1 + s := by linarith
  set u : Plane := ![w₀ / (1 + s), w₁ / (1 + s)]
  have hu : u 0 ^ 2 + u 1 ^ 2 = (1 - s) / (1 + s) := by
    have hu' : (w₀ / (1 + s)) ^ 2 + (w₁ / (1 + s)) ^ 2 = (1 - s) / (1 + s) := by
      have e3 : (w₀ / (1 + s)) ^ 2 + (w₁ / (1 + s)) ^ 2 = (w₀ ^ 2 + w₁ ^ 2) / (1 + s) ^ 2 := by
        rw [div_pow w₀, div_pow w₁, add_div]
      rw [e3, hw]
      field_simp
      ring
    exact hu'
  have hN : 1 + u 0 ^ 2 + u 1 ^ 2 = 2 / (1 + s) := by
    rw [add_assoc, hu]; field_simp; ring
  refine ⟨u, ?_, ?_, ?_⟩
  · show u 0 ^ 2 + u 1 ^ 2 ≤ 1
    rw [hu, div_le_one hs1]; linarith
  · intro hs0
    show u 0 ^ 2 + u 1 ^ 2 < 1
    rw [hu, div_lt_one hs1]; linarith
  · have hg : (1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2) = s := by
      rw [hN, sub_sub, hu]; field_simp; ring
    have hA0 : 2 * u 0 / (1 + u 0 ^ 2 + u 1 ^ 2) = w₀ := by
      rw [hN]; simp [u]; field_simp
    have hA1 : 2 * u 1 / (1 + u 0 ^ 2 + u 1 ^ 2) = w₁ := by
      rw [hN]; simp [u]; field_simp
    have hr := h₁.ne'
    ext i
    fin_cases i
    · show r₁ * (c₀ * (2 * u 0 / _) - c₁ * (2 * u 1 / _)) = y 0
      rw [hA0, hA1]; simp only [w₀, w₁]; field_simp
      linear_combination y 0 * hc
    · show r₁ * (c₀ * (2 * u 1 / _) + c₁ * (2 * u 0 / _)) = y 1
      rw [hA0, hA1]; simp only [w₀, w₁]; field_simp
      linear_combination y 1 * hc
    · show r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / _) * _ = y 2
      rw [hg, hy2]
    · show r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / _) * _ = y 3
      rw [hg, hy3]

end

end HryniewiczCriterion

namespace HryniewiczCriterion

noncomputable section

/-- A linear functional that vanishes along `f` vanishes on the differential of `f`. -/
theorem clm_fderiv_eq_zero_of_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → R4} {u : E} (hf : DifferentiableAt ℝ f u) (α : R4 →L[ℝ] ℝ)
    (h : ∀ x, α (f x) = 0) (v : E) : α (fderiv ℝ f u v) = 0 := by
  have h1 : fderiv ℝ (fun x => α (f x)) u = α.comp (fderiv ℝ f u) :=
    (α.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  have h2 : (fun x => α (f x)) = fun _ => (0 : ℝ) := funext h
  rw [h2] at h1
  have h3 := DFunLike.congr_fun h1 v
  simpa using h3.symm

/-- The functional `w ↦ w₂ sin 2πθ - w₃ cos 2πθ` (pairing with `i e^{2πiθ}` in the
`z₂`-plane). -/
def ellPerp (θ : ℝ) : R4 →L[ℝ] ℝ :=
  Real.sin (2 * Real.pi * θ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2 -
    Real.cos (2 * Real.pi * θ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 3

theorem ellPerp_apply (θ : ℝ) (w : R4) :
    ellPerp θ w = w 2 * Real.sin (2 * Real.pi * θ) - w 3 * Real.cos (2 * Real.pi * θ) := by
  simp [ellPerp, mul_comm]

theorem ellPage_contDiff_page (r₁ r₂ c₀ c₁ θ : ℝ) :
    ContDiff ℝ ∞ (ellPage r₁ r₂ c₀ c₁ θ) :=
  (ellPage_contDiff r₁ r₂ c₀ c₁).comp (contDiff_const.prodMk contDiff_id)

theorem ellPage_differentiableAt (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) :
    DifferentiableAt ℝ (ellPage r₁ r₂ c₀ c₁ θ) u :=
  ((ellPage_contDiff_page r₁ r₂ c₀ c₁ θ).differentiable (by simp)).differentiableAt

theorem ellPerp_fderiv (r₁ r₂ c₀ c₁ θ : ℝ) (u v : Plane) :
    ellPerp θ (fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u v) = 0 :=
  clm_fderiv_eq_zero_of_comp (ellPage_differentiableAt r₁ r₂ c₀ c₁ θ u) _
    (fun x => by rw [ellPerp_apply]; exact ellPage_perp r₁ r₂ c₀ c₁ θ x) v

theorem stereo_g_pos {u : Plane} (hu : u ∈ openUnitDisk) :
    0 < (1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2) := by
  have : u 0 ^ 2 + u 1 ^ 2 < 1 := hu
  exact div_pos (by linarith) (stereo_denom_pos u)

/-- Pages are immersed (on the whole plane): differentiate the left inverse. -/
theorem ellPage_fderiv_injective {r₁ r₂ c₀ c₁ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) (u : Plane) :
    Function.Injective (fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u) := by
  set e := ellPage r₁ r₂ c₀ c₁ θ
  have hden : 1 + (e u 2 * Real.cos (2 * Real.pi * θ) + e u 3 * Real.sin (2 * Real.pi * θ)) / r₂
      ≠ 0 := by
    rw [ellPage_inv_denom h₂]
    exact (div_pos two_pos (stereo_denom_pos u)).ne'
  have hinv : DifferentiableAt ℝ (ellPageInv r₁ r₂ c₀ c₁ θ) (e u) := by
    refine differentiableAt_pi.2 fun i => ?_
    fin_cases i
    · have hn : DifferentiableAt ℝ (fun y : R4 => (c₀ * y 0 + c₁ * y 1) / r₁) (e u) := by fun_prop
      have hd : DifferentiableAt ℝ (fun y : R4 =>
          1 + (y 2 * Real.cos (2 * Real.pi * θ) + y 3 * Real.sin (2 * Real.pi * θ)) / r₂) (e u) := by
        fun_prop
      refine (hn.mul (hd.inv hden)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => ?_)
      simp [ellPageInv, div_eq_mul_inv]
    · have hn : DifferentiableAt ℝ (fun y : R4 => (c₀ * y 1 - c₁ * y 0) / r₁) (e u) := by fun_prop
      have hd : DifferentiableAt ℝ (fun y : R4 =>
          1 + (y 2 * Real.cos (2 * Real.pi * θ) + y 3 * Real.sin (2 * Real.pi * θ)) / r₂) (e u) := by
        fun_prop
      refine (hn.mul (hd.inv hden)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => ?_)
      simp [ellPageInv, div_eq_mul_inv]
  have hcomp : (ellPageInv r₁ r₂ c₀ c₁ θ) ∘ e = id :=
    funext fun v => ellPageInv_ellPage h₁ h₂ hc θ v
  have hd := fderiv_comp u hinv (ellPage_differentiableAt r₁ r₂ c₀ c₁ θ u)
  rw [hcomp, fderiv_id] at hd
  intro v w hvw
  have := DFunLike.congr_fun hd v
  have h' := DFunLike.congr_fun hd w
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at this h'
  rw [this, h', hvw]

/-- `X_H` is transverse to the interior of every page. -/
theorem ellPage_transverse {r₁ r₂ c₀ c₁ : ℝ} (h₂ : r₂ ≠ 0) (θ : ℝ) (u : Plane)
    (hu : u ∈ openUnitDisk) :
    hamiltonianVectorField (ellipsoidH r₁ r₂) (ellPage r₁ r₂ c₀ c₁ θ u) ∉
      Set.range (fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u) := by
  rintro ⟨v, hv⟩
  have h0 := ellPerp_fderiv r₁ r₂ c₀ c₁ θ u v
  rw [hv, ellPerp_apply, ellipsoidH_hamiltonianVectorField] at h0
  have hr := ellPage_radial r₁ r₂ c₀ c₁ θ u
  have hg := stereo_g_pos hu
  simp at h0
  have : (2 / r₂ ^ 2) * (r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2))) = 0 := by
    rw [← hr]
    field_simp
    field_simp at h0
    linear_combination -h0
  have hne : (2 / r₂ ^ 2) * (r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2))) ≠ 0 :=
    mul_ne_zero (by positivity) (mul_ne_zero h₂ hg.ne')
  exact hne this

end

end HryniewiczCriterion

namespace HryniewiczCriterion

noncomputable section

theorem stereo_hasDerivAt_xA (a b : ℝ) :
    HasDerivAt (fun s => 2 * (a + s) / (1 + (a + s) ^ 2 + b ^ 2))
      ((2 * (1 + a ^ 2 + b ^ 2) - 4 * a ^ 2) / (1 + a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => a + s) 1 0 := (hasDerivAt_id 0).const_add a
  have hN : (1 + (a + 0) ^ 2 + b ^ 2) ≠ 0 := by positivity
  refine ((hs.const_mul 2).div (((hs.pow 2).const_add 1).add_const (b ^ 2)) hN).congr_deriv ?_
  have hN' : (1 + a ^ 2 + b ^ 2) ≠ 0 := by positivity
  simp only [Pi.pow_apply, add_zero]
  field_simp
  ring

theorem stereo_hasDerivAt_xB (a b : ℝ) :
    HasDerivAt (fun s => 2 * b / (1 + (a + s) ^ 2 + b ^ 2))
      (-(4 * a * b) / (1 + a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => a + s) 1 0 := (hasDerivAt_id 0).const_add a
  have hN : (1 + (a + 0) ^ 2 + b ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_const (0 : ℝ) (2 * b)).div
    (((hs.pow 2).const_add 1).add_const (b ^ 2)) hN).congr_deriv ?_
  have hN' : (1 + a ^ 2 + b ^ 2) ≠ 0 := by positivity
  simp only [Pi.pow_apply, add_zero]
  field_simp
  ring

theorem stereo_hasDerivAt_xG (a b : ℝ) :
    HasDerivAt (fun s => (1 - (a + s) ^ 2 - b ^ 2) / (1 + (a + s) ^ 2 + b ^ 2))
      (-(4 * a) / (1 + a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => a + s) 1 0 := (hasDerivAt_id 0).const_add a
  have hN : (1 + (a + 0) ^ 2 + b ^ 2) ≠ 0 := by positivity
  refine ((((hs.pow 2).const_sub 1).sub_const (b ^ 2)).div
    (((hs.pow 2).const_add 1).add_const (b ^ 2)) hN).congr_deriv ?_
  have hN' : (1 + a ^ 2 + b ^ 2) ≠ 0 := by positivity
  simp only [Pi.pow_apply, add_zero]
  field_simp
  ring

theorem stereo_hasDerivAt_yA (a b : ℝ) :
    HasDerivAt (fun s => 2 * a / (1 + a ^ 2 + (b + s) ^ 2))
      (-(4 * a * b) / (1 + a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => b + s) 1 0 := (hasDerivAt_id 0).const_add b
  have hN : (1 + a ^ 2 + (b + 0) ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_const (0 : ℝ) (2 * a)).div
    ((hs.pow 2).const_add (1 + a ^ 2)) hN).congr_deriv ?_
  have hN' : (1 + a ^ 2 + b ^ 2) ≠ 0 := by positivity
  simp only [Pi.pow_apply, add_zero]
  field_simp
  ring

theorem stereo_hasDerivAt_yB (a b : ℝ) :
    HasDerivAt (fun s => 2 * (b + s) / (1 + a ^ 2 + (b + s) ^ 2))
      ((2 * (1 + a ^ 2 + b ^ 2) - 4 * b ^ 2) / (1 + a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => b + s) 1 0 := (hasDerivAt_id 0).const_add b
  have hN : (1 + a ^ 2 + (b + 0) ^ 2) ≠ 0 := by positivity
  refine ((hs.const_mul 2).div ((hs.pow 2).const_add (1 + a ^ 2)) hN).congr_deriv ?_
  have hN' : (1 + a ^ 2 + b ^ 2) ≠ 0 := by positivity
  simp only [Pi.pow_apply, add_zero]
  field_simp
  ring

theorem stereo_hasDerivAt_yG (a b : ℝ) :
    HasDerivAt (fun s => (1 - a ^ 2 - (b + s) ^ 2) / (1 + a ^ 2 + (b + s) ^ 2))
      (-(4 * b) / (1 + a ^ 2 + b ^ 2) ^ 2) 0 := by
  have hs : HasDerivAt (fun s : ℝ => b + s) 1 0 := (hasDerivAt_id 0).const_add b
  have hN : (1 + a ^ 2 + (b + 0) ^ 2) ≠ 0 := by positivity
  refine (((hs.pow 2).const_sub (1 - a ^ 2)).div
    ((hs.pow 2).const_add (1 + a ^ 2)) hN).congr_deriv ?_
  have hN' : (1 + a ^ 2 + b ^ 2) ≠ 0 := by positivity
  simp only [Pi.pow_apply, add_zero]
  field_simp
  ring

/-- A directional derivative read off from a line. -/
theorem fderiv_single_eq_of_hasDerivAt {f : Plane → R4} {u : Plane}
    (hf : DifferentiableAt ℝ f u) (i : Fin 2) {V : R4}
    (h : HasDerivAt (fun s : ℝ => f (u + s • (Pi.single i 1 : Plane))) V 0) :
    fderiv ℝ f u (Pi.single i 1) = V := by
  have hl : HasDerivAt (fun s : ℝ => u + s • (Pi.single i 1 : Plane)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Plane)).const_add u
  have hf' : HasFDerivAt f (fderiv ℝ f u) ((fun s : ℝ => u + s • (Pi.single i 1 : Plane)) 0) := by
    simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt 0 hl).unique h

theorem ellPage_fderiv_dir0 (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) :
    fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u (Pi.single 0 1) =
      ![r₁ * (c₀ * ((2 * (1 + u 0 ^ 2 + u 1 ^ 2) - 4 * u 0 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) -
          c₁ * (-(4 * u 0 * u 1) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2)),
        r₁ * (c₀ * (-(4 * u 0 * u 1) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) +
          c₁ * ((2 * (1 + u 0 ^ 2 + u 1 ^ 2) - 4 * u 0 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2)),
        r₂ * (-(4 * u 0) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) * Real.cos (2 * Real.pi * θ),
        r₂ * (-(4 * u 0) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) * Real.sin (2 * Real.pi * θ)] := by
  refine fderiv_single_eq_of_hasDerivAt (ellPage_differentiableAt r₁ r₂ c₀ c₁ θ u) 0 ?_
  have hline : (fun s : ℝ => ellPage r₁ r₂ c₀ c₁ θ (u + s • (Pi.single 0 1 : Plane))) =
      fun s => ellPage r₁ r₂ c₀ c₁ θ ![u 0 + s, u 1] := by
    funext s; congr 1; ext j; fin_cases j <;> simp
  rw [hline, hasDerivAt_pi]
  intro i
  fin_cases i
  · exact (((stereo_hasDerivAt_xA (u 0) (u 1)).const_mul c₀).sub
      ((stereo_hasDerivAt_xB (u 0) (u 1)).const_mul c₁)).const_mul r₁
  · exact (((stereo_hasDerivAt_xB (u 0) (u 1)).const_mul c₀).add
      ((stereo_hasDerivAt_xA (u 0) (u 1)).const_mul c₁)).const_mul r₁
  · exact ((stereo_hasDerivAt_xG (u 0) (u 1)).const_mul r₂).mul_const _
  · exact ((stereo_hasDerivAt_xG (u 0) (u 1)).const_mul r₂).mul_const _

theorem ellPage_fderiv_dir1 (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) :
    fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u (Pi.single 1 1) =
      ![r₁ * (c₀ * (-(4 * u 0 * u 1) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) -
          c₁ * ((2 * (1 + u 0 ^ 2 + u 1 ^ 2) - 4 * u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2)),
        r₁ * (c₀ * ((2 * (1 + u 0 ^ 2 + u 1 ^ 2) - 4 * u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) +
          c₁ * (-(4 * u 0 * u 1) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2)),
        r₂ * (-(4 * u 1) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) * Real.cos (2 * Real.pi * θ),
        r₂ * (-(4 * u 1) / (1 + u 0 ^ 2 + u 1 ^ 2) ^ 2) * Real.sin (2 * Real.pi * θ)] := by
  refine fderiv_single_eq_of_hasDerivAt (ellPage_differentiableAt r₁ r₂ c₀ c₁ θ u) 1 ?_
  have hline : (fun s : ℝ => ellPage r₁ r₂ c₀ c₁ θ (u + s • (Pi.single 1 1 : Plane))) =
      fun s => ellPage r₁ r₂ c₀ c₁ θ ![u 0, u 1 + s] := by
    funext s; congr 1; ext j; fin_cases j <;> simp
  rw [hline, hasDerivAt_pi]
  intro i
  fin_cases i
  · exact (((stereo_hasDerivAt_yA (u 0) (u 1)).const_mul c₀).sub
      ((stereo_hasDerivAt_yB (u 0) (u 1)).const_mul c₁)).const_mul r₁
  · exact (((stereo_hasDerivAt_yB (u 0) (u 1)).const_mul c₀).add
      ((stereo_hasDerivAt_yA (u 0) (u 1)).const_mul c₁)).const_mul r₁
  · exact ((stereo_hasDerivAt_yG (u 0) (u 1)).const_mul r₂).mul_const _
  · exact ((stereo_hasDerivAt_yG (u 0) (u 1)).const_mul r₂).mul_const _

/-- Pages are positively oriented by `ω₀` on the open disk. -/
theorem ellPage_omega0_pos {r₁ r₂ c₀ c₁ : ℝ} (h₁ : r₁ ≠ 0) (hc : c₀ ^ 2 + c₁ ^ 2 = 1)
    (θ : ℝ) (u : Plane) (hu : u ∈ openUnitDisk) :
    0 < omega0 (fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u (Pi.single 0 1))
      (fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u (Pi.single 1 1)) := by
  rw [ellPage_fderiv_dir0, ellPage_fderiv_dir1]
  have hu' : u 0 ^ 2 + u 1 ^ 2 < 1 := hu
  set a := u 0
  set b := u 1
  set N := 1 + a ^ 2 + b ^ 2 with hNdef
  have hN : 0 < N := by positivity
  have key : omega0
      ![r₁ * (c₀ * ((2 * N - 4 * a ^ 2) / N ^ 2) - c₁ * (-(4 * a * b) / N ^ 2)),
        r₁ * (c₀ * (-(4 * a * b) / N ^ 2) + c₁ * ((2 * N - 4 * a ^ 2) / N ^ 2)),
        r₂ * (-(4 * a) / N ^ 2) * Real.cos (2 * Real.pi * θ),
        r₂ * (-(4 * a) / N ^ 2) * Real.sin (2 * Real.pi * θ)]
      ![r₁ * (c₀ * (-(4 * a * b) / N ^ 2) - c₁ * ((2 * N - 4 * b ^ 2) / N ^ 2)),
        r₁ * (c₀ * ((2 * N - 4 * b ^ 2) / N ^ 2) + c₁ * (-(4 * a * b) / N ^ 2)),
        r₂ * (-(4 * b) / N ^ 2) * Real.cos (2 * Real.pi * θ),
        r₂ * (-(4 * b) / N ^ 2) * Real.sin (2 * Real.pi * θ)] =
      r₁ ^ 2 * (c₀ ^ 2 + c₁ ^ 2) * (4 * (1 - a ^ 2 - b ^ 2) / N ^ 3) := by
    simp only [omega0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hNdef]
    field_simp
    ring
  rw [key, hc]
  have : 0 < 1 - a ^ 2 - b ^ 2 := by linarith
  positivity

/-- `θ`-derivative of the page family. -/
theorem ellPage_hasDerivAt_angle (r₁ r₂ c₀ c₁ θ : ℝ) (u : Plane) :
    HasDerivAt (fun t => ellPage r₁ r₂ c₀ c₁ t u)
      ![0, 0, r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) *
          (-Real.sin (2 * Real.pi * θ) * (2 * Real.pi * 1)),
        r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) *
          (Real.cos (2 * Real.pi * θ) * (2 * Real.pi * 1))] θ := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact (((hasDerivAt_id θ).const_mul (2 * Real.pi)).cos).const_mul _
  · exact (((hasDerivAt_id θ).const_mul (2 * Real.pi)).sin).const_mul _

/-- The map `(θ, u) ↦ page θ u` has injective differential on `ℝ × (open disk)`. -/
theorem ellPage_joint_regular {r₁ r₂ c₀ c₁ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) (u : Plane) (hu : u ∈ openUnitDisk) :
    Function.Injective
      (fderiv ℝ (fun z : ℝ × Plane => ellPage r₁ r₂ c₀ c₁ z.1 z.2) (θ, u)) := by
  set Φ := fun z : ℝ × Plane => ellPage r₁ r₂ c₀ c₁ z.1 z.2
  have hΦ : DifferentiableAt ℝ Φ (θ, u) :=
    ((ellPage_contDiff r₁ r₂ c₀ c₁).differentiable (by simp)).differentiableAt
  set L := fderiv ℝ Φ (θ, u)
  have hu' : fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u = L.comp (ContinuousLinearMap.inr ℝ ℝ Plane) :=
    (hΦ.hasFDerivAt.comp u (hasFDerivAt_prodMk_right θ u)).fderiv
  have hθ : HasDerivAt (fun t => ellPage r₁ r₂ c₀ c₁ t u) (L ((1 : ℝ), (0 : Plane))) θ := by
    have := (hΦ.hasFDerivAt.comp θ (hasFDerivAt_prodMk_left θ u)).hasDerivAt
    refine this.congr_deriv ?_
    simp [L]
  have hLθ := hθ.unique (ellPage_hasDerivAt_angle r₁ r₂ c₀ c₁ θ u)
  have hg := stereo_g_pos hu
  rw [injective_iff_map_eq_zero]
  rintro ⟨a, v⟩ hz
  have hsplit : ((a, v) : ℝ × Plane) = a • ((1 : ℝ), (0 : Plane)) + ((0 : ℝ), v) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, hLθ] at hz
  have hv : L ((0 : ℝ), v) = fderiv ℝ (ellPage r₁ r₂ c₀ c₁ θ) u v := by
    rw [hu']; rfl
  rw [hv] at hz
  have hp := congrArg (ellPerp θ) hz
  rw [map_add, map_smul, ellPerp_fderiv, map_zero, add_zero, ellPerp_apply] at hp
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
  simp only [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
    smul_eq_mul] at hp
  have ha : a = 0 := by
    have hne : r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) * (2 * Real.pi) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h₂ hg.ne') (by positivity)
    have : a * (r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) * (2 * Real.pi)) = 0 := by
      linear_combination -hp - a * r₂ * ((1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)) *
        (2 * Real.pi) * hcs
    exact (mul_eq_zero.1 this).resolve_right hne
  subst ha
  rw [zero_smul, zero_add] at hz
  have hv0 : v = 0 := (injective_iff_map_eq_zero _).1
    (ellPage_fderiv_injective h₁ h₂ hc θ u) v hz
  rw [hv0]; rfl

end

end HryniewiczCriterion

namespace HryniewiczCriterion

noncomputable section

/-- The `z₂`-plane of a trajectory with `z₂(0) ≠ 0` rotates with angular speed `2/r₂²`:
`z₂(t) = ρ e^{i(2t/r₂² + 2πt₀)}`. -/
theorem ellipsoid_trajectory_z2_polar {r₁ r₂ : ℝ} {y : ℝ → R4}
    (hy : IsTrajectory (ellipsoidH r₁ r₂) y) (h0 : y 0 2 ^ 2 + y 0 3 ^ 2 ≠ 0) :
    ∃ ρ > 0, ∃ t₀ : ℝ, ∀ t,
      y t 2 = ρ * Real.cos (2 / r₂ ^ 2 * t + 2 * Real.pi * t₀) ∧
        y t 3 = ρ * Real.sin (2 / r₂ ^ 2 * t + 2 * Real.pi * t₀) := by
  have hpos : 0 < y 0 2 ^ 2 + y 0 3 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
  set ρ := Real.sqrt (y 0 2 ^ 2 + y 0 3 ^ 2)
  have hρ : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρ2 : ρ ^ 2 = y 0 2 ^ 2 + y 0 3 ^ 2 := Real.sq_sqrt hpos.le
  obtain ⟨t₀, hc, hs⟩ := exists_cos_sin_eq (y 0 2 / ρ) (y 0 3 / ρ) (by
    rw [div_pow, div_pow, ← add_div, ← hρ2, div_self (by positivity)])
  refine ⟨ρ, hρ, t₀, fun t => ?_⟩
  obtain ⟨e2, e3⟩ := (ellipsoid_trajectory_eq hy t).2
  rw [Real.cos_add, Real.sin_add, hc, hs]
  constructor
  · rw [e2]; field_simp
  · rw [e3]; field_simp

/-- On the axis `z₂ = 0` of the energy surface, every point lies on the boundary circle
`ellPage θ (circlePoint t)`. -/
theorem ellPage_axis_point {r₁ r₂ c₀ c₁ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (hc : c₀ ^ 2 + c₁ ^ 2 = 1) (θ : ℝ) (y : R4) (hy : ellipsoidH r₁ r₂ y = 1)
    (h2 : y 2 = 0) (h3 : y 3 = 0) :
    ∃ t, ellPage r₁ r₂ c₀ c₁ θ (circlePoint t) = y := by
  have hE : y 0 ^ 2 + y 1 ^ 2 = r₁ ^ 2 := by
    simp only [ellipsoidH, h2, h3] at hy
    have h' : (y 0 ^ 2 + y 1 ^ 2) / r₁ ^ 2 = 1 := by simpa using hy
    exact (div_eq_one_iff_eq (by positivity)).1 h'
  obtain ⟨t, ht1, ht2⟩ := exists_cos_sin_eq ((c₀ * y 0 + c₁ * y 1) / r₁)
    ((c₀ * y 1 - c₁ * y 0) / r₁) (by
      rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity), ← hE]
      linear_combination (y 0 ^ 2 + y 1 ^ 2) * hc)
  refine ⟨t, ?_⟩
  rw [ellPage_circlePoint, ht1, ht2]
  have hr := h₁.ne'
  ext i
  fin_cases i
  · simp; field_simp; linear_combination y 0 * hc
  · simp; field_simp; linear_combination y 1 * hc
  · simp [h2]
  · simp [h3]

/-- The stereographic open book of the axis `z₂ = 0` of an ellipsoid. -/
theorem ellipsoid_axis_z2_hasAdaptedDiskOpenBook {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (P : PeriodicOrbit (ellipsoidH r₁ r₂)) (hP : P.IsPrime)
    (hax : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0}) :
    HasAdaptedDiskOpenBook (ellipsoidH r₁ r₂) P := by
  obtain ⟨hT, hE⟩ := ellipsoid_axis_orbit_period h₁ P hP hax
  have hax' : ∀ t, P.x t 2 = 0 ∧ P.x t 3 = 0 := fun t => hax ⟨t, rfl⟩
  have hr₁ := h₁.ne'
  have hr₂ := h₂.ne'
  set c₀ := P.x 0 0 / r₁
  set c₁ := P.x 0 1 / r₁
  have hc : c₀ ^ 2 + c₁ ^ 2 = 1 := by
    simp only [c₀, c₁]
    rw [div_pow, div_pow, ← add_div, hE, div_self (by positivity)]
  set e := ellPage r₁ r₂ c₀ c₁
  -- binding
  have hbind : ∀ θ t, e θ (circlePoint t) = P.x (P.T * t) := by
    intro θ t
    have hk : 2 / r₁ ^ 2 * (P.T * t) = 2 * Real.pi * t := by rw [hT]; field_simp
    obtain ⟨f0, f1⟩ := (ellipsoid_trajectory_eq P.trajectory (P.T * t)).1
    simp only [e]
    rw [ellPage_circlePoint]
    ext i
    fin_cases i
    · show r₁ * (c₀ * Real.cos (2 * Real.pi * t) - c₁ * Real.sin (2 * Real.pi * t)) =
        P.x (P.T * t) 0
      rw [f0, hk]; simp only [c₀, c₁]; field_simp
    · show r₁ * (c₀ * Real.sin (2 * Real.pi * t) + c₁ * Real.cos (2 * Real.pi * t)) =
        P.x (P.T * t) 1
      rw [f1, hk]; simp only [c₀, c₁]; field_simp
    · simp [(hax' _).1]
    · simp [(hax' _).2]
  -- the boundary circle is the orbit
  have himage : ∀ θ, e θ '' unitCircle = P.image := by
    intro θ
    apply Set.Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
      obtain ⟨t, ht1, ht2⟩ := exists_cos_sin_eq (u 0) (u 1) hu'
      have : u = circlePoint t := by
        ext j; fin_cases j
        · simp [circlePoint, ht1]
        · simp [circlePoint, ht2]
      rw [this, hbind]
      exact ⟨_, rfl⟩
    · rintro _ ⟨s, rfl⟩
      refine ⟨circlePoint (s / P.T), ?_, ?_⟩
      · show Real.cos _ ^ 2 + Real.sin _ ^ 2 = 1
        rw [add_comm]; exact Real.sin_sq_add_cos_sq _
      · rw [hbind, mul_div_cancel₀ _ P.T_pos.ne']
  -- points of `S` off the orbit have `z₂ ≠ 0`
  have hoff : ∀ y : R4, ellipsoidH r₁ r₂ y = 1 → y ∉ P.image → y 2 ^ 2 + y 3 ^ 2 ≠ 0 := by
    intro y hy hyP h0
    have h2 : y 2 = 0 := by nlinarith [sq_nonneg (y 2), sq_nonneg (y 3)]
    have h3 : y 3 = 0 := by nlinarith [sq_nonneg (y 2), sq_nonneg (y 3)]
    obtain ⟨t, ht⟩ := ellPage_axis_point h₁ h₂ hc 0 y hy h2 h3
    apply hyP
    rw [← ht, ← himage 0]
    refine ⟨circlePoint t, ?_, rfl⟩
    show Real.cos _ ^ 2 + Real.sin _ ^ 2 = 1
    rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  -- a trajectory off the orbit meets page `θ` at the times `π r₂² (θ - t₀ + k)`
  have hhit : ∀ θ, ∀ y : ℝ → R4, IsTrajectory (ellipsoidH r₁ r₂) y → y 0 ∉ P.image →
      ∃ t₀ : ℝ, ∀ k : ℤ,
        y (Real.pi * r₂ ^ 2 * (θ - t₀ + k)) ∈ e θ '' closedUnitDisk := by
    intro θ y hy hy0
    obtain ⟨ρ, hρ, t₀, hpol⟩ := ellipsoid_trajectory_z2_polar hy (hoff _ (hy.2 0) hy0)
    refine ⟨t₀, fun k => ?_⟩
    set t := Real.pi * r₂ ^ 2 * (θ - t₀ + k)
    have hk : 2 / r₂ ^ 2 * t + 2 * Real.pi * t₀ = 2 * Real.pi * θ + k * (2 * Real.pi) := by
      simp only [t]; field_simp; ring
    obtain ⟨p2, p3⟩ := hpol t
    rw [hk, Real.cos_add_int_mul_two_pi] at p2
    rw [hk, Real.sin_add_int_mul_two_pi] at p3
    obtain ⟨u, hu, -, hue⟩ := ellPage_surj h₁ h₂ hc θ (ρ / r₂) (by positivity) (y t) (hy.2 t)
      (by rw [p2]; field_simp) (by rw [p3]; field_simp)
    exact ⟨u, hu, hue⟩
  refine ⟨{
    page := e
    smooth := ellPage_contDiff r₁ r₂ c₀ c₁
    periodic := ?_
    page_section := ?_
    binding := hbind
    page_positive := fun θ u hu => ellPage_omega0_pos hr₁ hc θ u hu
    fibration := ?_
    regular := fun θ u hu => ellPage_joint_regular hr₁ hr₂ hc θ u hu }⟩
  · intro θ u
    have h1 : 2 * Real.pi * (θ + 1) = 2 * Real.pi * θ + 2 * Real.pi := by ring
    simp only [e, ellPage, h1, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · intro θ
    refine ⟨⟨ellPage_contDiff_page r₁ r₂ c₀ c₁ θ,
      (ellPage_injective hr₁ hr₂ hc θ).injOn,
      fun u _ => ellPage_fderiv_injective hr₁ hr₂ hc θ u⟩, ?_, himage θ,
      fun u hu => ellPage_transverse hr₂ θ u hu, ?_⟩
    · rintro _ ⟨u, -, rfl⟩
      exact ellPage_energy hr₁ hr₂ hc θ u
    · intro y hy hy0 a
      obtain ⟨t₀, hk⟩ := hhit θ y hy hy0
      have hpi : 0 < Real.pi * r₂ ^ 2 := by positivity
      obtain ⟨k₁, hk₁⟩ := exists_int_gt (a / (Real.pi * r₂ ^ 2) - θ + t₀)
      obtain ⟨k₂, hk₂⟩ := exists_int_lt (a / (Real.pi * r₂ ^ 2) - θ + t₀)
      refine ⟨⟨_, ?_, hk k₁⟩, ⟨_, ?_, hk k₂⟩⟩
      · have : a / (Real.pi * r₂ ^ 2) < θ - t₀ + k₁ := by linarith
        rw [div_lt_iff₀ hpi] at this
        linarith
      · have : θ - t₀ + k₂ < a / (Real.pi * r₂ ^ 2) := by linarith
        rw [lt_div_iff₀ hpi] at this
        linarith
  · intro y hy hyP
    have hy' : ellipsoidH r₁ r₂ y = 1 := hy
    have h0 := hoff y hy' hyP
    have hpos : 0 < y 2 ^ 2 + y 3 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set ρ := Real.sqrt (y 2 ^ 2 + y 3 ^ 2)
    have hρ : 0 < ρ := Real.sqrt_pos.2 hpos
    have hρ2 : ρ ^ 2 = y 2 ^ 2 + y 3 ^ 2 := Real.sq_sqrt hpos.le
    obtain ⟨t₀, hc0, hs0⟩ := exists_cos_sin_eq (y 2 / ρ) (y 3 / ρ) (by
      rw [div_pow, div_pow, ← add_div, ← hρ2, div_self (by positivity)])
    set θ := Int.fract t₀
    have hθ : 2 * Real.pi * θ = 2 * Real.pi * t₀ + ((-⌊t₀⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
      simp only [θ, Int.fract]; push_cast; ring
    have hcθ : Real.cos (2 * Real.pi * θ) = y 2 / ρ := by
      rw [hθ, Real.cos_add_int_mul_two_pi, hc0]
    have hsθ : Real.sin (2 * Real.pi * θ) = y 3 / ρ := by
      rw [hθ, Real.sin_add_int_mul_two_pi, hs0]
    obtain ⟨u, -, hu, hue⟩ := ellPage_surj h₁ h₂ hc θ (ρ / r₂) (by positivity) y hy'
      (by rw [hcθ]; field_simp) (by rw [hsθ]; field_simp)
    refine ⟨(θ, u), ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, hu (by positivity), hue⟩, ?_⟩
    rintro ⟨θ', u'⟩ ⟨hθ', hu', hue'⟩
    simp only at hθ' hu' hue'
    -- compare the `z₂`-components
    have hg := stereo_g_pos (hu (by positivity))
    have hg' := stereo_g_pos hu'
    have hz2 := congrArg (fun w : R4 => w 2) (hue.trans hue'.symm)
    have hz3 := congrArg (fun w : R4 => w 3) (hue.trans hue'.symm)
    simp only [e, ellPage, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons] at hz2 hz3
    set g := (1 - u 0 ^ 2 - u 1 ^ 2) / (1 + u 0 ^ 2 + u 1 ^ 2)
    set g' := (1 - u' 0 ^ 2 - u' 1 ^ 2) / (1 + u' 0 ^ 2 + u' 1 ^ 2)
    have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * θ)
    have hcs' := Real.sin_sq_add_cos_sq (2 * Real.pi * θ')
    have hgg : g = g' := by
      have : (r₂ * g) ^ 2 = (r₂ * g') ^ 2 := by
        linear_combination (r₂ * g * Real.cos (2 * Real.pi * θ) +
          r₂ * g' * Real.cos (2 * Real.pi * θ')) * hz2 +
          (r₂ * g * Real.sin (2 * Real.pi * θ) + r₂ * g' * Real.sin (2 * Real.pi * θ')) * hz3 +
          (r₂ * g') ^ 2 * hcs' - (r₂ * g) ^ 2 * hcs
      have := (sq_eq_sq₀ (by positivity) (by positivity)).1 this
      exact mul_left_cancel₀ hr₂ this
    rw [← hgg] at hz2 hz3
    have hrg : r₂ * g ≠ 0 := mul_ne_zero hr₂ hg.ne'
    have hθθ : θ' = θ := eq_of_cos_sin_eq hθ' ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      (mul_left_cancel₀ hrg hz2).symm (mul_left_cancel₀ hrg hz3).symm
    subst hθθ
    have huu : u' = u := ellPage_injective hr₁ hr₂ hc θ (hue'.trans hue.symm)
    rw [huu]

end

end HryniewiczCriterion

namespace HryniewiczCriterion

noncomputable section

/-- The swap `(z₁, z₂) ↦ (z₂, z₁)` of the two complex coordinates of `ℝ⁴`. -/
def swapCLM : R4 →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) (![2, 3, 0, 1] i)

theorem swapCLM_apply (x : R4) : swapCLM x = ![x 2, x 3, x 0, x 1] := by
  ext i; fin_cases i <;> rfl

theorem swapCLM_swapCLM (x : R4) : swapCLM (swapCLM x) = x := by
  ext i; fin_cases i <;> rfl

theorem swapCLM_injective : Function.Injective swapCLM := by
  intro x y h
  rw [← swapCLM_swapCLM x, h, swapCLM_swapCLM]

theorem ellipsoidH_swap (r₁ r₂ : ℝ) (x : R4) :
    ellipsoidH r₂ r₁ (swapCLM x) = ellipsoidH r₁ r₂ x := by
  simp [ellipsoidH, swapCLM_apply]; ring

theorem hamiltonianVectorField_ellipsoid_swap (r₁ r₂ : ℝ) (x : R4) :
    hamiltonianVectorField (ellipsoidH r₂ r₁) (swapCLM x) =
      swapCLM (hamiltonianVectorField (ellipsoidH r₁ r₂) x) := by
  rw [ellipsoidH_hamiltonianVectorField, ellipsoidH_hamiltonianVectorField, swapCLM_apply,
    swapCLM_apply]
  ext i; fin_cases i <;> simp

theorem omega0_swap (u v : R4) : omega0 (swapCLM u) (swapCLM v) = omega0 u v := by
  simp [omega0, swapCLM_apply]; ring

theorem isTrajectory_ellipsoid_swap {r₁ r₂ : ℝ} {y : ℝ → R4}
    (hy : IsTrajectory (ellipsoidH r₁ r₂) y) :
    IsTrajectory (ellipsoidH r₂ r₁) (fun t => swapCLM (y t)) := by
  refine ⟨fun t => ?_, fun t => by rw [ellipsoidH_swap]; exact hy.2 t⟩
  rw [hamiltonianVectorField_ellipsoid_swap]
  exact swapCLM.hasFDerivAt.comp_hasDerivAt t (hy.1 t)

theorem fderiv_swapCLM_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → R4} {u : E} (hf : DifferentiableAt ℝ f u) :
    fderiv ℝ (fun x => swapCLM (f x)) u = swapCLM.comp (fderiv ℝ f u) :=
  (swapCLM.hasFDerivAt.comp u hf.hasFDerivAt).fderiv

/-- The swapped periodic orbit. -/
def PeriodicOrbit.ellipsoidSwap {r₁ r₂ : ℝ} (P : PeriodicOrbit (ellipsoidH r₁ r₂)) :
    PeriodicOrbit (ellipsoidH r₂ r₁) where
  x := fun t => swapCLM (P.x t)
  T := P.T
  T_pos := P.T_pos
  trajectory := isTrajectory_ellipsoid_swap P.trajectory
  periodic := fun t => by simp only [P.periodic]

theorem PeriodicOrbit.ellipsoidSwap_image {r₁ r₂ : ℝ} (P : PeriodicOrbit (ellipsoidH r₁ r₂)) :
    (P.ellipsoidSwap).image = swapCLM '' P.image := by
  ext y; constructor
  · rintro ⟨t, rfl⟩; exact ⟨P.x t, ⟨t, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩

theorem mem_image_swap_iff {S : Set R4} {y : R4} : swapCLM y ∈ swapCLM '' S ↔ y ∈ S :=
  swapCLM_injective.mem_set_image

/-- Transport of an adapted open book along the swap. -/
theorem hasAdaptedDiskOpenBook_ellipsoid_swap {r₁ r₂ : ℝ} (P : PeriodicOrbit (ellipsoidH r₁ r₂))
    (hB : HasAdaptedDiskOpenBook (ellipsoidH r₂ r₁) P.ellipsoidSwap) :
    HasAdaptedDiskOpenBook (ellipsoidH r₁ r₂) P := by
  obtain ⟨B⟩ := hB
  have hdiff : ∀ θ u, DifferentiableAt ℝ (B.page θ) u := fun θ u =>
    (((B.page_section θ).1.1).differentiable (by simp)).differentiableAt
  have hS : ∀ y : R4, ellipsoidH r₁ r₂ (swapCLM y) = ellipsoidH r₂ r₁ y := fun y => by
    rw [← ellipsoidH_swap r₁ r₂ (swapCLM y), swapCLM_swapCLM]
  have himg : ∀ y : R4, swapCLM y ∈ P.image ↔ y ∈ P.ellipsoidSwap.image := by
    intro y
    rw [PeriodicOrbit.ellipsoidSwap_image]
    constructor
    · intro h; rw [← swapCLM_swapCLM y]; exact ⟨_, h, rfl⟩
    · rintro ⟨z, hz, hzy⟩; rw [← hzy, swapCLM_swapCLM]; exact hz
  refine ⟨{
    page := fun θ u => swapCLM (B.page θ u)
    smooth := swapCLM.contDiff.comp B.smooth
    periodic := fun θ u => by simp only [B.periodic]
    page_section := fun θ => ?_
    binding := fun θ t => by
      simp only [B.binding]
      exact swapCLM_swapCLM _
    page_positive := fun θ u hu => by
      rw [fderiv_swapCLM_comp (hdiff θ u)]
      simp only [ContinuousLinearMap.comp_apply, omega0_swap]
      exact B.page_positive θ u hu
    fibration := fun y hy hyP => ?_
    regular := fun θ u hu => ?_ }⟩
  · obtain ⟨⟨hsm, hinj, hfd⟩, hE, hI, htr, hgl⟩ := B.page_section θ
    refine ⟨⟨swapCLM.contDiff.comp hsm, swapCLM_injective.comp_injOn hinj, fun u hu => ?_⟩,
      ?_, ?_, fun u hu => ?_, fun y hy hy0 a => ?_⟩
    · rw [fderiv_swapCLM_comp (hdiff θ u)]
      exact swapCLM_injective.comp (hfd u hu)
    · rintro _ ⟨u, hu, rfl⟩
      show ellipsoidH r₁ r₂ (swapCLM (B.page θ u)) = 1
      rw [hS]; exact hE ⟨u, hu, rfl⟩
    · ext y; constructor
      · rintro ⟨u, hu, rfl⟩
        have : B.page θ u ∈ P.ellipsoidSwap.image := hI ▸ ⟨u, hu, rfl⟩
        exact (himg _).2 this
      · intro hy
        have h1 : swapCLM y ∈ P.ellipsoidSwap.image := by
          rw [← himg, swapCLM_swapCLM]; exact hy
        rw [← hI] at h1
        obtain ⟨u, hu, hue⟩ := h1
        refine ⟨u, hu, ?_⟩
        show swapCLM (B.page θ u) = y
        rw [hue, swapCLM_swapCLM]
    · rintro ⟨v, hv⟩
      apply htr u hu
      refine ⟨v, swapCLM_injective ?_⟩
      calc swapCLM (fderiv ℝ (B.page θ) u v)
          = fderiv ℝ (fun x => swapCLM (B.page θ x)) u v := by
            rw [fderiv_swapCLM_comp (hdiff θ u)]; rfl
        _ = _ := hv
        _ = _ := hamiltonianVectorField_ellipsoid_swap r₂ r₁ _
    · have hy' := isTrajectory_ellipsoid_swap hy
      have hy0' : swapCLM (y 0) ∉ P.ellipsoidSwap.image := by
        rw [← himg, swapCLM_swapCLM]; exact hy0
      obtain ⟨⟨t₁, ht₁, ⟨u₁, hu₁, he₁⟩⟩, ⟨t₂, ht₂, ⟨u₂, hu₂, he₂⟩⟩⟩ := hgl _ hy' hy0' a
      refine ⟨⟨t₁, ht₁, u₁, hu₁, ?_⟩, ⟨t₂, ht₂, u₂, hu₂, ?_⟩⟩
      · show swapCLM (B.page θ u₁) = y t₁
        rw [he₁, swapCLM_swapCLM]
      · show swapCLM (B.page θ u₂) = y t₂
        rw [he₂, swapCLM_swapCLM]
  · have hy' : swapCLM y ∈ energySurface (ellipsoidH r₂ r₁) := by
      show ellipsoidH r₂ r₁ (swapCLM y) = 1
      rw [ellipsoidH_swap]; exact hy
    have hyP' : swapCLM y ∉ P.ellipsoidSwap.image := by
      rw [← himg, swapCLM_swapCLM]; exact hyP
    obtain ⟨z, hz, huniq⟩ := B.fibration _ hy' hyP'
    refine ⟨z, ⟨hz.1, hz.2.1, ?_⟩, fun z' hz' => huniq z' ⟨hz'.1, hz'.2.1, ?_⟩⟩
    · show swapCLM (B.page z.1 z.2) = y
      rw [hz.2.2, swapCLM_swapCLM]
    · have := hz'.2.2
      rw [← this, swapCLM_swapCLM]
  · have hΦ : DifferentiableAt ℝ (fun z : ℝ × Plane => B.page z.1 z.2) (θ, u) :=
      (B.smooth.differentiable (by simp)).differentiableAt
    show Function.Injective
      (fderiv ℝ (fun z : ℝ × Plane => swapCLM (B.page z.1 z.2)) (θ, u))
    rw [fderiv_swapCLM_comp hΦ]
    exact swapCLM_injective.comp (B.regular θ u hu)

end

end HryniewiczCriterion

namespace HryniewiczCriterion

theorem ellipsoid_axes_bind_adapted_open_books_aux (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (P : PeriodicOrbit
      (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2))
    (hP : P.IsPrime)
    (haxis : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0} ∨ P.image ⊆ {x | x 0 = 0 ∧ x 1 = 0}) :
    HasAdaptedDiskOpenBook
      (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2) P := by
  change PeriodicOrbit (ellipsoidH r₁ r₂) at P
  change HasAdaptedDiskOpenBook (ellipsoidH r₁ r₂) P
  rcases haxis with h | h
  · exact ellipsoid_axis_z2_hasAdaptedDiskOpenBook h₁ h₂ P hP h
  · refine hasAdaptedDiskOpenBook_ellipsoid_swap P
      (ellipsoid_axis_z2_hasAdaptedDiskOpenBook h₂ h₁ P.ellipsoidSwap ?_ ?_)
    · intro t ht hT heq
      exact hP t ht hT (swapCLM_injective heq)
    · rw [PeriodicOrbit.ellipsoidSwap_image]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨h0, h1⟩ := h hy
      simp [swapCLM_apply, h0, h1]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (P : PeriodicOrbit
      (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2))
    (hP : P.IsPrime)
    (haxis : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0} ∨ P.image ⊆ {x | x 0 = 0 ∧ x 1 = 0}) :
    HasAdaptedDiskOpenBook
      (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2) P :=
  ellipsoid_axes_bind_adapted_open_books_aux r₁ r₂ h₁ h₂ P hP haxis
