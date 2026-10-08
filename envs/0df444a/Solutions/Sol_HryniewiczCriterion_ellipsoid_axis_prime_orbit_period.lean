-- Prove2me | solution 1 for HryniewiczCriterion.ellipsoid_axis_prime_orbit_period
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:20:31.046231+00:00
-- url     : https://prove2.me/submissions/a898ad87-f2f7-43a1-8eb8-b756f45db7cb

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

open HryniewiczCriterion

theorem solution {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (P : PeriodicOrbit (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2)) (hP : P.IsPrime)
    (hax : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0}) :
    P.T = Real.pi * r₁ ^ 2 ∧ P.x 0 0 ^ 2 + P.x 0 1 ^ 2 = r₁ ^ 2 :=
  ellipsoid_axis_orbit_period h₁ P hP hax
