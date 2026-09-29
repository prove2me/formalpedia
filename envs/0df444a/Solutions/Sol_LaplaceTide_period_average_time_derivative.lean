-- Prove2me | solution 1 for LaplaceTide.period_average_time_derivative
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:18:01.199996+00:00
-- url     : https://prove2.me/submissions/2307953b-5217-46d6-8997-1280218c17a7

import Mathlib
import Definitions.Def_LaplaceTide_core

open LaplaceTide

theorem W3a_LaplaceTide_int_deriv_zero (T : ℝ) (E : ℝ → ℝ)
    (hdiff : Differentiable ℝ E) (hcont : Continuous (deriv E)) (hper : Function.Periodic E T) :
    ∫ t in (0 : ℝ)..T, deriv E t = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub (fun s _ => hdiff s) (hcont.intervalIntegrable 0 T)]
  have := hper 0
  rw [zero_add] at this
  rw [this, sub_self]

theorem solution (T : ℝ) (E : ℝ → ℝ) (hT : 0 < T)
    (hdiff : Differentiable ℝ E) (hcont : Continuous (deriv E)) (hper : Function.Periodic E T) :
    (1 / T) * ∫ t in (0 : ℝ)..T, deriv E t = 0 := by
  rw [W3a_LaplaceTide_int_deriv_zero T E hdiff hcont hper, mul_zero]

theorem W3a_LaplaceTide_vertical_structure_mode (N Dstar g : ℝ) (n : ℕ) (Dn : ℝ) (Fw : ℝ → ℝ)
    (hN : 0 < N) (hDstar : 0 < Dstar) (hg : 0 < g) (hn : 1 ≤ n)
    (hDn : Dn = (N * Dstar) ^ 2 / (g * (n : ℝ) ^ 2 * Real.pi ^ 2))
    (hFw : ∀ z, Fw z = Real.sin ((n : ℝ) * Real.pi * (z + Dstar) / Dstar)) :
    (∀ z, deriv (deriv Fw) z + (N ^ 2 / (g * Dn)) * Fw z = 0) ∧
      Fw (-Dstar) = 0 ∧ Fw 0 = 0 := by
  have hF : Fw = fun z => Real.sin ((n : ℝ) * Real.pi * (z + Dstar) / Dstar) := funext hFw
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hd1 : ∀ z, HasDerivAt Fw
      (Real.cos ((n : ℝ) * Real.pi * (z + Dstar) / Dstar) * ((n : ℝ) * Real.pi / Dstar)) z := by
    intro z
    rw [hF]
    have h := ((((hasDerivAt_id z).add_const Dstar).const_mul ((n : ℝ) * Real.pi)).div_const
      Dstar).sin
    exact h.congr_deriv (by simp only [id]; ring)
  have hdF : deriv Fw = fun z =>
      Real.cos ((n : ℝ) * Real.pi * (z + Dstar) / Dstar) * ((n : ℝ) * Real.pi / Dstar) :=
    funext fun z => (hd1 z).deriv
  have hd2 : ∀ z, HasDerivAt (deriv Fw)
      (-Real.sin ((n : ℝ) * Real.pi * (z + Dstar) / Dstar) * ((n : ℝ) * Real.pi / Dstar)
        * ((n : ℝ) * Real.pi / Dstar)) z := by
    intro z
    rw [hdF]
    have h := (((((hasDerivAt_id z).add_const Dstar).const_mul ((n : ℝ) * Real.pi)).div_const
      Dstar).cos).mul_const ((n : ℝ) * Real.pi / Dstar)
    exact h.congr_deriv (by simp only [id]; ring)
  have hk : N ^ 2 / (g * Dn) = ((n : ℝ) * Real.pi / Dstar) ^ 2 := by
    rw [hDn]
    have := Real.pi_pos
    field_simp
  refine ⟨fun z => ?_, ?_, ?_⟩
  · rw [(hd2 z).deriv, hk, hFw z]
    ring
  · rw [hFw]
    simp
  · rw [hFw]
    rw [show (n : ℝ) * Real.pi * (0 + Dstar) / Dstar = (n : ℝ) * Real.pi by
      rw [zero_add]; field_simp]
    exact Real.sin_nat_mul_pi n

theorem W3a_LaplaceTide_hdt (k σ x t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ((k : ℂ) * x - (σ : ℂ) * s)))
      (Complex.exp (Complex.I * ((k : ℂ) * x - (σ : ℂ) * t)) * (-(Complex.I * σ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h := ((h1.const_mul (σ : ℂ)).const_sub ((k : ℂ) * x)).const_mul Complex.I |>.cexp
  exact h.congr_deriv (by ring)

theorem W3a_LaplaceTide_hdx (k σ x t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ((k : ℂ) * s - (σ : ℂ) * t)))
      (Complex.exp (Complex.I * ((k : ℂ) * x - (σ : ℂ) * t)) * (Complex.I * k)) x := by
  have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 x := (hasDerivAt_id x).ofReal_comp
  have h := ((h1.const_mul (k : ℂ)).sub_const ((σ : ℂ) * t)).const_mul Complex.I |>.cexp
  exact h.congr_deriv (by ring)

theorem W3a_LaplaceTide_barotropic_plane_wave (g Dstar a k sigma : ℝ) (Z U : ℝ → ℝ → ℂ)
    (hg : 0 < g) (hDstar : 0 < Dstar) (ha : a ≠ 0) (hsigma : sigma ≠ 0)
    (hZ : ∀ x t, Z x t = (a : ℂ) * Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t)))
    (hU : ∀ x t, U x t = (a : ℂ) * ((g * k / sigma : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t))) :
    ((∀ x t, deriv (fun s => U x s) t = -(g : ℂ) * deriv (fun s => Z s t) x) ∧
      (∀ x t, deriv (fun s => Z x s) t + (Dstar : ℂ) * deriv (fun s => U s t) x = 0)) ↔
      (sigma = k * Real.sqrt (g * Dstar) ∨ sigma = -(k * Real.sqrt (g * Dstar))) := by
  have hs : (sigma : ℂ) ≠ 0 := by exact_mod_cast hsigma
  have hinv : (sigma : ℂ) * (sigma : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs
  have hC : ((g * k / sigma : ℝ) : ℂ) = (g : ℂ) * k * (sigma : ℂ)⁻¹ := by
    push_cast; ring
  have dUt : ∀ x t, deriv (fun s => U x s) t = (a : ℂ) * ((g : ℂ) * k * (sigma : ℂ)⁻¹) *
      (Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t)) * (-(Complex.I * sigma))) := by
    intro x t
    have hf : (fun s => U x s) = fun s : ℝ => (a : ℂ) * ((g * k / sigma : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * (s : ℂ))) := funext fun s => hU x s
    rw [hf, ((W3a_LaplaceTide_hdt k sigma x t).const_mul _).deriv, hC]
  have dUx : ∀ x t, deriv (fun s => U s t) x = (a : ℂ) * ((g : ℂ) * k * (sigma : ℂ)⁻¹) *
      (Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t)) * (Complex.I * k)) := by
    intro x t
    have hf : (fun s => U s t) = fun s : ℝ => (a : ℂ) * ((g * k / sigma : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((k : ℂ) * (s : ℂ) - (sigma : ℂ) * t)) := funext fun s => hU s t
    rw [hf, ((W3a_LaplaceTide_hdx k sigma x t).const_mul _).deriv, hC]
  have dZt : ∀ x t, deriv (fun s => Z x s) t = (a : ℂ) *
      (Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t)) * (-(Complex.I * sigma))) := by
    intro x t
    have hf : (fun s => Z x s) = fun s : ℝ => (a : ℂ) *
        Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * (s : ℂ))) := funext fun s => hZ x s
    rw [hf, ((W3a_LaplaceTide_hdt k sigma x t).const_mul _).deriv]
  have dZx : ∀ x t, deriv (fun s => Z s t) x = (a : ℂ) *
      (Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t)) * (Complex.I * k)) := by
    intro x t
    have hf : (fun s => Z s t) = fun s : ℝ => (a : ℂ) *
        Complex.exp (Complex.I * ((k : ℂ) * (s : ℂ) - (sigma : ℂ) * t)) := funext fun s => hZ s t
    rw [hf, ((W3a_LaplaceTide_hdx k sigma x t).const_mul _).deriv]
  have hsq : (sigma = k * Real.sqrt (g * Dstar) ∨ sigma = -(k * Real.sqrt (g * Dstar))) ↔
      g * Dstar * k ^ 2 - sigma ^ 2 = 0 := by
    rw [← sq_eq_sq_iff_eq_or_eq_neg, mul_pow, Real.sq_sqrt (by positivity)]
    constructor <;> intro h <;> linarith
  rw [hsq]
  constructor
  · rintro ⟨-, h2⟩
    have eq := h2 0 0
    rw [dZt, dUx] at eq
    set E := Complex.exp (Complex.I * ((k : ℂ) * (0 : ℝ) - (sigma : ℂ) * (0 : ℝ)))
    have h0 : ((a : ℂ) * E * Complex.I) * ((g : ℂ) * Dstar * k ^ 2 - sigma ^ 2) = 0 := by
      linear_combination (sigma : ℂ) * eq - ((a : ℂ) * E * Complex.I * g * Dstar * k ^ 2) * hinv
    have hw : (a : ℂ) * E * Complex.I ≠ 0 := by
      have : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      simp [this, E, Complex.exp_ne_zero]
    have h1 := (mul_eq_zero.1 h0).resolve_left hw
    exact_mod_cast h1
  · intro h
    have hc : (g : ℂ) * Dstar * k ^ 2 - sigma ^ 2 = 0 := by exact_mod_cast h
    refine ⟨fun x t => ?_, fun x t => ?_⟩
    · rw [dUt, dZx]
      set E := Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t))
      linear_combination (-((a : ℂ) * g * k * E * Complex.I)) * hinv
    · rw [dZt, dUx]
      set E := Complex.exp (Complex.I * ((k : ℂ) * x - (sigma : ℂ) * t))
      linear_combination ((a : ℂ) * E * Complex.I * (sigma : ℂ)⁻¹) * hc
        + ((a : ℂ) * E * Complex.I * sigma) * hinv

theorem W3a_LaplaceTide_energy_equation_no_solid_earth_tide
    (f g rho Dc : ℝ) (Gamma Fx Fy u v zeta : Field3)
    (hrho : 0 < rho) (hDc : 0 < Dc)
    (hu : PartialDiff u) (hv : PartialDiff v) (hzeta : PartialDiff zeta)
    (hGamma : PartialDiff Gamma)
    (hlte : IsLTE f g rho (fun _ _ => Dc) Gamma Fx Fy u v zeta (fun _ _ _ => 0)) :
    ∀ x y t,
      1 / 2 * rho * Dc * dt (fun x y t => (u x y t) ^ 2 + (v x y t) ^ 2) x y t
        + 1 / 2 * rho * g * dt (fun x y t => (zeta x y t) ^ 2) x y t
        + (dx (fun x y t => rho * g * zeta x y t * u x y t * Dc) x y t
          + dy (fun x y t => rho * g * zeta x y t * v x y t * Dc) x y t)
      = rho * dt zeta x y t * Gamma x y t
        + (dx (fun x y t => rho * u x y t * Dc * Gamma x y t) x y t
          + dy (fun x y t => rho * v x y t * Dc * Gamma x y t) x y t)
        + (u x y t * Fx x y t + v x y t * Fy x y t) := by
  intro x y t
  have hut : HasDerivAt (fun s => u x y s) (dt u x y t) t := (hu.2.2 x y t).hasDerivAt
  have hvt : HasDerivAt (fun s => v x y s) (dt v x y t) t := (hv.2.2 x y t).hasDerivAt
  have hζt : HasDerivAt (fun s => zeta x y s) (dt zeta x y t) t := (hzeta.2.2 x y t).hasDerivAt
  have hux : HasDerivAt (fun s => u s y t) (dx u x y t) x := (hu.1 x y t).hasDerivAt
  have hvy : HasDerivAt (fun s => v x s t) (dy v x y t) y := (hv.2.1 x y t).hasDerivAt
  have hζx : HasDerivAt (fun s => zeta s y t) (dx zeta x y t) x := (hzeta.1 x y t).hasDerivAt
  have hζy : HasDerivAt (fun s => zeta x s t) (dy zeta x y t) y := (hzeta.2.1 x y t).hasDerivAt
  have hΓx : HasDerivAt (fun s => Gamma s y t) (dx Gamma x y t) x := (hGamma.1 x y t).hasDerivAt
  have hΓy : HasDerivAt (fun s => Gamma x s t) (dy Gamma x y t) y :=
    (hGamma.2.1 x y t).hasDerivAt
  have hu2 : HasDerivAt (fun s => u x y s ^ 2) (2 * u x y t * dt u x y t) t :=
    (hut.pow 2).congr_deriv (by simp)
  have hv2 : HasDerivAt (fun s => v x y s ^ 2) (2 * v x y t * dt v x y t) t :=
    (hvt.pow 2).congr_deriv (by simp)
  have hζ2 : HasDerivAt (fun s => zeta x y s ^ 2) (2 * zeta x y t * dt zeta x y t) t :=
    (hζt.pow 2).congr_deriv (by simp)
  have e1 : dt (fun x y t => (u x y t) ^ 2 + (v x y t) ^ 2) x y t = _ := (hu2.add hv2).deriv
  have e2 : dt (fun x y t => (zeta x y t) ^ 2) x y t = _ := hζ2.deriv
  have e3 : dx (fun x y t => rho * g * zeta x y t * u x y t * Dc) x y t = _ :=
    (((hζx.const_mul (rho * g)).mul hux).mul_const Dc).deriv
  have e4 : dy (fun x y t => rho * g * zeta x y t * v x y t * Dc) x y t = _ :=
    (((hζy.const_mul (rho * g)).mul hvy).mul_const Dc).deriv
  have e5 : dx (fun x y t => rho * u x y t * Dc * Gamma x y t) x y t = _ :=
    (((hux.const_mul rho).mul_const Dc).mul hΓx).deriv
  have e6 : dy (fun x y t => rho * v x y t * Dc * Gamma x y t) x y t = _ :=
    (((hvy.const_mul rho).mul_const Dc).mul hΓy).deriv
  have e7 : dx (fun x y t => u x y t * Dc) x y t = _ := (hux.mul_const Dc).deriv
  have e8 : dy (fun x y t => v x y t * Dc) x y t = _ := (hvy.mul_const Dc).deriv
  have e9 : dt (fun (_ : ℝ) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) x y t = 0 := by simp [dt]
  have Mx := hlte.momentum_x x y t
  have My := hlte.momentum_y x y t
  have C := hlte.continuity x y t
  beta_reduce at Mx My C
  rw [e7, e8, e9] at C
  have hFx : rho * Dc * (Fx x y t / (rho * Dc)) = Fx x y t := by field_simp
  have hFy : rho * Dc * (Fy x y t / (rho * Dc)) = Fy x y t := by field_simp
  rw [e1, e2, e3, e4, e5, e6]
  linear_combination (rho * Dc * u x y t) * Mx + (rho * Dc * v x y t) * My
    + (rho * g * zeta x y t - rho * Gamma x y t) * C + u x y t * hFx + v x y t * hFy

theorem W3a_LaplaceTide_energy_equation_with_solid_earth_tide
    (f g rho : ℝ) (D : ℝ → ℝ → ℝ) (Gamma Fx Fy u v zeta delta : Field3)
    (hrho : 0 < rho) (hDpos : ∀ x y, 0 < D x y) (hD : PartialDiff₂ D)
    (hu : PartialDiff u) (hv : PartialDiff v) (hzeta : PartialDiff zeta)
    (hdelta : PartialDiff delta) (hGamma : PartialDiff Gamma)
    (hlte : IsLTE f g rho D Gamma Fx Fy u v zeta delta) :
    ∀ x y t, dt (kineticEnergy rho D u v) x y t
      + dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y t
      + dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y t
      + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y t
      = workRate rho g D u v Gamma (observedTide zeta delta) delta x y t
        + (u x y t * Fx x y t + v x y t * Fy x y t) := by
  intro x y t
  have hut : HasDerivAt (fun s => u x y s) (dt u x y t) t := (hu.2.2 x y t).hasDerivAt
  have hvt : HasDerivAt (fun s => v x y s) (dt v x y t) t := (hv.2.2 x y t).hasDerivAt
  have hζt : HasDerivAt (fun s => zeta x y s) (dt zeta x y t) t := (hzeta.2.2 x y t).hasDerivAt
  have hδt : HasDerivAt (fun s => delta x y s) (dt delta x y t) t :=
    (hdelta.2.2 x y t).hasDerivAt
  have hux : HasDerivAt (fun s => u s y t) (dx u x y t) x := (hu.1 x y t).hasDerivAt
  have hvy : HasDerivAt (fun s => v x s t) (dy v x y t) y := (hv.2.1 x y t).hasDerivAt
  have hζx : HasDerivAt (fun s => zeta s y t) (dx zeta x y t) x := (hzeta.1 x y t).hasDerivAt
  have hζy : HasDerivAt (fun s => zeta x s t) (dy zeta x y t) y := (hzeta.2.1 x y t).hasDerivAt
  have hδx : HasDerivAt (fun s => delta s y t) (dx delta x y t) x := (hdelta.1 x y t).hasDerivAt
  have hδy : HasDerivAt (fun s => delta x s t) (dy delta x y t) y :=
    (hdelta.2.1 x y t).hasDerivAt
  have hΓx : HasDerivAt (fun s => Gamma s y t) (dx Gamma x y t) x := (hGamma.1 x y t).hasDerivAt
  have hΓy : HasDerivAt (fun s => Gamma x s t) (dy Gamma x y t) y :=
    (hGamma.2.1 x y t).hasDerivAt
  have hDx : HasDerivAt (fun s => D s y) (deriv (fun s => D s y) x) x := (hD.1 x y).hasDerivAt
  have hDy : HasDerivAt (fun s => D x s) (deriv (fun s => D x s) y) y := (hD.2 x y).hasDerivAt
  have hu2 : HasDerivAt (fun s => u x y s ^ 2) (2 * u x y t * dt u x y t) t :=
    (hut.pow 2).congr_deriv (by simp)
  have hv2 : HasDerivAt (fun s => v x y s ^ 2) (2 * v x y t * dt v x y t) t :=
    (hvt.pow 2).congr_deriv (by simp)
  have hz0 := hζt.sub hδt
  have hz2 : HasDerivAt (fun s => (zeta x y s - delta x y s) ^ 2)
      (2 * (zeta x y t - delta x y t) * (dt zeta x y t - dt delta x y t)) t :=
    (hz0.pow 2).congr_deriv (by simp)
  have eKE : dt (kineticEnergy rho D u v) x y t = _ :=
    ((hu2.add hv2).const_mul (1 / 2 * rho * D x y)).deriv
  have ePE : dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y t = _ :=
    (((hz2.add ((hz0.const_mul 2).mul hδt)).add ((hδt.const_mul 2).mul_const (D x y))).const_mul
      (1 / 2 * rho * g)).deriv
  have eFX : dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y t = _ :=
    (((hDx.const_mul (rho * g)).mul hux).mul ((hζx.sub hδx).add hδx)).deriv
  have eFY : dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y t = _ :=
    (((hDy.const_mul (rho * g)).mul hvy).mul ((hζy.sub hδy).add hδy)).deriv
  have eW0 : dt (observedTide zeta delta) x y t = dt zeta x y t - dt delta x y t := hz0.deriv
  have eW1 : dx (fun x y t => u x y t * D x y * Gamma x y t) x y t = _ :=
    ((hux.mul hDx).mul hΓx).deriv
  have eW2 : dy (fun x y t => v x y t * D x y * Gamma x y t) x y t = _ :=
    ((hvy.mul hDy).mul hΓy).deriv
  have eC1 : dx (fun x y t => u x y t * D x y) x y t = _ := (hux.mul hDx).deriv
  have eC2 : dy (fun x y t => v x y t * D x y) x y t = _ := (hvy.mul hDy).deriv
  have Mx := hlte.momentum_x x y t
  have My := hlte.momentum_y x y t
  have C := hlte.continuity x y t
  rw [eC1, eC2] at C
  have hρD : rho * D x y ≠ 0 := (mul_pos hrho (hDpos x y)).ne'
  have hρ0 : rho ≠ 0 := hrho.ne'
  have hD0 : D x y ≠ 0 := (hDpos x y).ne'
  have hFx : rho * D x y * (Fx x y t / (rho * D x y)) = Fx x y t := by field_simp
  have hFy : rho * D x y * (Fy x y t / (rho * D x y)) = Fy x y t := by field_simp
  simp only [workRate]
  rw [eKE, ePE, eFX, eFY, eW0, eW1, eW2]
  simp only [observedTide]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  linear_combination (rho * D x y * u x y t) * Mx + (rho * D x y * v x y t) * My
    + (rho * g * zeta x y t - rho * Gamma x y t) * C + u x y t * hFx + v x y t * hFy

theorem W3a_LaplaceTide_energy_equation_period_averaged
    (f g rho : ℝ) (D : ℝ → ℝ → ℝ) (Gamma Fx Fy u v zeta delta : Field3)
    (x y T : ℝ) (hT : 0 < T)
    (hrho : 0 < rho) (hDpos : ∀ x y, 0 < D x y) (hD : PartialDiff₂ D)
    (hu : PartialDiff u) (hv : PartialDiff v) (hzeta : PartialDiff zeta)
    (hdelta : PartialDiff delta) (hGamma : PartialDiff Gamma)
    (hlte : IsLTE f g rho D Gamma Fx Fy u v zeta delta)
    (hKEper : Function.Periodic (fun s => kineticEnergy rho D u v x y s) T)
    (hPEper : Function.Periodic
      (fun s => potentialEnergy rho g D (observedTide zeta delta) delta x y s) T)
    (hKEcont : Continuous (fun s => dt (kineticEnergy rho D u v) x y s))
    (hPEcont : Continuous
      (fun s => dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y s))
    (hflux : IntervalIntegrable
      (fun s => dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y s
        + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y s)
      MeasureTheory.volume 0 T) :
    (1 / T) * ∫ t in (0 : ℝ)..T,
        (dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y t
          + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y t)
      = (1 / T) * ∫ t in (0 : ℝ)..T,
        (workRate rho g D u v Gamma (observedTide zeta delta) delta x y t
          + (u x y t * Fx x y t + v x y t * Fy x y t)) := by
  have main := W3a_LaplaceTide_energy_equation_with_solid_earth_tide f g rho D Gamma Fx Fy u v
    zeta delta hrho hDpos hD hu hv hzeta hdelta hGamma hlte x y
  have hKEd : Differentiable ℝ (fun s => kineticEnergy rho D u v x y s) := fun s =>
    ((((hu.2.2 x y s).pow 2).add ((hv.2.2 x y s).pow 2)).const_mul (1 / 2 * rho * D x y))
  have hPEd : Differentiable ℝ
      (fun s => potentialEnergy rho g D (observedTide zeta delta) delta x y s) := fun s =>
    have hz0 := (hzeta.2.2 x y s).sub (hdelta.2.2 x y s)
    (((hz0.pow 2).add ((hz0.const_mul 2).mul (hdelta.2.2 x y s))).add
      (((hdelta.2.2 x y s).const_mul 2).mul_const (D x y))).const_mul (1 / 2 * rho * g)
  have hK0 : ∫ s in (0 : ℝ)..T, dt (kineticEnergy rho D u v) x y s = 0 :=
    W3a_LaplaceTide_int_deriv_zero T _ hKEd hKEcont hKEper
  have hP0 : ∫ s in (0 : ℝ)..T,
      dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y s = 0 :=
    W3a_LaplaceTide_int_deriv_zero T _ hPEd hPEcont hPEper
  have hfun : (fun t => workRate rho g D u v Gamma (observedTide zeta delta) delta x y t
          + (u x y t * Fx x y t + v x y t * Fy x y t)) =
      fun t => (dt (kineticEnergy rho D u v) x y t
        + dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y t)
        + (dx (energyFluxX rho g D u (observedTide zeta delta) delta) x y t
          + dy (energyFluxY rho g D v (observedTide zeta delta) delta) x y t) := by
    funext s
    have := main s
    linarith
  have hi1 : IntervalIntegrable (fun s => dt (kineticEnergy rho D u v) x y s
      + dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y s)
      MeasureTheory.volume 0 T := (hKEcont.add hPEcont).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun s => dt (kineticEnergy rho D u v) x y s)
      MeasureTheory.volume 0 T := hKEcont.intervalIntegrable 0 T
  have hi3 : IntervalIntegrable
      (fun s => dt (potentialEnergy rho g D (observedTide zeta delta) delta) x y s)
      MeasureTheory.volume 0 T := hPEcont.intervalIntegrable 0 T
  rw [hfun, intervalIntegral.integral_add hi1 hflux, intervalIntegral.integral_add hi2 hi3,
    hK0, hP0]
  ring
