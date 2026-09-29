-- Prove2me | solution 1 for ModularCurve.SiegelUnit.differentiableOn_siegelFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/108fb4aa-f67b-5ac0-b8a2-ff0ed4ef6aab

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_jacobiTheta_two_eq_tprod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun

set_option autoImplicit false

noncomputable section

open Complex
p2m_open "UpperHalfPlane~I"
open scoped Manifold
open scoped Real MatrixGroups

namespace E97cSHol

def qq (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

def qa (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := cexp (2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ))

def pref (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * τ)

def sprod (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  (1 - qa N r s τ) * ∏' n : ℕ, ((1 - qq τ ^ (n + 1) * qa N r s τ) *
    (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹))

theorem siegelFun_eq (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * sprod N r s τ := by
  unfold ModularCurve.siegelFun pref sprod qq qa; simp only [mul_assoc]

theorem siegelFun_level_zero (r s : ℤ) (τ : ℂ) : ModularCurve.siegelFun 0 r s τ = 0 := by
  simp [ModularCurve.siegelFun]

theorem qq_add_one (τ : ℂ) : qq (τ + 1) = qq τ := by
  unfold qq
  rw [show 2 * π * I * (τ + 1) = 2 * π * I * τ + 2 * π * I by ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

theorem qa_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s (τ + 1) = qa N r (r + s) τ := by
  unfold qa
  push_cast
  ring_nf

theorem pref_add_one (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) :
    pref N r s (τ + 1) = cexp (π * I / 6) * pref N r (r + s) τ := by
  unfold pref
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [neg_mul, neg_mul, mul_neg, neg_inj, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem sprod_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) : sprod N r s (τ + 1) = sprod N r (r + s) τ := by
  unfold sprod
  rw [qq_add_one, qa_add_one]

theorem siegelFun_add_one (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s (τ + 1) = cexp (π * I / 6) * ModularCurve.siegelFun N r (r + s) τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelFun_level_zero]
  rw [siegelFun_eq, siegelFun_eq, pref_add_one N hN, sprod_add_one, mul_assoc]

theorem norm_qq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qq τ‖ < 1 := by
  unfold qq
  rw [Complex.norm_exp]
  have : (2 * π * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

theorem qa_ne_zero (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s τ ≠ 0 := Complex.exp_ne_zero _

def P (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - qq τ ^ (n + 1))

theorem multipliable_P {τ : ℂ} (hτ : 0 < τ.im) : Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow (norm_qq_lt_one hτ)

theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k : ℕ) :
    Multipliable fun n : ℕ => 1 - q ^ (n + k) * c := by
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + k) * c)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_add]
    have := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right (‖q‖ ^ k * ‖c‖)
    refine this.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem multipliable_b {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ n * qa N r s τ := by
  simpa using multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 0

theorem multipliable_b_succ {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * qa N r s τ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ) 1

theorem multipliable_c {τ : ℂ} (hτ : 0 < τ.im) (N : ℕ) (r s : ℤ) :
    Multipliable fun n : ℕ => 1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹ :=
  multipliable_one_sub_pow_mul (norm_qq_lt_one hτ) (qa N r s τ)⁻¹ 1

def w (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + (1 - τ) / 2

theorem jtp_term (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℂ) (n : ℕ) :
    (1 - cexp (2 * π * I * (n + 1) * τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ)) *
      (1 + cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ)) =
      (1 - qq τ ^ (n + 1)) * ((1 - qq τ ^ n * qa N r s τ) *
        (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e1 : cexp (2 * π * I * (n + 1) * τ) = qq τ ^ (n + 1) := by
    rw [show 2 * π * I * (n + 1) * τ = ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) by push_cast; ring,
      Complex.exp_nat_mul, qq]
  have e2 : cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ) = -(qq τ ^ n * qa N r s τ) := by
    have : π * I * (2 * n + 1) * τ + 2 * π * I * w N r s τ =
        (n : ℂ) * (2 * π * I * τ) + 2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ) + π * I := by
      unfold w; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, qq, qa]
    ring
  have e3 : cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ) =
      -(qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := by
    have : π * I * (2 * n + 1) * τ - 2 * π * I * w N r s τ =
        ((n + 1 : ℕ) : ℂ) * (2 * π * I * τ) + -(2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ)) +
          -(π * I) := by
      unfold w; push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg,
      Complex.exp_neg, Complex.exp_pi_mul_I, qq, qa]
    ring
  rw [e1, e2, e3]; ring

theorem theta_eq (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (w N r s τ) τ = P τ * sprod N r s τ := by
  rw [jacobiTheta_two_eq_tprod _ _ hτ, tprod_congr (jtp_term N hN r s τ)]
  have hP := multipliable_P hτ
  have hb := multipliable_b hτ N r s
  have hb1 := multipliable_b_succ hτ N r s
  have hc := multipliable_c hτ N r s
  have hbc : Multipliable fun n : ℕ => (1 - qq τ ^ n * qa N r s τ) *
      (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹) := (hb.hasProd.mul hc.hasProd).multipliable
  have h3 : ∏' n : ℕ, (1 - qq τ ^ n * qa N r s τ) =
      (1 - qq τ ^ 0 * qa N r s τ) * ∏' n : ℕ, (1 - qq τ ^ (n + 1) * qa N r s τ) :=
    tprod_eq_zero_mul' hb1
  rw [hP.tprod_mul hbc, hb.tprod_mul hc, h3, pow_zero, one_mul, mul_assoc, ← hb1.tprod_mul hc]
  simp only [P, sprod]

theorem qParam_24 (τ : ℂ) : Function.Periodic.qParam 24 τ = cexp (π * I * τ / 12) := by
  unfold Function.Periodic.qParam
  congr 1
  push_cast
  ring

theorem one_sub_eta_q (n : ℕ) (τ : ℂ) : 1 - ModularForm.eta_q n τ = 1 - qq τ ^ (n + 1) := by
  simp only [ModularForm.eta_q, Function.Periodic.qParam, qq]
  congr 3
  push_cast
  ring

theorem eta_eq (τ : ℂ) : ModularForm.eta τ = cexp (π * I * τ / 12) * P τ := by
  unfold ModularForm.eta P
  rw [qParam_24, tprod_congr (fun n => one_sub_eta_q n τ)]

theorem P_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : P τ ≠ 0 := by
  have h := ModularForm.eta_tprod_ne_zero (z := τ) hτ
  rwa [tprod_congr (fun n => one_sub_eta_q n τ)] at h

theorem differentiable_w (N : ℕ) (r s : ℤ) : Differentiable ℂ (w N r s) := by
  unfold w; fun_prop

theorem differentiable_pref (N : ℕ) (r s : ℤ) : Differentiable ℂ (pref N r s) := by
  unfold pref; fun_prop

theorem differentiableAt_theta_w (N : ℕ) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (fun z => jacobiTheta₂ (w N r s z) z) τ := by
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (w N r s τ, τ) :=
    (hasFDerivAt_jacobiTheta₂ (w N r s τ) hτ).differentiableAt
  have h2 : DifferentiableAt ℂ (fun z => (w N r s z, z)) τ :=
    ((differentiable_w N r s) τ).prodMk differentiableAt_id
  have h3 : DifferentiableAt ℂ ((fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) ∘ (fun z => (w N r s z, z))) τ :=
    DifferentiableAt.comp (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f := fun z => (w N r s z, z)) τ h1 h2
  exact h3

theorem differentiableAt_P {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ P τ := by
  have h := ModularForm.differentiableAt_eta_tprod (z := τ) hτ
  have hfun : (fun x => ∏' n, (1 - ModularForm.eta_q n x)) = P := by
    funext x
    exact tprod_congr (fun n => one_sub_eta_q n x)
  rwa [hfun] at h

theorem siegelFun_eq_theta (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * (jacobiTheta₂ (w N r s τ) τ / P τ) := by
  rw [siegelFun_eq, theta_eq N hN r s hτ, mul_div_cancel_left₀ _ (P_ne_zero hτ)]

theorem differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) {z : ℂ | 0 < z.im} := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp only [siegelFun_level_zero]
    exact differentiableOn_const 0
  · have h : DifferentiableOn ℂ (fun z => pref N r s z * (jacobiTheta₂ (w N r s z) z / P z)) {z : ℂ | 0 < z.im} :=
      fun z hz => (((differentiable_pref N r s) z).mul
        ((differentiableAt_theta_w N r s hz).div (differentiableAt_P hz) (P_ne_zero hz))).differentiableWithinAt
    exact h.congr fun z hz => siegelFun_eq_theta N hN r s hz

theorem mdifferentiable_siegelFun (N : ℕ) (r s : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => ModularCurve.siegelFun N r s (τ : ℂ)) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have hd : DifferentiableAt ℂ (fun z : ℂ => ModularCurve.siegelFun N r s z) (τ : ℂ) :=
    (differentiableOn_siegelFun N r s).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp only [Function.comp_apply, id_eq] at hz
  simp only [Function.comp_apply, hz]

end E97cSHol

open scoped Manifold in
open ModularCurve in
theorem solution (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ)) :=
  ⟨E97cSHol.differentiableOn_siegelFun N r s, E97cSHol.mdifferentiable_siegelFun N r s⟩

end
end S_ModularCurve_SiegelUnit_differentiableOn_siegelFun
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun (solution)
