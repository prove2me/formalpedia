-- Prove2me | solution 1 for LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/54862e55-e0df-59b5-80fe-6d67078c9b8d

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv

set_option autoImplicit false

open MeasureTheory Set Real Complex Filter Topology

namespace GaussRodrigues

noncomputable def g (z : ℝ) : ℝ := Real.exp (-(Real.pi * z ^ 2))

noncomputable def Gc (s : ℝ) : ℂ := (Real.exp (-(Real.pi * s ^ 2)) : ℂ)

noncomputable def H (n : ℕ) (σ : ℝ) : ℂ := ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * (g z : ℂ)

theorem g_pos (z : ℝ) : 0 < g z := Real.exp_pos _

theorem pow_le_exp_half (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k ≤ (k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)) * Real.exp (Real.pi / 2 * x ^ 2) := by
  have h1 : x ^ k / (k.factorial : ℝ) ≤ Real.exp x := Real.pow_div_factorial_le_exp x hx k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hk] at h1; linarith
  have h3 : x ≤ 1 / (2 * Real.pi) + Real.pi / 2 * x ^ 2 := by
    have hπ := Real.pi_pos
    have : 0 ≤ (Real.pi * x - 1) ^ 2 := sq_nonneg _
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  calc x ^ k ≤ (k.factorial : ℝ) * Real.exp x := h2
    _ ≤ (k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi) + Real.pi / 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) hk.le
    _ = _ := by rw [Real.exp_add]; ring

theorem integrable_abs_pow_mul_g (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k * g z) := by
  have hb : Integrable (fun z : ℝ => Real.exp (-(Real.pi / 2) * z ^ 2)) := integrable_exp_neg_mul_sq (by positivity)
  refine Integrable.mono' (hb.const_mul ((k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)))) ?_ ?_
  · exact ((continuous_abs.pow k).mul (by unfold g; fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    have h := pow_le_exp_half k (abs_nonneg z)
    rw [sq_abs] at h
    have hg : 0 < g z := g_pos z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg z) k) hg.le)]
    unfold g
    have hE : Real.exp (Real.pi / 2 * z ^ 2) * Real.exp (-(Real.pi * z ^ 2)) = Real.exp (-(Real.pi / 2) * z ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |z| ^ k * Real.exp (-(Real.pi * z ^ 2))
        ≤ ((k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)) * Real.exp (Real.pi / 2 * z ^ 2)) * Real.exp (-(Real.pi * z ^ 2)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = (k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)) * Real.exp (-(Real.pi / 2) * z ^ 2) := by rw [← hE]; ring

theorem norm_sub_I_mul (σ z : ℝ) : ‖(σ : ℂ) - I * (z : ℂ)‖ ≤ |σ| + |z| := by
  calc ‖(σ : ℂ) - I * (z : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖I * (z : ℂ)‖ := norm_sub_le _ _
    _ = |σ| + |z| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

theorem add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) : (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h : a + b ≤ 2 * max a b := by
    rcases le_total a b with hab | hab
    · rw [max_eq_right hab]; linarith
    · rw [max_eq_left hab]; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by positivity) h n
    _ = 2 ^ n * (max a b) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total a b with hab | hab
        · rw [max_eq_right hab]; linarith [pow_nonneg ha n]
        · rw [max_eq_left hab]; linarith [pow_nonneg hb n]

theorem integrable_bound (A : ℝ) (hA : 0 ≤ A) (n j : ℕ) :
    Integrable (fun z : ℝ => 2 ^ n * (A ^ n + |z| ^ n) * |z| ^ j * g z) := by
  have h1 := (integrable_abs_pow_mul_g j).const_mul (2 ^ n * A ^ n)
  have h2 := (integrable_abs_pow_mul_g (n + j)).const_mul ((2 : ℝ) ^ n)
  refine (h1.add h2).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.add_apply, pow_add]
  ring

theorem norm_integrand_le (A : ℝ) {x : ℝ} (hx : |x| ≤ A) (z : ℝ) (n j : ℕ) :
    ‖((x : ℂ) - I * (z : ℂ)) ^ n * (z : ℂ) ^ j * (g z : ℂ)‖ ≤ 2 ^ n * (A ^ n + |z| ^ n) * |z| ^ j * g z := by
  have hA : 0 ≤ A := (abs_nonneg x).trans hx
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (g_pos z)]
  have h1 : ‖(x : ℂ) - I * (z : ℂ)‖ ^ n ≤ 2 ^ n * (A ^ n + |z| ^ n) := by
    calc ‖(x : ℂ) - I * (z : ℂ)‖ ^ n ≤ (|x| + |z|) ^ n := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_I_mul x z) n
      _ ≤ (A + |z|) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ 2 ^ n * (A ^ n + |z| ^ n) := add_pow_le A |z| hA (abs_nonneg z) n
  have := g_pos z
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) this.le

theorem continuous_integrand (x : ℝ) (n j : ℕ) :
    Continuous (fun z : ℝ => ((x : ℂ) - I * (z : ℂ)) ^ n * (z : ℂ) ^ j * (g z : ℂ)) := by
  unfold g; fun_prop

theorem integrable_integrand (x : ℝ) (n j : ℕ) :
    Integrable (fun z : ℝ => ((x : ℂ) - I * (z : ℂ)) ^ n * (z : ℂ) ^ j * (g z : ℂ)) :=
  Integrable.mono' (integrable_bound |x| (abs_nonneg x) n j) (continuous_integrand x n j).aestronglyMeasurable
    (ae_of_all _ fun z => norm_integrand_le |x| le_rfl z n j)

theorem integrable_integrand' (x : ℝ) (n : ℕ) :
    Integrable (fun z : ℝ => ((x : ℂ) - I * (z : ℂ)) ^ n * (g z : ℂ)) := by
  simpa using integrable_integrand x n 0

theorem H_zero (σ : ℝ) : H 0 σ = 1 := by
  unfold H g
  simp only [pow_zero, one_mul]
  rw [integral_complex_ofReal]
  have h := integral_gaussian Real.pi
  rw [div_self Real.pi_ne_zero, Real.sqrt_one] at h
  have : ∫ z : ℝ, Real.exp (-(Real.pi * z ^ 2)) = 1 := by simpa only [neg_mul] using h
  rw [this]; simp

theorem hasDerivAt_H (n : ℕ) (σ : ℝ) : HasDerivAt (H (n + 1)) ((n + 1 : ℕ) * H n σ) σ := by
  have hF_meas : ∀ᶠ (x : ℝ) in 𝓝 σ, AEStronglyMeasurable (fun z : ℝ => (((x : ℝ) : ℂ) - I * (z : ℂ)) ^ (n + 1) * (g z : ℂ)) volume :=
    Eventually.of_forall fun x => (integrable_integrand' x (n + 1)).aestronglyMeasurable
  have hF_int := integrable_integrand' σ (n + 1)
  have hF'_meas : AEStronglyMeasurable (fun z : ℝ => ((n + 1 : ℕ) : ℂ) * ((σ : ℂ) - I * (z : ℂ)) ^ n * (g z : ℂ)) volume := by
    refine Continuous.aestronglyMeasurable ?_; unfold g; fun_prop
  have hbound := (integrable_bound (|σ| + 1) (by positivity) n 0).const_mul ((n + 1 : ℕ) : ℝ)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := σ) (s := Metric.ball σ 1)
    (F := fun (x : ℝ) (z : ℝ) => (((x : ℝ) : ℂ) - I * (z : ℂ)) ^ (n + 1) * (g z : ℂ))
    (F' := fun (x : ℝ) (z : ℝ) => ((n + 1 : ℕ) : ℂ) * (((x : ℝ) : ℂ) - I * (z : ℂ)) ^ n * (g z : ℂ))
    (Metric.ball_mem_nhds σ one_pos) hF_meas hF_int hF'_meas ?_ hbound ?_
  · have heq : (∫ z : ℝ, ((n + 1 : ℕ) : ℂ) * ((σ : ℂ) - I * (z : ℂ)) ^ n * (g z : ℂ)) = (n + 1 : ℕ) * H n σ := by
      unfold H; rw [← integral_const_mul]; congr 1; funext z; ring
    rw [← heq]
    exact h.2
  · refine ae_of_all _ fun z x hx => ?_
    have hx' : |x| ≤ |σ| + 1 := by
      have := Metric.mem_ball.mp hx; rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub x σ; linarith
    have hb := norm_integrand_le (|σ| + 1) hx' z n 0
    simp only [pow_zero, mul_one] at hb
    rw [norm_mul, norm_mul] at *
    rw [Complex.norm_natCast]
    calc ((n + 1 : ℕ) : ℝ) * ‖((x : ℂ) - I * (z : ℂ)) ^ n‖ * ‖(g z : ℂ)‖
        ≤ ((n + 1 : ℕ) : ℝ) * (2 ^ n * ((|σ| + 1) ^ n + |z| ^ n) * g z) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · refine ae_of_all _ fun z (x : ℝ) _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => ((y : ℂ) - I * (z : ℂ))) 1 x := by
      have := (hasDerivAt_id (x : ℂ)).comp_ofReal
      simpa using (this.sub_const (I * (z : ℂ)))
    have h2 := (h1.pow (n + 1)).mul_const ((g z : ℂ))
    convert h2 using 1 <;> first | rfl | (push_cast; ring1)

end GaussRodrigues

namespace GaussRodrigues

theorem tendsto_abs_pow_mul_g (k : ℕ) : Tendsto (fun z : ℝ => |z| ^ k * g z) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact Real.pi_pos (k : ℝ)
  refine h.congr' (Eventually.of_forall fun z => ?_)
  rw [Real.rpow_natCast]
  unfold g
  rw [neg_mul]

theorem tendsto_uv (σ : ℝ) (n : ℕ) (l : Filter ℝ) (hl : l ≤ cocompact ℝ) :
    Tendsto (fun z : ℝ => ((σ : ℂ) - I * (z : ℂ)) ^ n * ((-(1 / (2 * Real.pi)) : ℂ) * (g z : ℂ))) l (𝓝 0) := by
  have h0 : Tendsto (fun z : ℝ => |z| ^ 0 * g z) l (𝓝 0) := (tendsto_abs_pow_mul_g 0).mono_left hl
  have hn : Tendsto (fun z : ℝ => |z| ^ n * g z) l (𝓝 0) := (tendsto_abs_pow_mul_g n).mono_left hl
  have hsum : Tendsto (fun z : ℝ => (1 / (2 * Real.pi)) * (2 ^ n * (|σ| ^ n * (|z| ^ 0 * g z) + |z| ^ n * g z))) l (𝓝 0) := by
    have := ((h0.const_mul (|σ| ^ n)).add hn).const_mul ((2 : ℝ) ^ n) |>.const_mul (1 / (2 * Real.pi))
    simpa using this
  refine squeeze_zero_norm (fun z => ?_) hsum
  have hb := norm_integrand_le |σ| le_rfl z n 0
  simp only [pow_zero, mul_one] at hb
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (g_pos z)] at *
  have hc : ‖((-(1 / (2 * Real.pi)) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [show ((-(1 / (2 * Real.pi)) : ℂ)) = (((-(1 / (2 * Real.pi))) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  rw [hc]
  have hg := g_pos z
  calc ‖((σ : ℂ) - I * (z : ℂ)) ^ n‖ * (1 / (2 * Real.pi) * g z)
      = 1 / (2 * Real.pi) * (‖((σ : ℂ) - I * (z : ℂ)) ^ n‖ * g z) := by ring
    _ ≤ 1 / (2 * Real.pi) * (2 ^ n * (|σ| ^ n + |z| ^ n) * g z) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / (2 * Real.pi) * (2 ^ n * (|σ| ^ n * (1 * g z) + |z| ^ n * g z)) := by ring

theorem hasDerivAt_g (z : ℝ) : HasDerivAt g (-(2 * Real.pi * z) * g z) z := by
  have h := (((hasDerivAt_pow 2 z).const_mul Real.pi).neg).exp
  unfold g
  convert h using 1 <;> first | rfl | (simp only [Pi.neg_apply]; push_cast; ring1)

theorem ibp (n : ℕ) (σ : ℝ) :
    ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * (z : ℂ) * (g z : ℂ) =
      -(I * n / (2 * Real.pi)) * ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ (n - 1) * (g z : ℂ) := by
  set u : ℝ → ℂ := fun z => ((σ : ℂ) - I * (z : ℂ)) ^ n with hu
  set u' : ℝ → ℂ := fun z => (n : ℂ) * ((σ : ℂ) - I * (z : ℂ)) ^ (n - 1) * (-I) with hu'
  set v : ℝ → ℂ := fun z => ((-(1 / (2 * Real.pi)) : ℂ) * (g z : ℂ)) with hv
  set v' : ℝ → ℂ := fun z => (z : ℂ) * (g z : ℂ) with hv'
  have hdu : ∀ z : ℝ, HasDerivAt u (u' z) z := by
    intro z
    have h1 : HasDerivAt (fun y : ℝ => I * (y : ℂ)) I z := by
      simpa using ((hasDerivAt_id (z : ℂ)).comp_ofReal).const_mul I
    have h2 : HasDerivAt (fun y : ℝ => (σ : ℂ) - I * (y : ℂ)) (-I) z := h1.const_sub (σ : ℂ)
    have h3 := h2.pow n
    simp only [hu, hu']
    convert h3 using 1
    rfl
    rfl
  have hdv : ∀ z : ℝ, HasDerivAt v (v' z) z := by
    intro z
    have h := ((hasDerivAt_g z).ofReal_comp).const_mul ((-(1 / (2 * Real.pi)) : ℂ))
    simp only [hv, hv']
    convert h using 1 <;> first | rfl | (push_cast; field_simp) | (push_cast; ring1)
  have huv' : Integrable (u * v') := by
    have := integrable_integrand σ n 1
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [hu, hv', Pi.mul_apply, pow_one]; ring
  have hu'v : Integrable (u' * v) := by
    have := (integrable_integrand' σ (n - 1)).const_mul ((n : ℂ) * (-I) * ((-(1 / (2 * Real.pi))) : ℂ))
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [hu', hv, Pi.mul_apply]; ring
  have hbot : Tendsto (u * v) atBot (𝓝 0) := by
    have := tendsto_uv σ n atBot (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left)
    simp only [hu, hv] at this ⊢
    exact this
  have htop : Tendsto (u * v) atTop (𝓝 0) := by
    have := tendsto_uv σ n atTop (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
    simp only [hu, hv] at this ⊢
    exact this
  have h := integral_mul_deriv_eq_deriv_mul (fun z _ => hdu z) (fun z _ => hdv z) huv' hu'v hbot htop
  simp only [hu, hu', hv, hv', sub_zero] at h
  have lhs : (∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * (z : ℂ) * (g z : ℂ)) =
      ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * ((z : ℂ) * (g z : ℂ)) := by
    congr 1; funext z; ring
  rw [lhs, h, zero_sub, ← integral_neg, ← integral_const_mul]
  congr 1; funext z
  ring

theorem H_succ_succ (n : ℕ) (σ : ℝ) :
    H (n + 2) σ = (σ : ℂ) * H (n + 1) σ - ((n + 1 : ℕ) / (2 * Real.pi) : ℂ) * H n σ := by
  have h1 := integrable_integrand' σ (n + 1)
  have h2 : Integrable (fun z : ℝ => ((σ : ℂ) - I * (z : ℂ)) ^ (n + 1) * (z : ℂ) * (g z : ℂ)) := by
    have := integrable_integrand σ (n + 1) 1; simpa [pow_one] using this
  have hexp : H (n + 2) σ = (σ : ℂ) * (∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ (n + 1) * (g z : ℂ)) -
      I * (∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ (n + 1) * (z : ℂ) * (g z : ℂ)) := by
    unfold H
    rw [← integral_const_mul (σ : ℂ), ← integral_const_mul I, ← integral_sub (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext z; ring
  rw [hexp, ibp (n + 1) σ]
  unfold H
  simp only [Nat.add_sub_cancel]
  have hI : I * I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (↑n + 1) / (2 * ↑Real.pi) * (∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * (g z : ℂ)) * hI

theorem H_one (σ : ℝ) : H 1 σ = (σ : ℂ) := by
  have h1 : Integrable (fun z : ℝ => (g z : ℂ)) := by simpa using integrable_integrand' σ 0
  have h2 : Integrable (fun z : ℝ => (z : ℂ) * (g z : ℂ)) := by simpa using integrable_integrand σ 0 1
  have hexp : H 1 σ = (σ : ℂ) * (∫ z : ℝ, (g z : ℂ)) - I * (∫ z : ℝ, (z : ℂ) * (g z : ℂ)) := by
    unfold H
    rw [← integral_const_mul (σ : ℂ), ← integral_const_mul I, ← integral_sub (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext z; ring
  have hodd : (∫ z : ℝ, (z : ℂ) * (g z : ℂ)) = 0 := by
    have := ibp 0 σ
    simpa using this
  have h0 : (∫ z : ℝ, (g z : ℂ)) = 1 := by
    have := H_zero σ; unfold H at this; simpa using this
  rw [hexp, hodd, h0]
  ring

theorem hasDerivAt_Gc (s : ℝ) : HasDerivAt Gc ((-(2 * Real.pi * s) * g s : ℝ) : ℂ) s := by
  have h := (hasDerivAt_g s).ofReal_comp
  exact h

theorem Gc_eq (s : ℝ) : Gc s = (g s : ℂ) := rfl

theorem key (n : ℕ) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => Gc s * H n s) (-(2 * (Real.pi : ℂ)) * (Gc σ * H (n + 1) σ)) σ := by
  rcases n with _ | k
  · have hH : (fun s : ℝ => Gc s * H 0 s) = Gc := by funext s; rw [H_zero, mul_one]
    rw [hH, H_one]
    have h := hasDerivAt_Gc σ
    convert h using 1 <;> first | rfl | (rw [Gc_eq]; push_cast; ring1)
  · have h := (hasDerivAt_Gc σ).mul (hasDerivAt_H k σ)
    convert h using 1 <;> first | rfl | (rw [H_succ_succ k σ, Gc_eq]; push_cast; field_simp; ring1) | (simp only [Pi.mul_apply]; rw [H_succ_succ k σ, Gc_eq]; push_cast; field_simp; ring1)

noncomputable def c : ℂ := (-(2 * (Real.pi : ℂ)))⁻¹

theorem c_ne_zero : c ≠ 0 := by
  unfold c; exact inv_ne_zero (neg_ne_zero.mpr (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))

theorem c_mul : c * (-(2 * (Real.pi : ℂ))) = 1 := by
  unfold c; exact inv_mul_cancel₀ (neg_ne_zero.mpr (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))

theorem main_eq (n : ℕ) : ∀ s : ℝ, Gc s * H n s = c ^ n * iteratedDeriv n Gc s := by
  induction n with
  | zero => intro s; rw [H_zero, iteratedDeriv_zero, pow_zero, mul_one, one_mul]
  | succ n ih =>
    intro s
    have hcn : c ^ n ≠ 0 := pow_ne_zero _ c_ne_zero
    have hfun : iteratedDeriv n Gc = fun s => (c ^ n)⁻¹ * (Gc s * H n s) := by
      funext t; rw [ih t, ← mul_assoc, inv_mul_cancel₀ hcn, one_mul]
    rw [iteratedDeriv_succ, hfun, ((key n s).const_mul ((c ^ n)⁻¹)).deriv, pow_succ]
    have e : ∀ X : ℂ, c ^ n * c * ((c ^ n)⁻¹ * (-(2 * (Real.pi : ℂ)) * X)) = X := fun X => by
      rw [show c ^ n * c * ((c ^ n)⁻¹ * (-(2 * (Real.pi : ℂ)) * X)) = (c ^ n * (c ^ n)⁻¹) * (c * -(2 * (Real.pi : ℂ))) * X by ring,
        mul_inv_cancel₀ hcn, c_mul]
      ring
    exact (e _).symm

end GaussRodrigues

open GaussRodrigues in
theorem solution (n : ℕ) (σ : ℝ) :
    (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) *
        ∫ z : ℝ, ((σ : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) =
      (-(2 * (Real.pi : ℂ)))⁻¹ ^ n * iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ :=
  main_eq n σ

end S_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
end P2MW
export P2MW.S_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv (solution)
