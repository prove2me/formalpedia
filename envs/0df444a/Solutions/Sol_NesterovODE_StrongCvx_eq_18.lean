-- Prove2me | solution 1 for NesterovODE.StrongCvx.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:44:07.881377+00:00
-- url     : https://prove2.me/submissions/750276d9-b97f-4a7d-b4a0-8caade3faebb

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

set_option autoImplicit false

section HlpSec
open scoped InnerProductSpace
open Filter Topology

namespace HlpNOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem inner_grad_eq (f : H → ℝ) (p v : H) : ⟪gradient f p, v⟫_ℝ = fderiv ℝ f p v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem line_hasDeriv {f : H → ℝ} {p : H} (hp : DifferentiableAt ℝ f p) (x v : H) (t : ℝ)
    (hpt : x + t • v = p) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (⟪gradient f p, v⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  rw [inner_grad_eq]
  subst hpt
  exact hp.hasFDerivAt.comp_hasDerivAt t h1

theorem convex_ineq {X : Set H} {f : H → ℝ} (hf : ConvexOn ℝ X f)
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have h1 := line_hasDeriv (hd x hx) x (y - x) 0 (by simp)
  have h2 := h1.tendsto_slope_zero_right
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • ((fun s : ℝ => f (x + s • (y - x))) (0 + t) - (fun s : ℝ => f (x + s • (y - x))) 0)
        ≤ f y - f x := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have hc := hf.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring : (1 - t) + t = 1)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [e] at hc
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at hc ⊢
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto h2 h3
  linarith

end HlpNOS
end HlpSec

open scoped InnerProductSpace

theorem energy5_deriv {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (L : NNReal)
    (r : ℝ) (x₀ xstar : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n)
    (hf : NesterovODE.StrongCvx.InFL L f) (hr : 1 < r)
    (hX : NesterovODE.StrongCvx.IsSolution f r x₀ X V)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => NesterovODE.StrongCvx.energy5 f r xstar X V u)
      (4 * t / (r - 1) * (f (X t) - f xstar) -
        2 * t * inner ℝ (X t - xstar) (gradient f (X t))) t := by
  obtain ⟨_, _, _, _, h⟩ := hX
  obtain ⟨hXd, hVd⟩ := h t ht
  obtain ⟨_, _, hC1, _⟩ := hf
  have hr1 : r - 1 ≠ 0 := by linarith
  have ht0 : t ≠ 0 := ht.ne'
  have hfd : DifferentiableAt ℝ f (X t) := (hC1.differentiable one_ne_zero) _
  have h1 : HasDerivAt (fun s => f (X s)) (inner ℝ (gradient f (X t)) (V t)) t := by
    rw [HlpNOS.inner_grad_eq]
    exact hfd.hasFDerivAt.comp_hasDerivAt t hXd
  have h2 : HasDerivAt (fun s : ℝ => 2 * s ^ 2 / (r - 1) * (f (X s) - f xstar))
      (4 * t / (r - 1) * (f (X t) - f xstar)
        + 2 * t ^ 2 / (r - 1) * inner ℝ (gradient f (X t)) (V t)) t := by
    have := (((hasDerivAt_pow 2 t).const_mul 2).div_const (r - 1)).mul (h1.sub_const (f xstar))
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    ring
  have h3 : HasDerivAt (fun s : ℝ => X s + (s / (r - 1)) • V s - xstar)
      (V t + ((t / (r - 1)) • (-(r / t) • V t - gradient f (X t)) + (1 / (r - 1)) • V t)) t := by
    have h5 : HasDerivAt (fun s : ℝ => s / (r - 1)) (1 / (r - 1)) t := by
      simpa using (hasDerivAt_id t).div_const (r - 1)
    have := (hXd.add (h5.smul hVd)).sub_const xstar
    exact this
  have hZ : V t + ((t / (r - 1)) • (-(r / t) • V t - gradient f (X t)) + (1 / (r - 1)) • V t)
      = -(t / (r - 1)) • gradient f (X t) := by
    match_scalars <;> field_simp <;> ring
  rw [hZ] at h3
  have h4 := h3.norm_sq
  have h6 := h2.add (h4.const_mul (r - 1))
  refine h6.congr_deriv ?_
  have e1 : X t + (t / (r - 1)) • V t - xstar = (X t - xstar) + (t / (r - 1)) • V t := by abel
  rw [e1, inner_add_left]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_neg_right,
    real_inner_comm (V t)]
  field_simp
  ring

theorem solution (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (L : NNReal) (r : ℝ)
    (x₀ xstar : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n)
    (hL : 0 < L) (hf : NesterovODE.StrongCvx.InFL L f) (hr : 1 < r)
    (hmin : ∀ y, f xstar ≤ f y)
    (hX : NesterovODE.StrongCvx.IsSolution f r x₀ X V)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => NesterovODE.StrongCvx.energy5 f r xstar X V u)
      (4 * t / (r - 1) * (f (X t) - f xstar) -
        2 * t * inner ℝ (X t - xstar) (gradient f (X t))) t ∧
      4 * t / (r - 1) * (f (X t) - f xstar) -
        2 * t * inner ℝ (X t - xstar) (gradient f (X t)) ≤
        -(2 * (r - 3) * t / (r - 1)) * (f (X t) - f xstar) := by
  refine ⟨energy5_deriv f L r x₀ xstar X V hf hr hX t ht, ?_⟩
  obtain ⟨_, hconv, hC1, _⟩ := hf
  have hd : ∀ x ∈ (Set.univ : Set (NesterovODE.WellPosed.E n)), DifferentiableAt ℝ f x :=
    fun x _ => (hC1.differentiable one_ne_zero) x
  have hc := HlpNOS.convex_ineq hconv hd (Set.mem_univ (X t)) (Set.mem_univ xstar)
  have e4 : inner ℝ (gradient f (X t)) (xstar - X t)
      = - inner ℝ (X t - xstar) (gradient f (X t)) := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  rw [e4] at hc
  have hr1 : 0 < r - 1 := by linarith
  have e5 : -(2 * (r - 3) * t / (r - 1)) * (f (X t) - f xstar)
      = 4 * t / (r - 1) * (f (X t) - f xstar) - 2 * t * (f (X t) - f xstar) := by
    field_simp
    ring
  rw [e5]
  nlinarith
