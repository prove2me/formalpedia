-- Prove2me | solution 1 for NecoaraNG.Compose.lipschitz_grad
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:50:22.133002+00:00
-- url     : https://prove2.me/submissions/bbe4f245-1873-4532-9252-11db1d90180f

import Mathlib
import Definitions.Def_NecoaraNG_Compose_Setting

set_option autoImplicit false

section HlpSec
open scoped InnerProductSpace
open Filter Topology

namespace Hlp
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

end Hlp
end HlpSec

open scoped InnerProductSpace
open NecoaraNG.Compose

theorem solution {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p) (d : NecoaraNG.Chain.E p)
    (g : NecoaraNG.Chain.E m → ℝ) (hgdiff : ∀ u, DifferentiableAt ℝ g u) (Lg : ℝ)
    (hLg : ∀ u v, ‖gradient g u - gradient g v‖ ≤ Lg * ‖u - v‖) :
    LipGradOn (polyhedron C d) (fun x => g (A x)) (Lg * ‖A‖ ^ 2) := by
  intro x _ y _
  have hgrad : ∀ z : NecoaraNG.Chain.E n, gradient (fun x => g (A x)) z
      = (ContinuousLinearMap.adjoint A) (gradient g (A z)) := by
    intro z
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [Hlp.inner_grad_eq, Hlp.inner_grad_eq]
    have h := ((hgdiff (A z)).hasFDerivAt.comp z A.hasFDerivAt).fderiv
    have h' : fderiv ℝ (fun x => g (A x)) z = (fderiv ℝ g (A z)).comp A := h
    rw [h']
    rfl
  rw [hgrad x, hgrad y, ← map_sub]
  have h1 : ‖(ContinuousLinearMap.adjoint A) (gradient g (A x) - gradient g (A y))‖
      ≤ ‖A‖ * ‖gradient g (A x) - gradient g (A y)‖ := by
    have := (ContinuousLinearMap.adjoint A).le_opNorm (gradient g (A x) - gradient g (A y))
    rwa [LinearIsometryEquiv.norm_map] at this
  have h2 := hLg (A x) (A y)
  have h3 : ‖A x - A y‖ ≤ ‖A‖ * ‖x - y‖ := by
    rw [← map_sub]; exact A.le_opNorm _
  by_cases hL : 0 ≤ Lg
  · calc _ ≤ ‖A‖ * ‖gradient g (A x) - gradient g (A y)‖ := h1
      _ ≤ ‖A‖ * (Lg * ‖A x - A y‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ ‖A‖ * (Lg * (‖A‖ * ‖x - y‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hL) (norm_nonneg _)
      _ = Lg * ‖A‖ ^ 2 * ‖x - y‖ := by ring
  · push Not at hL
    have hzero : ∀ u : NecoaraNG.Chain.E m, u = 0 := by
      intro u
      by_contra hu
      have h := hLg u 0
      have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
      rw [sub_zero] at h
      nlinarith [norm_nonneg (gradient g u - gradient g 0)]
    have hA0 : A = 0 := by
      ext v i
      have := hzero (A v)
      simp [this]
    have hn : ‖A‖ = 0 := by rw [hA0]; simp
    rw [hn] at h1 ⊢
    simp at h1 ⊢
    exact h1
