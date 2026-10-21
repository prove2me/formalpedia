-- Prove2me | solution 1 for NesterovODE.Rate.bound_chain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:38:39.922577+00:00
-- url     : https://prove2.me/submissions/d396153d-81dc-4f86-997b-0c89f2756d7e

import Mathlib
import Definitions.Def_NesterovODE_Rate_Setting

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

namespace NesterovODE.Rate
open scoped InnerProductSpace

theorem Hlp_energy_aux {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n))
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V)
    (t : ℝ) (ht : 0 < t) (A : EuclideanSpace ℝ (Fin n)) (hA : HasDerivAt V A t) :
    HasDerivAt (energy f xstar X V)
      (2 * t * (f (X t) - f xstar) + t ^ 2 * inner ℝ (gradient f (X t)) (V t)
        + 4 * inner ℝ (X t + (t / 2) • V t - xstar) ((3 / 2 : ℝ) • V t + (t / 2) • A)) t := by
  obtain ⟨_, _, _, _, h⟩ := hX
  obtain ⟨hXd, _⟩ := h t ht
  obtain ⟨L, _, _, hC1, _⟩ := hf
  have hfd : DifferentiableAt ℝ f (X t) := (hC1.differentiable one_ne_zero) _
  have h1 : HasDerivAt (fun s => f (X s)) (inner ℝ (gradient f (X t)) (V t)) t := by
    rw [Hlp.inner_grad_eq]
    exact hfd.hasFDerivAt.comp_hasDerivAt t hXd
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * (f (X s) - f xstar))
      (2 * t * (f (X t) - f xstar) + t ^ 2 * inner ℝ (gradient f (X t)) (V t)) t := by
    have := (hasDerivAt_pow 2 t).mul (h1.sub_const (f xstar))
    refine this.congr_deriv ?_
    norm_num <;> ring
  have h3 : HasDerivAt (fun s : ℝ => X s + (s / 2) • V s - xstar)
      (V t + ((t / 2) • A + (1 / 2 : ℝ) • V t)) t := by
    have h5 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const 2
    exact (hXd.add (h5.smul hA)).sub_const xstar
  have h4 := h3.norm_sq
  have e : V t + ((t / 2) • A + (1 / 2 : ℝ) • V t) = (3 / 2 : ℝ) • V t + (t / 2) • A := by module
  rw [e] at h4
  have := h2.add (h4.const_mul 2)
  refine this.congr_deriv ?_
  ring

theorem Hlp_energy_nonpos {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (energy f xstar X V)
        (2 * t * (f (X t) - f xstar)
          + 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t))) t ∧
      2 * t * (f (X t) - f xstar) + 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t))
        = 2 * t * (f (X t) - f xstar) - 2 * t * inner ℝ (X t - xstar) (gradient f (X t)) ∧
      2 * t * (f (X t) - f xstar) - 2 * t * inner ℝ (X t - xstar) (gradient f (X t)) ≤ 0 := by
  have hX' := hX
  obtain ⟨_, _, _, _, h⟩ := hX'
  obtain ⟨hXd, hVd⟩ := h t ht
  have hA := Hlp_energy_aux f hf x₀ xstar X V hX t ht _ hVd
  have e1 : (3 / 2 : ℝ) • V t + (t / 2) • (-(3 / t) • V t - gradient f (X t))
      = -(t / 2) • gradient f (X t) := by
    have : (t / 2) * (3 / t) = 3 / 2 := by field_simp
    rw [smul_sub, smul_smul, mul_neg, this]
    module
  rw [e1] at hA
  have e2 : t ^ 2 * inner ℝ (gradient f (X t)) (V t)
        + 4 * inner ℝ (X t + (t / 2) • V t - xstar) (-(t / 2) • gradient f (X t))
      = 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t)) := by
    have : X t + (t / 2) • V t - xstar = (X t - xstar) + (t / 2) • V t := by abel
    rw [this, inner_add_left]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_neg_right, real_inner_comm (V t)]
    ring
  have hD : HasDerivAt (energy f xstar X V)
      (2 * t * (f (X t) - f xstar)
          + 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t))) t := by
    refine hA.congr_deriv ?_
    rw [add_assoc, e2]
  have e3 : 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t))
      = - 2 * t * inner ℝ (X t - xstar) (gradient f (X t)) := by
    rw [real_inner_smul_right]; ring
  refine ⟨hD, ?_, ?_⟩
  · rw [e3]; ring
  · obtain ⟨L, _, hconv, hC1, _⟩ := hf
    have hd : ∀ x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))), DifferentiableAt ℝ f x :=
      fun x _ => (hC1.differentiable one_ne_zero) x
    have hc := Hlp.convex_ineq hconv hd (Set.mem_univ (X t)) (Set.mem_univ xstar)
    have hm := hxstar (X t)
    have e4 : inner ℝ (gradient f (X t)) (xstar - X t) = - inner ℝ (X t - xstar) (gradient f (X t)) := by
      rw [real_inner_comm, ← inner_neg_left, neg_sub]
    rw [e4] at hc
    nlinarith

end NesterovODE.Rate

open NesterovODE.Rate
open scoped InnerProductSpace

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V) :
    AntitoneOn (energy f xstar X V) (Set.Ici 0) ∧
      ∀ t : ℝ, 0 < t →
        f (X t) - f xstar ≤ energy f xstar X V t / t ^ 2 ∧
        energy f xstar X V t / t ^ 2 ≤ energy f xstar X V 0 / t ^ 2 ∧
        energy f xstar X V 0 / t ^ 2 = 2 * ‖x₀ - xstar‖ ^ 2 / t ^ 2 := by
  obtain ⟨hX0, hV0, hXw, hVc, hode⟩ := hX
  have hX' : IsSolution f 3 x₀ X V := ⟨hX0, hV0, hXw, hVc, hode⟩
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt (energy f xstar X V) _ t := fun t ht =>
    (Hlp_energy_nonpos f hf x₀ xstar hxstar X V hX' t ht).1
  have hnp : ∀ t : ℝ, 0 < t → 2 * t * (f (X t) - f xstar)
      + 4 * inner ℝ (X t - xstar) (-(t / 2) • gradient f (X t)) ≤ 0 := fun t ht => by
    obtain ⟨_, h2, h3⟩ := Hlp_energy_nonpos f hf x₀ xstar hxstar X V hX' t ht
    rw [h2]; exact h3
  have hanti : AntitoneOn (energy f xstar X V) (Set.Ici 0) := by
    obtain ⟨L, _, _, hC1, _⟩ := hf
    have hfc : Continuous f := hC1.continuous
    have hXc : ContinuousWithinAt X (Set.Ici 0) 0 := hXw.continuousWithinAt
    have hc0 : ContinuousWithinAt (energy f xstar X V) (Set.Ici 0) 0 := by
      unfold energy
      have h1 : ContinuousWithinAt (fun t : ℝ => f (X t)) (Set.Ici 0) 0 :=
        hfc.continuousAt.comp_continuousWithinAt hXc
      have h2 : ContinuousWithinAt (fun t : ℝ => X t + (t / 2) • V t - xstar) (Set.Ici 0) 0 :=
        (hXc.add ((continuous_id.div_const 2).continuousWithinAt.smul hVc)).sub_const xstar
      exact ((continuous_pow 2).continuousWithinAt.mul (h1.sub_const _)).add
        ((continuousWithinAt_const.mul (continuous_norm.continuousWithinAt.comp h2 (Set.mapsTo_univ _ _)
          |>.pow 2)))
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      rcases (Set.mem_Ici.1 ht).eq_or_lt with h | h
      · subst h; exact hc0
      · exact (hder t h).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hder t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t ht).deriv]
      exact hnp t ht
  refine ⟨hanti, fun t ht => ?_⟩
  have hE0 : energy f xstar X V 0 = 2 * ‖x₀ - xstar‖ ^ 2 := by
    simp [energy, hX0, hV0]
  have ht2 : 0 < t ^ 2 := pow_pos ht 2
  refine ⟨?_, ?_, by rw [hE0]⟩
  · rw [le_div_iff₀ ht2]
    unfold energy
    nlinarith [sq_nonneg ‖X t + (t / 2) • V t - xstar‖]
  · exact div_le_div_of_nonneg_right (hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht.le) ht2.le
