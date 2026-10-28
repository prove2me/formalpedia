-- Prove2me | solution 1 for HighResODE.NAGSC.eq_3_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:28:51.940405+00:00
-- url     : https://prove2.me/submissions/207afcd6-c4fd-4c9a-9643-3ba20e9eadb1

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

open scoped InnerProductSpace

namespace Aux_HR_eq37

open HighResODE.NAGSC

lemma descent {n : ℕ} (f : E n → ℝ) (hf : Differentiable ℝ f) (L : ℝ)
    (hS : ∀ x y : E n, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x z : E n) :
    f z ≤ f x + ⟪gradient f x, z - x⟫_ℝ + L / 2 * ‖z - x‖ ^ 2 := by
  set v := z - x with hv
  set c := ⟪gradient f x, v⟫_ℝ with hc
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * c - L / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • v), v⟫_ℝ - c - L * t * ‖v‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hfd : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) := (hf _).hasFDerivAt
    have h1 := hfd.comp_hasDerivAt t hline
    have hg : fderiv ℝ f (x + t • v) v = ⟪gradient f (x + t • v), v⟫_ℝ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [hg] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hL := hS (x + t • v) x
      have hn : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hi : ⟪gradient f (x + t • v), v⟫_ℝ - c ≤
          ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := by
        rw [hc, ← inner_sub_left]
        exact real_inner_le_norm _ _
      rw [hn] at hL
      nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hL (norm_nonneg v)]
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1 : ℝ) • v = z := by rw [one_smul, hv, add_sub_cancel]
  have e0 : x + (0 : ℝ) • v = x := by rw [zero_smul, add_zero]
  simp only [ψ, e1, e0] at h
  norm_num at h
  linarith

end Aux_HR_eq37

open HighResODE.NAGSC in
theorem solution {n : ℕ} (f : E n → ℝ) (μ L : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ (1 / (4 * L)) x y) :
    ∀ k : ℕ, f (x k) - f xs ≤
      4 * (1 - Real.sqrt (μ / (4 * L))) / (3 + 4 * Real.sqrt (μ / (4 * L))) *
        lyap f μ (1 / (4 * L)) xs x k := by
  intro k
  have hL := hf.isF1.L_pos
  have hμ := hf.mu_pos
  have hμL := hf.mu_le_L
  set r := Real.sqrt (μ / (4 * L)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = μ / (4 * L) := Real.sq_sqrt (by positivity)
  have hrhalf : r ≤ 1 / 2 := by
    have : μ / (4 * L) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  have h1r : 0 < 1 - r := by linarith
  set Δ := f (x k) - f xs with hΔ
  set G := ‖gradient f (x k)‖ ^ 2 with hG
  have hΔ0 : 0 ≤ Δ := by linarith [hmin (x k)]
  -- descent: G ≤ 2 L Δ
  have hGΔ : G ≤ 2 * L * Δ := by
    have hd := Aux_HR_eq37.descent f hf.isF1.differentiable L hf.isF1.lipschitz_gradient (x k)
      (x k - (1 / L) • gradient f (x k))
    have e1 : x k - (1 / L) • gradient f (x k) - x k = -((1 / L) • gradient f (x k)) := by abel
    rw [e1, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
      norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)] at hd
    have := hmin (x k - (1 / L) • gradient f (x k))
    have e2 : L / 2 * ((1 / L) ^ 2 * ‖gradient f (x k)‖ ^ 2) = G / (2 * L) := by
      rw [hG]; field_simp
    have e3 : 1 / L * ‖gradient f (x k)‖ ^ 2 = G / L := by rw [hG]; ring
    rw [e2, e3] at hd
    have : G / (2 * L) ≤ Δ := by
      have : G / L - G / (2 * L) = G / (2 * L) := by field_simp; ring
      linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  -- lower bound on lyap
  have hmu : μ * (1 / (4 * L)) = μ / (4 * L) := by ring
  have hlow : (1 + r) / (1 - r) * Δ - 1 / (4 * L) * G / (2 * (1 - r)) ≤
      lyap f μ (1 / (4 * L)) xs x k := by
    unfold lyap
    rw [hmu, ← hr, ← hΔ, ← hG]
    have hb1 : 0 ≤ 1 / 4 * ‖vel (1 / (4 * L)) x k‖ ^ 2 := by positivity
    have hb2 : 0 ≤ 1 / 4 * ‖vel (1 / (4 * L)) x k +
        (2 * Real.sqrt μ / (1 - r)) • (x (k + 1) - xs) +
        Real.sqrt (1 / (4 * L)) • gradient f (x k)‖ ^ 2 := by positivity
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlow h1r.le
  have eA : (1 - r) * ((1 + r) / (1 - r) * Δ - 1 / (4 * L) * G / (2 * (1 - r))) =
      (1 + r) * Δ - G / (8 * L) := by
    field_simp
    ring
  rw [eA] at hmul
  have hG8 : G / (8 * L) ≤ Δ / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hpos : 0 < 3 + 4 * r := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith
