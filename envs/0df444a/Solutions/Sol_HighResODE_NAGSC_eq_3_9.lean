-- Prove2me | solution 1 for HighResODE.NAGSC.eq_3_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:34:22.657774+00:00
-- url     : https://prove2.me/submissions/ba247a4c-ec63-4965-a673-d862920a87fa

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

open scoped InnerProductSpace

namespace Aux_HR_eq39

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

lemma scal1 (s r : ℝ) (hr : 0 ≤ r) : s + (1 - r) / (1 + r) * s = 2 * s / (1 + r) := by
  have : 0 < 1 + r := by linarith
  field_simp
  ring

end Aux_HR_eq39

open HighResODE.NAGSC in
theorem solution {n : ℕ} (f : E n → ℝ) (μ L s : ℝ) (hf : IsS1 f μ L) (xs : E n)
    (hmin : ∀ z : E n, f xs ≤ f z) (x y : ℕ → E n) (hrun : IsNAGSC f μ s x y)
    (hs : 0 < s) (hμs : μ * s < 1) :
    lyap f μ s xs x 0 ≤
        (1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)) * (f (x 0) - f xs)
          + s / (1 + Real.sqrt (μ * s)) ^ 2 * ‖gradient f (x 0)‖ ^ 2
          + 1 / 4 * ‖(2 * Real.sqrt μ / (1 - Real.sqrt (μ * s))) • (x 0 - xs)
              - ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) •
                  (Real.sqrt s • gradient f (x 0))‖ ^ 2 ∧
      (1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)) * (f (x 0) - f xs)
          + s / (1 + Real.sqrt (μ * s)) ^ 2 * ‖gradient f (x 0)‖ ^ 2
          + 1 / 4 * ‖(2 * Real.sqrt μ / (1 - Real.sqrt (μ * s))) • (x 0 - xs)
              - ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) •
                  (Real.sqrt s • gradient f (x 0))‖ ^ 2 ≤
        (1 / 2 * ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s)))
            + L * s / (1 + Real.sqrt (μ * s)) ^ 2
            + 2 * μ / L / (1 - Real.sqrt (μ * s)) ^ 2
            + L * s / 2 * ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) ^ 2) *
          L * ‖x 0 - xs‖ ^ 2 := by
  have hL := hf.isF1.L_pos
  have hμ := hf.mu_pos
  set q := Real.sqrt s with hqdef
  set m := Real.sqrt μ with hmdef
  have hq : 0 < q := Real.sqrt_pos.mpr hs
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hqq : q ^ 2 = s := Real.sq_sqrt hs.le
  have hmm : m ^ 2 = μ := Real.sq_sqrt hμ.le
  set r := Real.sqrt (μ * s) with hrdef
  have hrmq : r = m * q := by rw [hrdef, Real.sqrt_mul hμ.le]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by
    have : r ^ 2 < 1 := by rw [hrdef, Real.sq_sqrt (by positivity)]; exact hμs
    nlinarith
  have h1r : 0 < 1 - r := by linarith
  have h1r' : 0 < 1 + r := by linarith
  set g := gradient f (x 0) with hg
  -- the first iterate
  have hx1 : x 1 = x 0 - (2 * s / (1 + r)) • g := by
    rw [hrun.step_x 0, hrun.step_y 0, hrun.init, ← hrdef, ← hg]
    rw [← Aux_HR_eq39.scal1 s r hr0]
    module
  have hvel : vel s x 0 = -(2 * q / (1 + r)) • g := by
    unfold vel
    rw [hx1, ← hqdef]
    have : x 0 - (2 * s / (1 + r)) • g - x 0 = -((2 * s / (1 + r)) • g) := by abel
    rw [this, smul_neg, smul_smul, neg_smul]
    congr 2
    rw [← hqq]
    field_simp
  have hV : vel s x 0 + (2 * m / (1 - r)) • (x (0 + 1) - xs) + q • g =
      (2 * m / (1 - r)) • (x 0 - xs) - ((1 + r) / (1 - r)) • (q • g) := by
    rw [zero_add, hvel, hx1]
    have hc : -(2 * q / (1 + r)) - 2 * m / (1 - r) * (2 * s / (1 + r)) + q =
        -((1 + r) / (1 - r) * q) := by
      have hne1 : 1 - r ≠ 0 := h1r.ne'
      have hne2 : 1 + r ≠ 0 := h1r'.ne'
      rw [← hqq]
      rw [show 2 * m / (1 - r) * (2 * q ^ 2 / (1 + r)) = 4 * (m * q) * q / (1 - r) / (1 + r) by
        ring, ← hrmq]
      field_simp
      ring
    linear_combination (norm := module) hc • g
  -- part 1
  have hnorm_vel : ‖vel s x 0‖ ^ 2 = 4 * s / (1 + r) ^ 2 * ‖g‖ ^ 2 := by
    rw [hvel, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← hqq]
    field_simp <;> ring
  constructor
  · unfold lyap
    rw [← hrdef, ← hg, hV, hnorm_vel]
    have : 0 ≤ s * ‖g‖ ^ 2 / (2 * (1 - r)) := by positivity
    have e : 1 / 4 * (4 * s / (1 + r) ^ 2 * ‖g‖ ^ 2) = s / (1 + r) ^ 2 * ‖g‖ ^ 2 := by ring
    linarith
  · -- part 2
    have hgs : gradient f xs = 0 := by
      have hmin' : IsLocalMin f xs := Filter.Eventually.of_forall hmin
      have h0 := hmin'.hasFDerivAt_eq_zero (hf.isF1.differentiable xs).hasFDerivAt
      rw [gradient, h0, map_zero]
    set D := ‖x 0 - xs‖ ^ 2 with hD
    have hD0 : 0 ≤ D := by positivity
    have hgD : ‖g‖ ^ 2 ≤ L ^ 2 * D := by
      have := hf.isF1.lipschitz_gradient (x 0) xs
      rw [hgs, sub_zero, ← hg] at this
      have h0 := norm_nonneg g
      rw [hD]
      nlinarith [norm_nonneg (x 0 - xs)]
    have hfD : f (x 0) - f xs ≤ L / 2 * D := by
      have := Aux_HR_eq39.descent f hf.isF1.differentiable L hf.isF1.lipschitz_gradient xs (x 0)
      rw [hgs, inner_zero_left] at this
      rw [hD]; linarith
    set A := 2 * m / (1 - r) with hA
    set B := (1 + r) / (1 - r) with hB
    have hsq : ‖A • (x 0 - xs) - B • (q • g)‖ ^ 2 ≤ 2 * (A ^ 2 * D) + 2 * (B ^ 2 * (s * ‖g‖ ^ 2)) := by
      have h1 := norm_sub_le (A • (x 0 - xs)) (B • (q • g))
      have e1 : ‖A • (x 0 - xs)‖ ^ 2 = A ^ 2 * D := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have e2 : ‖B • (q • g)‖ ^ 2 = B ^ 2 * (s * ‖g‖ ^ 2) := by
        rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
          sq_abs, hqq]
      have h2 : ‖A • (x 0 - xs) - B • (q • g)‖ ^ 2 ≤
          (‖A • (x 0 - xs)‖ + ‖B • (q • g)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖A • (x 0 - xs)‖ - ‖B • (q • g)‖)]
    have hA2 : A ^ 2 = 4 * μ / (1 - r) ^ 2 := by rw [hA, div_pow, mul_pow, hmm]; ring
    have hB0 : 0 ≤ B := by positivity
    have t1 : B * (f (x 0) - f xs) ≤ B * (L / 2 * D) := mul_le_mul_of_nonneg_left hfD hB0
    have t2 : s / (1 + r) ^ 2 * ‖g‖ ^ 2 ≤ s / (1 + r) ^ 2 * (L ^ 2 * D) :=
      mul_le_mul_of_nonneg_left hgD (by positivity)
    have t3 : B ^ 2 * (s * ‖g‖ ^ 2) ≤ B ^ 2 * (s * (L ^ 2 * D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgD hs.le) (sq_nonneg B)
    have eR : (1 / 2 * B + L * s / (1 + r) ^ 2 + 2 * μ / L / (1 - r) ^ 2 + L * s / 2 * B ^ 2) *
        L * D = B * (L / 2 * D) + s / (1 + r) ^ 2 * (L ^ 2 * D) +
          1 / 4 * (2 * (A ^ 2 * D) + 2 * (B ^ 2 * (s * (L ^ 2 * D)))) := by
      rw [hA2]
      field_simp
      ring
    rw [eR]
    nlinarith
