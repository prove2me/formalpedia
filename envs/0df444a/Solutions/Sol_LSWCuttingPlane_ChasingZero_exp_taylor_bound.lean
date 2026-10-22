-- Prove2me | solution 1 for LSWCuttingPlane.ChasingZero.exp_taylor_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:02:07.041705+00:00
-- url     : https://prove2.me/submissions/f86095dd-51da-49b5-aa90-0317775c95ff

import Mathlib
set_option autoImplicit false

lemma uu_mono (f f' : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (f' x) x) (h : ∀ x, 0 ≤ x → 0 ≤ f' x) :
    MonotoneOn f (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.2 (fun x => (hd x).continuousAt)).continuousOn
  · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    exact h x (le_of_lt hx)

lemma uu_A (y : ℝ) (hy : 0 ≤ y) : 1 - y ^ 2 / 2 ≤ Real.exp (-y) * (1 + y) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x) * (1 + x) - 1 + x ^ 2 / 2)
      (x * (1 - Real.exp (-x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    have h2 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h3 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have := ((h1.mul h2).sub_const 1).add h3
    refine HasDerivAt.congr_deriv this ?_
    ring
  have hm := uu_mono _ _ hd (fun x hx => mul_nonneg hx (by
    have : Real.exp (-x) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
    linarith))
  have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp at this
  linarith

lemma uu_B (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 1 - x + x ^ 2 / 2 - Real.exp (-x))
      (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_neg x).exp
    have h3 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have h4 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have := (h4.add h3).sub h1
    refine HasDerivAt.congr_deriv this ?_
    ring
  have hm := uu_mono _ _ hd (fun x hx => by
    have := Real.add_one_le_exp (-x)
    linarith)
  have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp at this
  linarith

lemma uu_part1 (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h := uu_A x hx
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
    nlinarith [this, h2]
  · rw [abs_of_nonpos hx]
    have h := uu_B (-x) (by linarith)
    simp only [neg_neg] at h
    have h1 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith [sq_nonneg x]

theorem solution :
    (∀ x : ℝ, Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp |x|) ∧
    (∀ c δ x α : ℝ, |δ| ≤ c →
      Real.exp (α * x + α * δ) ≤
        Real.exp (α * x) + α * δ * Real.exp (α * x)
          + 1 / 2 * α ^ 2 * δ ^ 2 * Real.exp (α * x + |α| * c)) := by
  refine ⟨uu_part1, ?_⟩
  intro c δ x α hδ
  have h := uu_part1 (α * δ)
  have hab : Real.exp |α * δ| ≤ Real.exp (|α| * c) := by
    apply Real.exp_le_exp.2
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hδ (abs_nonneg α)
  have hE := Real.exp_pos (α * x)
  have hsq : 0 ≤ (α * δ) ^ 2 / 2 := by positivity
  rw [Real.exp_add]
  calc Real.exp (α * x) * Real.exp (α * δ)
      ≤ Real.exp (α * x) * (1 + α * δ + (α * δ) ^ 2 / 2 * Real.exp |α * δ|) :=
        mul_le_mul_of_nonneg_left h hE.le
    _ ≤ Real.exp (α * x) * (1 + α * δ + (α * δ) ^ 2 / 2 * Real.exp (|α| * c)) := by
        apply mul_le_mul_of_nonneg_left _ hE.le
        have := mul_le_mul_of_nonneg_left hab hsq
        linarith
    _ = _ := by rw [Real.exp_add (α * x) (|α| * c)]; ring
