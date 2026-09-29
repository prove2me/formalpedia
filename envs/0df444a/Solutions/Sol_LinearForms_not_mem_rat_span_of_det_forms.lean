-- Prove2me | solution 1 for LinearForms.not_mem_rat_span_of_det_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T18:05:18.235986+00:00
-- url     : https://prove2.me/submissions/37cadc8d-8664-43e2-897b-bfed95bdff22

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

lemma LinearForms_det_forms_core_aux (x y : ℝ) (d a b : ℤ) (hd : 0 < d) (hdy : (d : ℝ) * y = a + b * x)
    (p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℤ)
    (hdet : p0 * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2) ≠ 0) :
    1 ≤ ((d : ℝ) * (d + |(b : ℝ)|)) *
      ((|(p0 : ℝ) + q0 * x + r0 * y| + |(p1 : ℝ) + q1 * x + r1 * y|
        + |(p2 : ℝ) + q2 * x + r2 * y|) *
      ((|(q0 : ℝ)| + |(r0 : ℝ)|) + (|(q1 : ℝ)| + |(r1 : ℝ)|) + (|(q2 : ℝ)| + |(r2 : ℝ)|))) := by
  set m0 := d * p0 + a * r0
  set m1 := d * p1 + a * r1
  set m2 := d * p2 + a * r2
  set k0 := d * q0 + b * r0
  set k1 := d * q1 + b * r1
  set k2 := d * q2 + b * r2
  have hid : d ^ 2 * (p0 * (q1 * r2 - r1 * q2) - q0 * (p1 * r2 - r1 * p2) + r0 * (p1 * q2 - q1 * p2))
      = r0 * (m1 * k2 - m2 * k1) - r1 * (m0 * k2 - m2 * k0) + r2 * (m0 * k1 - m1 * k0) := by
    simp only [m0, m1, m2, k0, k1, k2]; ring
  have hne : (m0 * k1 - m1 * k0) ≠ 0 ∨ (m0 * k2 - m2 * k0) ≠ 0 ∨ (m1 * k2 - m2 * k1) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [h1, h2, h3] at hid
    have : d ^ 2 ≠ 0 := by positivity
    exact hdet (by simpa [this] using hid)
  have hone : (1 : ℤ) ≤ |m0 * k1 - m1 * k0| + |m0 * k2 - m2 * k0| + |m1 * k2 - m2 * k1| := by
    have a1 := abs_nonneg (m0 * k1 - m1 * k0)
    have a2 := abs_nonneg (m0 * k2 - m2 * k0)
    have a3 := abs_nonneg (m1 * k2 - m2 * k1)
    rcases hne with h | h | h
    · have := Int.one_le_abs h; omega
    · have := Int.one_le_abs h; omega
    · have := Int.one_le_abs h; omega
  have honeR : (1 : ℝ) ≤ |((m0 * k1 - m1 * k0 : ℤ) : ℝ)| + |((m0 * k2 - m2 * k0 : ℤ) : ℝ)|
      + |((m1 * k2 - m2 * k1 : ℤ) : ℝ)| := by
    simp only [← Int.cast_abs]; exact_mod_cast hone
  -- real forms
  set L0 : ℝ := (p0 : ℝ) + q0 * x + r0 * y
  set L1 : ℝ := (p1 : ℝ) + q1 * x + r1 * y
  set L2 : ℝ := (p2 : ℝ) + q2 * x + r2 * y
  set H0 : ℝ := |(q0 : ℝ)| + |(r0 : ℝ)|
  set H1 : ℝ := |(q1 : ℝ)| + |(r1 : ℝ)|
  set H2 : ℝ := |(q2 : ℝ)| + |(r2 : ℝ)|
  set c : ℝ := (d : ℝ) + |(b : ℝ)|
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkey : ∀ (pi qi ri pj qj rj : ℤ),
      (((d * pi + a * ri) * (d * qj + b * rj) - (d * pj + a * rj) * (d * qi + b * ri) : ℤ) : ℝ)
        = d * (((pi : ℝ) + qi * x + ri * y) * ((d * qj + b * rj : ℤ) : ℝ)
          - ((pj : ℝ) + qj * x + rj * y) * ((d * qi + b * ri : ℤ) : ℝ)) := by
    intro pi qi ri pj qj rj
    push_cast
    linear_combination (rj * ((d:ℝ) * qi + b * ri) - ↑ri * ((d:ℝ) * qj + b * rj)) * hdy
  have hk : ∀ qi ri : ℤ, |((d * qi + b * ri : ℤ) : ℝ)| ≤ c * (|(qi : ℝ)| + |(ri : ℝ)|) := by
    intro qi ri
    push_cast
    have e1 : |(d : ℝ) * qi| = d * |(qi : ℝ)| := by rw [abs_mul, abs_of_pos hdR]
    have e2 : |(b : ℝ) * ri| = |(b : ℝ)| * |(ri : ℝ)| := abs_mul _ _
    have := abs_add_le ((d : ℝ) * qi) ((b : ℝ) * ri)
    have hb := abs_nonneg (b : ℝ)
    have hq := abs_nonneg (qi : ℝ)
    have hr := abs_nonneg (ri : ℝ)
    simp only [c]; nlinarith
  have hpair : ∀ (pi qi ri pj qj rj : ℤ),
      |(((d * pi + a * ri) * (d * qj + b * rj) - (d * pj + a * rj) * (d * qi + b * ri) : ℤ) : ℝ)|
        ≤ d * c * (|(pi : ℝ) + qi * x + ri * y| * (|(qj : ℝ)| + |(rj : ℝ)|)
          + |(pj : ℝ) + qj * x + rj * y| * (|(qi : ℝ)| + |(ri : ℝ)|)) := by
    intro pi qi ri pj qj rj
    rw [hkey, abs_mul, abs_of_pos hdR]
    have t := abs_sub (((pi : ℝ) + qi * x + ri * y) * ((d * qj + b * rj : ℤ) : ℝ))
      (((pj : ℝ) + qj * x + rj * y) * ((d * qi + b * ri : ℤ) : ℝ))
    rw [abs_mul, abs_mul] at t
    have kj := hk qj rj
    have ki := hk qi ri
    have u1 := mul_le_mul_of_nonneg_left kj (abs_nonneg ((pi : ℝ) + qi * x + ri * y))
    have u2 := mul_le_mul_of_nonneg_left ki (abs_nonneg ((pj : ℝ) + qj * x + rj * y))
    have : |((pi : ℝ) + qi * x + ri * y) * ((d * qj + b * rj : ℤ) : ℝ)
      - ((pj : ℝ) + qj * x + rj * y) * ((d * qi + b * ri : ℤ) : ℝ)|
        ≤ c * (|(pi : ℝ) + qi * x + ri * y| * (|(qj : ℝ)| + |(rj : ℝ)|)
          + |(pj : ℝ) + qj * x + rj * y| * (|(qi : ℝ)| + |(ri : ℝ)|)) := by nlinarith
    calc (d : ℝ) * |_| ≤ d * (c * _) := mul_le_mul_of_nonneg_left this hdR.le
      _ = _ := by ring
  have P01 := hpair p0 q0 r0 p1 q1 r1
  have P02 := hpair p0 q0 r0 p2 q2 r2
  have P12 := hpair p1 q1 r1 p2 q2 r2
  have l0 := abs_nonneg L0
  have l1 := abs_nonneg L1
  have l2 := abs_nonneg L2
  have h0 : 0 ≤ H0 := by positivity
  have h1 : 0 ≤ H1 := by positivity
  have h2 : 0 ≤ H2 := by positivity
  have hc : 0 ≤ (d : ℝ) * c := by positivity
  have diag : 0 ≤ (d : ℝ) * c * (|L0| * H0 + |L1| * H1 + |L2| * H2) := by positivity
  have expand : (d : ℝ) * c * ((|L0| + |L1| + |L2|) * (H0 + H1 + H2))
      = d * c * (|L0| * H1 + |L1| * H0) + d * c * (|L0| * H2 + |L2| * H0)
        + d * c * (|L1| * H2 + |L2| * H1) + d * c * (|L0| * H0 + |L1| * H1 + |L2| * H2) := by ring
  rw [expand]
  linarith

theorem solution (x y : ℝ) (p q r : ℕ → ℤ)
    (hdet : ∃ᶠ n in atTop,
      (!![p n, q n, r n; p (n + 1), q (n + 1), r (n + 1); p (n + 2), q (n + 2), r (n + 2)] :
        Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0)
    (hS : Tendsto (fun n : ℕ =>
      (|(p n : ℝ) + q n * x + r n * y| + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y|
        + |(p (n + 2) : ℝ) + q (n + 2) * x + r (n + 2) * y|) *
      ((|(q n : ℝ)| + |(r n : ℝ)|) + (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
        + (|(q (n + 2) : ℝ)| + |(r (n + 2) : ℝ)|))) atTop (𝓝 0)) :
    ∀ α β : ℚ, y ≠ α + β * x := by
  intro α β hy
  set d : ℤ := (α.den : ℤ) * β.den with hd_def
  set a : ℤ := α.num * β.den
  set b : ℤ := β.num * α.den
  have hd : 0 < d := by positivity
  have hdy : (d : ℝ) * y = a + b * x := by
    rw [hy, Rat.cast_def, Rat.cast_def]
    have ha : (α.den : ℝ) ≠ 0 := by positivity
    have hb : (β.den : ℝ) ≠ 0 := by positivity
    simp only [d, a, b]; push_cast
    field_simp
  set C : ℝ := (d : ℝ) * (d + |(b : ℝ)|)
  have hC : 0 < C := by positivity
  have hev : ∀ᶠ n in atTop, _ < 1 / C := hS.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (hdet.and_eventually hev).exists
  rw [Matrix.det_fin_three] at hn1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const] at hn1
  have key := LinearForms_det_forms_core_aux x y d a b hd hdy (p n) (q n) (r n) (p (n + 1)) (q (n + 1)) (r (n + 1))
    (p (n + 2)) (q (n + 2)) (r (n + 2)) (by intro h; apply hn1; linear_combination h)
  rw [lt_div_iff₀ hC] at hn2
  linarith [mul_comm C ((|(p n : ℝ) + q n * x + r n * y| + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y|
        + |(p (n + 2) : ℝ) + q (n + 2) * x + r (n + 2) * y|) *
      ((|(q n : ℝ)| + |(r n : ℝ)|) + (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
        + (|(q (n + 2) : ℝ)| + |(r (n + 2) : ℝ)|)))]
