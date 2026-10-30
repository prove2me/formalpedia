-- Prove2me | solution 1 for JuschenkoMonod.tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:43:43.43797+00:00
-- url     : https://prove2.me/submissions/7d6e0a62-be04-4979-b4af-e656caff6a21

import Mathlib
import Definitions.Def_JuschenkoMonod

namespace JuschenkoMonod

/-- `F(x) = exp(-n e^{-x/n}) e^{-x/n}`; the terms of the first series are `F(|j|)`. -/
noncomputable def Fx (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * Real.exp (-x / n)) * Real.exp (-x / n)

/-- `A(x) = exp(-n e^{-x/n})`, the telescoping majorant. -/
noncomputable def Ax (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * Real.exp (-x / n))

/-- `D = n (1 - e^{-1/n})`. -/
noncomputable def Dn (n : ℕ) : ℝ := (n : ℝ) * (1 - Real.exp (-1 / n))

lemma Fx_nonneg (n : ℕ) (x : ℝ) : 0 ≤ Fx n x := by
  unfold Fx; positivity

lemma Ax_le_one (n : ℕ) (x : ℝ) : Ax n x ≤ 1 := by
  unfold Ax
  rw [Real.exp_le_one_iff]
  have : 0 ≤ (n : ℝ) * Real.exp (-x / n) := by positivity
  linarith

lemma Dn_pos (n : ℕ) (hn : 0 < n) : 0 < Dn n := by
  unfold Dn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Real.exp (-1 / n) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) hn')
  have : 0 < 1 - Real.exp (-1 / n) := by linarith
  positivity

/-- One telescoping step: `D F(x) ≤ A(x+1) - A(x)`. -/
lemma step (n : ℕ) (hn : 0 < n) (x : ℝ) :
    Dn n * Fx n x ≤ Ax n (x + 1) - Ax n x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s := Real.exp (-x / n) with hs
  set q := Real.exp (-1 / n) with hq
  have hsq : Real.exp (-(x + 1) / n) = s * q := by
    rw [hs, hq, ← Real.exp_add]
    congr 1
    ring
  have hA1 : Ax n (x + 1) = Real.exp (-(n * (s * q))) := by
    show Real.exp (-(n : ℝ) * Real.exp (-(x + 1) / n)) = _
    rw [hsq, neg_mul]
  have hA0 : Ax n x = Real.exp (-(n * s)) := by
    show Real.exp (-(n : ℝ) * s) = _
    rw [neg_mul]
  have hF : Fx n x = Real.exp (-(n * s)) * s := by
    show Real.exp (-(n : ℝ) * s) * s = _
    rw [neg_mul]
  rw [hA1, hA0, hF]
  have hD : Dn n = n * (1 - q) := rfl
  rw [hD]
  clear_value s q
  have key : Real.exp (-(n * (s * q))) = Real.exp (-(n * s)) * Real.exp (n * s * (1 - q)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [key]
  have h1 := Real.add_one_le_exp (n * s * (1 - q))
  have he : 0 < Real.exp (-(n * s)) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h1 he.le]

lemma telescope (n : ℕ) (hn : 0 < n) (c : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, Dn n * Fx n (k + c) ≤ Ax n (N + c) - Ax n c := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := step n hn (N + c)
    push_cast
    have e : (N : ℝ) + 1 + c = N + c + 1 := by ring
    rw [e]
    linarith

lemma partial_le (n : ℕ) (hn : 0 < n) (c : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, Fx n (k + c) ≤ (1 - Ax n c) / Dn n := by
  have hD := Dn_pos n hn
  rw [le_div_iff₀ hD, Finset.sum_mul]
  have := telescope n hn c N
  have h1 := Ax_le_one n (N + c)
  calc ∑ k ∈ Finset.range N, Fx n (k + c) * Dn n
      = ∑ k ∈ Finset.range N, Dn n * Fx n (k + c) := by
        refine Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ ≤ 1 - Ax n c := by linarith

lemma summable_shift (n : ℕ) (hn : 0 < n) (c : ℝ) :
    Summable (fun k : ℕ => Fx n (k + c)) :=
  summable_of_sum_range_le (fun _ => Fx_nonneg n _) (partial_le n hn c)

lemma tsum_shift_le (n : ℕ) (hn : 0 < n) (c : ℝ) :
    ∑' k : ℕ, Fx n (k + c) ≤ (1 - Ax n c) / Dn n :=
  Real.tsum_le_of_sum_range_le (fun _ => Fx_nonneg n _) (partial_le n hn c)

/-- `(2 - e^{-n}) / D ≤ e`. -/
lemma numeric (n : ℕ) (hn : 0 < n) : (2 - Real.exp (-(n : ℝ))) / Dn n ≤ Real.exp 1 := by
  have hD := Dn_pos n hn
  rw [div_le_iff₀ hD]
  have he := Real.exp_one_gt_d9
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    unfold Dn
    simp only [Nat.cast_one, one_mul, div_one]
    have hinv : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
    rw [hinv]
    have hpos : 0 < Real.exp 1 := Real.exp_pos 1
    rw [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne']
    have : (Real.exp 1)⁻¹ ≥ 0 := by positivity
    have hi : Real.exp 1 * (Real.exp 1)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    nlinarith
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast h
    have hnpos : (0 : ℝ) < n := by linarith
    set x : ℝ := 1 / n with hx
    have hx0 : 0 ≤ x := by positivity
    have hx2 : x ≤ 1 / 2 := by
      rw [hx, div_le_div_iff₀ hnpos (by norm_num)]; linarith
    have hnx : (n : ℝ) * x = 1 := by rw [hx]; field_simp
    set E := Real.exp x with hE
    have hEq := Real.quadratic_le_exp_of_nonneg hx0
    rw [← hE] at hEq
    have hEpos : 0 < E := Real.exp_pos x
    have hq : Real.exp (-1 / n) = E⁻¹ := by
      rw [hE, ← Real.exp_neg]; congr 1; rw [hx]; ring
    unfold Dn
    rw [hq]
    have hen : 0 ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
    -- suffices 2 ≤ e n (1 - 1/E), i.e. 2E ≤ e n (E - 1)
    have hkey : 2 * E ≤ Real.exp 1 * n * (E - 1) := by
      -- E(e n - 2) ≥ P (e n - 2) where P = 1 + x + x²/2, and e n (P - 1) - 2P ≥ 0
      have hen2 : 0 ≤ Real.exp 1 * n - 2 := by nlinarith
      have hP : Real.exp 1 * n * ((1 + x + x ^ 2 / 2) - 1) - 2 * (1 + x + x ^ 2 / 2) ≥ 0 := by
        have : Real.exp 1 * n * ((1 + x + x ^ 2 / 2) - 1) = Real.exp 1 * (1 + x / 2) := by
          have : (n : ℝ) * (x + x ^ 2 / 2) = 1 + x / 2 := by
            have : (n : ℝ) * (x + x ^ 2 / 2) = n * x * (1 + x / 2) := by ring
            rw [this, hnx, one_mul]
          calc Real.exp 1 * n * ((1 + x + x ^ 2 / 2) - 1)
              = Real.exp 1 * (n * (x + x ^ 2 / 2)) := by ring
            _ = _ := by rw [this]
        rw [this]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hEq hen2]
    have hinv : E * E⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
    have hinvpos : 0 ≤ E⁻¹ := by positivity
    -- e n (1 - 1/E) = e n (E - 1) / E ≥ 2
    have : 2 ≤ Real.exp 1 * (n * (1 - E⁻¹)) := by
      have h3 : Real.exp 1 * (n * (1 - E⁻¹)) = (Real.exp 1 * n * (E - 1)) * E⁻¹ := by
        field_simp
      rw [h3]
      have := mul_le_mul_of_nonneg_right hkey hinvpos
      rw [mul_assoc, hinv] at this
      linarith
    nlinarith

/-- `x e^{-n x} ≤ 1/(e n)`. -/
lemma mul_exp_le (n : ℕ) (hn : 0 < n) (s : ℝ) :
    Real.exp (-(n : ℝ) * s) * s ≤ 1 / (Real.exp 1 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.add_one_le_exp (n * s - 1)
  rw [Real.exp_sub] at h
  have he := Real.exp_pos 1
  have hy := Real.exp_pos (n * s)
  rw [le_div_iff₀ (by positivity)]
  -- n s ≤ e^{n s} / e
  have h2 : n * s * Real.exp 1 ≤ Real.exp (n * s) := by
    have := (le_div_iff₀ he).mp (by linarith : n * s - 1 + 1 ≤ Real.exp (n * s) / Real.exp 1)
    linarith
  have hneg : Real.exp (-(n : ℝ) * s) * Real.exp (n * s) = 1 := by
    rw [← Real.exp_add]; simp
  have hnn : 0 ≤ Real.exp (-(n : ℝ) * s) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left h2 hnn]

theorem lemma24_aux (n : ℕ) (hn : 0 < n) :
    (Summable fun j : ℤ => a n j * Real.exp (-(|j| : ℝ) / n)) ∧
      ∑' j : ℤ, a n j * Real.exp (-(|j| : ℝ) / n) ≤ 3 ∧
      (Summable fun j : ℤ => a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n)) ∧
      ∑' j : ℤ, a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n) ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set f : ℤ → ℝ := fun j => a n j * Real.exp (-(|j| : ℝ) / n) with hf
  have hfx : ∀ j : ℤ, f j = Fx n (|j| : ℝ) := fun j => rfl
  have hpos : (fun k : ℕ => f k) = fun k : ℕ => Fx n ((k : ℝ) + 0) := by
    funext k; rw [hfx]; simp
  have hneg : (fun k : ℕ => f (-(k + 1))) = fun k : ℕ => Fx n ((k : ℝ) + 1) := by
    funext k; rw [hfx]; congr 1; push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hs1 : Summable fun k : ℕ => f k := by rw [hpos]; exact summable_shift n hn 0
  have hs2 : Summable fun k : ℕ => f (-(k + 1)) := by rw [hneg]; exact summable_shift n hn 1
  have hsum : Summable f := Summable.of_nat_of_neg_add_one hs1 hs2
  have hf0 : ∀ j, 0 ≤ f j := fun j => by rw [hfx]; exact Fx_nonneg n _
  have hle_e : ∑' j : ℤ, f j ≤ Real.exp 1 := by
    rw [tsum_of_nat_of_neg_add_one hs1 hs2, hpos, hneg]
    have t1 := tsum_shift_le n hn 0
    have t2 := tsum_shift_le n hn 1
    have hA0 : Ax n 0 = Real.exp (-(n : ℝ)) := by unfold Ax; simp
    have hA1 : 0 ≤ Ax n 1 := by unfold Ax; positivity
    have hD := Dn_pos n hn
    have hnum := numeric n hn
    have : (1 - Ax n 0) / Dn n + (1 - Ax n 1) / Dn n ≤ (2 - Real.exp (-(n : ℝ))) / Dn n := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hD.le
      rw [hA0]; linarith
    linarith
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- second series: g j = f j ^ 2 ≤ f j / (e n)
  have hg : ∀ j : ℤ, a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n) = f j * f j := by
    intro j
    rw [hfx]
    unfold Fx a
    have : Real.exp (-2 * (|j| : ℝ) / n) = Real.exp (-(|j| : ℝ) / n) * Real.exp (-(|j| : ℝ) / n) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  have hfb : ∀ j : ℤ, f j ≤ 1 / (Real.exp 1 * n) := by
    intro j
    rw [hfx]
    exact mul_exp_le n hn _
  have hgle : ∀ j : ℤ, f j * f j ≤ f j * (1 / (Real.exp 1 * n)) :=
    fun j => mul_le_mul_of_nonneg_left (hfb j) (hf0 j)
  have hgsum : Summable fun j : ℤ => f j * f j :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hf0 j) (hf0 j)) hgle
      (hsum.mul_right _)
  refine ⟨hsum, he3.trans' hle_e, ?_, ?_⟩
  · simp_rw [hg]; exact hgsum
  · simp_rw [hg]
    calc ∑' j : ℤ, f j * f j ≤ ∑' j : ℤ, f j * (1 / (Real.exp 1 * n)) :=
          hgsum.tsum_le_tsum hgle (hsum.mul_right _)
      _ = (∑' j : ℤ, f j) * (1 / (Real.exp 1 * n)) := tsum_mul_right
      _ ≤ Real.exp 1 * (1 / (Real.exp 1 * n)) :=
          mul_le_mul_of_nonneg_right hle_e (by positivity)
      _ = 1 / n := by field_simp

end JuschenkoMonod

theorem solution : ∀ (n : ℕ) (_ : 0 < n),
    (Summable fun j : ℤ => JuschenkoMonod.a n j * Real.exp (-(|j| : ℝ) / n)) ∧
      ∑' j : ℤ, JuschenkoMonod.a n j * Real.exp (-(|j| : ℝ) / n) ≤ 3 ∧
      (Summable fun j : ℤ => JuschenkoMonod.a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n)) ∧
      ∑' j : ℤ, JuschenkoMonod.a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n) ≤ 1 / n :=
  fun n hn => JuschenkoMonod.lemma24_aux n hn
