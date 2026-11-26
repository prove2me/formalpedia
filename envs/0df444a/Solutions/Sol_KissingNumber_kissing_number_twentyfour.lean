-- Prove2me | solution 1 for KissingNumber.kissing_number_twentyfour
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T22:05:42.557135+00:00
-- url     : https://prove2.me/submissions/2b603da0-1165-4cbd-9c18-5a20ca3874f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_KissingNumber
import Theorems.Thm_LefebvreVariations_kissing_number_twentyfour_lower
import Theorems.Thm_LefebvreVariations_gegenbauer_positive_definite
set_option autoImplicit false
open KissingNumber
open scoped InnerProductSpace

/-! Reduction of `KissingNumber.kissing_number_twentyfour` (τ(24) = 196560).
Two lemmas are open step'd, and they are the only sources of `the gap axiom`:
* `LefebvreVariations.kissing_number_twentyfour_lower` (the new variation: the Leech lattice
  gives 196560 minimal vectors forming a kissing configuration);
* `LefebvreVariations.gegenbauer_positive_definite` (the already published variation, Schoenberg),
  used only for `n = 24` and `0 ≤ k ≤ 10`.
Upper bound: Delsarte–Levenshtein with
`f(t) = (t+1)(t+1/2)²(t+1/4)²t²(t-1/4)²(t-1/2)` (degree 10, `f ≤ 0` on `[-1,1/2]`),
`f = Σ_{k≤10} c_k C_k^{(11)}` with all `c_k > 0`, `c_0 = 15/1490944`, `f(1) = 2025/1024`,
`f(1)/c_0 = 196560`; the expansion is checked by `ring`. -/

open LefebvreVariations

private noncomputable def G (k : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (k / 2 + 1),
    (-1 : ℝ) ^ m * (ascPochhammer ℝ (k - m)).eval ((((24 : ℕ) : ℝ) - 2) / 2) /
      ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ)) * (2 * t) ^ (k - 2 * m)

private lemma G_sum_nonneg (k : ℕ) (C : KissingConfig 24) :
    0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points, G k ⟪x, y⟫_ℝ :=
  gegenbauer_positive_definite 24 (by norm_num) k C.points C.unit_norm

private lemma poch11 (j : ℕ) :
    (ascPochhammer ℝ j).eval ((((24 : ℕ) : ℝ) - 2) / 2) = (ascPochhammer ℝ j).eval 11 := by
  norm_num

private noncomputable def f (t : ℝ) : ℝ :=
  (t + 1) * (t + 1 / 2) ^ 2 * (t + 1 / 4) ^ 2 * t ^ 2 * (t - 1 / 4) ^ 2 * (t - 1 / 2)

private lemma f_expand (t : ℝ) :
    f t =
      15 / 1490944 * G 0 t + 45 / 4100096 * G 1 t + 15 / 1949696 * G 2 t +
        435 / 79659008 * G 3 t + 6927 / 2230452224 * G 4 t + 489 / 278806528 * G 5 t +
        17747 / 22435725312 * G 6 t + 261 / 756760576 * G 7 t + 5 / 44808192 * G 8 t +
        3 / 94595072 * G 9 t + 1 / 189190144 * G 10 t := by
  simp only [f, G, poch11]
  simp [Finset.sum_range_succ, ascPochhammer_succ_right, Nat.factorial]
  ring

private lemma f_nonpos (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1 / 2) : f t ≤ 0 := by
  have h := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ t + 1)
      (sq_nonneg (t + 1 / 2))) (sq_nonneg (t + 1 / 4))) (sq_nonneg t))
    (sq_nonneg (t - 1 / 4))
  exact mul_nonpos_of_nonneg_of_nonpos h (by linarith)

private lemma card_le (C : KissingConfig 24) : C.points.card ≤ 196560 := by
  set s := C.points with hsdef
  have hlow : 15 / 1490944 * (s.card : ℝ) ^ 2 ≤ ∑ x ∈ s, ∑ y ∈ s, f ⟪x, y⟫_ℝ := by
    simp only [f_expand, Finset.sum_add_distrib, ← Finset.mul_sum]
    have g0 : ∑ x ∈ s, ∑ y ∈ s, G 0 ⟪x, y⟫_ℝ = (s.card : ℝ) ^ 2 := by
      simp [G]; ring
    rw [g0]
    have h1 := G_sum_nonneg 1 C
    have h2 := G_sum_nonneg 2 C
    have h3 := G_sum_nonneg 3 C
    have h4 := G_sum_nonneg 4 C
    have h5 := G_sum_nonneg 5 C
    have h6 := G_sum_nonneg 6 C
    have h7 := G_sum_nonneg 7 C
    have h8 := G_sum_nonneg 8 C
    have h9 := G_sum_nonneg 9 C
    have h10 := G_sum_nonneg 10 C
    rw [← hsdef] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    linarith
  have hup : ∑ x ∈ s, ∑ y ∈ s, f ⟪x, y⟫_ℝ ≤ ∑ _x ∈ s, (2025 / 1024 : ℝ) := by
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← Finset.add_sum_erase s _ hx]
    have hxx : ⟪x, x⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, C.unit_norm x hx]; norm_num
    have hrest : ∑ y ∈ s.erase x, f ⟪x, y⟫_ℝ ≤ 0 := by
      refine Finset.sum_nonpos fun y hy => ?_
      have hy' := Finset.mem_of_mem_erase hy
      have hne := Finset.ne_of_mem_erase hy
      have hcs := abs_real_inner_le_norm x y
      rw [C.unit_norm x hx, C.unit_norm y hy', one_mul] at hcs
      exact f_nonpos _ (neg_le_of_abs_le hcs) (C.inner_le x hx y hy' (Ne.symm hne))
    rw [hxx]
    have : f 1 = 2025 / 1024 := by simp only [f]; norm_num
    linarith
  rw [Finset.sum_const, nsmul_eq_mul] at hup
  have hN : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have : (s.card : ℝ) ≤ 196560 := by nlinarith
  exact_mod_cast this

theorem solution : kissingNumber 24 = (196560 : ℕ∞) := by
  apply le_antisymm
  · refine iSup_le fun D => ?_
    exact_mod_cast card_le D
  · exact LefebvreVariations.kissing_number_twentyfour_lower
