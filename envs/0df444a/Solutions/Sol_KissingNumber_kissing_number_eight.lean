-- Prove2me | solution 1 for KissingNumber.kissing_number_eight
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:56:15.687269+00:00
-- url     : https://prove2.me/submissions/09209b4f-e194-4253-993d-3d6bc4973af4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_KissingNumber
import Theorems.Thm_LefebvreVariations_gegenbauer_positive_definite
set_option autoImplicit false
open KissingNumber
open scoped InnerProductSpace

/-! Reduction of `KissingNumber.kissing_number_eight` (τ(8) = 240) to the variation
`LefebvreVariations.gegenbauer_positive_definite` (Schoenberg's positive-definiteness of the
Gegenbauer polynomials on spheres). The variation is the only open step in this file.
Upper bound: Delsarte's linear-programming bound with the Levenshtein polynomial
`f(t) = (t+1)(t+1/2)²t²(t-1/2)`, whose expansion in the polynomials `C_k^{(3)}` has
coefficients `3/320, 1/80, 5/448, 39/4480, 19/3840, 1/448, 1/1792` and `f(1)/f₀ = 240`.
Lower bound: the 240 roots of `E₈`, checked by kernel computation (`decide +kernel`). -/

open LefebvreVariations

private noncomputable def G (k : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (k / 2 + 1),
    (-1 : ℝ) ^ m * (ascPochhammer ℝ (k - m)).eval ((((8 : ℕ) : ℝ) - 2) / 2) /
      ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ)) * (2 * t) ^ (k - 2 * m)

private lemma G_sum_nonneg (k : ℕ) (C : KissingConfig 8) :
    0 ≤ ∑ x ∈ C.points, ∑ y ∈ C.points, G k ⟪x, y⟫_ℝ :=
  gegenbauer_positive_definite 8 (by norm_num) k C.points C.unit_norm

private lemma poch3 (j : ℕ) : (ascPochhammer ℝ j).eval ((((8 : ℕ) : ℝ) - 2) / 2) = (ascPochhammer ℝ j).eval 3 := by
  norm_num

private lemma f_expand (t : ℝ) :
    (t + 1) * (t + 1 / 2) ^ 2 * t ^ 2 * (t - 1 / 2) =
      3 / 320 * G 0 t + 1 / 80 * G 1 t + 5 / 448 * G 2 t + 39 / 4480 * G 3 t +
        19 / 3840 * G 4 t + 1 / 448 * G 5 t + 1 / 1792 * G 6 t := by
  simp only [G, poch3]
  simp [Finset.sum_range_succ, ascPochhammer_succ_right, Nat.factorial]
  ring

private lemma f_nonpos (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1 / 2) :
    (t + 1) * (t + 1 / 2) ^ 2 * t ^ 2 * (t - 1 / 2) ≤ 0 := by
  have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ t + 1) (sq_nonneg (t + 1 / 2)))
    (sq_nonneg t)
  exact mul_nonpos_of_nonneg_of_nonpos this (by linarith)

private lemma card_le (C : KissingConfig 8) : C.points.card ≤ 240 := by
  set s := C.points with hsdef
  have hlow : 3 / 320 * (s.card : ℝ) ^ 2 ≤
      ∑ x ∈ s, ∑ y ∈ s, (⟪x, y⟫_ℝ + 1) * (⟪x, y⟫_ℝ + 1 / 2) ^ 2 * ⟪x, y⟫_ℝ ^ 2 *
        (⟪x, y⟫_ℝ - 1 / 2) := by
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
    rw [← hsdef] at h1 h2 h3 h4 h5 h6
    linarith
  have hup : ∑ x ∈ s, ∑ y ∈ s, (⟪x, y⟫_ℝ + 1) * (⟪x, y⟫_ℝ + 1 / 2) ^ 2 * ⟪x, y⟫_ℝ ^ 2 *
      (⟪x, y⟫_ℝ - 1 / 2) ≤ ∑ _x ∈ s, (9 / 4 : ℝ) := by
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← Finset.add_sum_erase s _ hx]
    have hxx : ⟪x, x⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, C.unit_norm x hx]; norm_num
    have hrest : ∑ y ∈ s.erase x, (⟪x, y⟫_ℝ + 1) * (⟪x, y⟫_ℝ + 1 / 2) ^ 2 * ⟪x, y⟫_ℝ ^ 2 *
        (⟪x, y⟫_ℝ - 1 / 2) ≤ 0 := by
      refine Finset.sum_nonpos fun y hy => ?_
      have hy' := Finset.mem_of_mem_erase hy
      have hne := Finset.ne_of_mem_erase hy
      have hcs := abs_real_inner_le_norm x y
      rw [C.unit_norm x hx, C.unit_norm y hy', one_mul] at hcs
      exact f_nonpos _ (neg_le_of_abs_le hcs) (C.inner_le x hx y hy' (Ne.symm hne))
    rw [hxx]
    linarith
  rw [Finset.sum_const, nsmul_eq_mul] at hup
  have hN : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have : (s.card : ℝ) ≤ 240 := by nlinarith
  exact_mod_cast this

/-- Doubled coordinates of the 112 roots `±eᵢ ± eⱼ`. -/
private def typeA : List (List ℤ) :=
  (List.range 8).flatMap fun i => (List.range 8).flatMap fun j =>
    if i < j then [2, -2].flatMap fun s => [2, -2].map fun t =>
      (List.range 8).map fun l => if l = i then s else if l = j then t else 0
    else []

private def signs : ℕ → List (List ℤ)
  | 0 => [[]]
  | n + 1 => (signs n).flatMap fun v => [1 :: v, -1 :: v]

/-- Doubled coordinates of the 128 roots `(±½)⁸` with an even number of minus signs. -/
private def typeB : List (List ℤ) := (signs 8).filter fun v => v.count (-1) % 2 == 0

private def raw : List (List ℤ) := typeA ++ typeB

private def dotL (a b : List ℤ) : ℤ := ((List.range 8).map fun i => a.getD i 0 * b.getD i 0).sum

private theorem raw_norm : ∀ a ∈ raw, dotL a a = 8 := by decide +kernel

private theorem raw_pair : raw.Pairwise (fun a b => dotL a b ≤ 4) := by decide +kernel

private theorem raw_len : raw.length = 240 := by decide +kernel

private lemma dotL_comm (a b : List ℤ) : dotL a b = dotL b a := by
  simp [dotL, mul_comm]

private noncomputable def toA (a : List ℤ) : Ambient 8 :=
  WithLp.toLp 2 (fun i : Fin 8 => (a.getD i 0 : ℝ) / Real.sqrt 8)

private lemma inner_toA (a b : List ℤ) : ⟪toA a, toA b⟫_ℝ = (dotL a b : ℝ) / 8 := by
  have hpos : Real.sqrt 8 ≠ 0 := by positivity
  simp only [toA, PiLp.inner_apply, dotL, Fin.sum_univ_eight, List.range_succ, List.range_zero,
    List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, RCLike.inner_apply, conj_trivial]
  push_cast
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  simp
  ring

private lemma e8_card_ge : ∃ C : KissingConfig 8, C.points.card = 240 := by
  have hnodup : (raw.map toA).Nodup := by
    refine List.pairwise_map.2 (raw_pair.imp_of_mem ?_)
    intro a b ha _ hab heq
    have h1 := inner_toA a b
    rw [heq, inner_toA, raw_norm b ‹_›] at h1
    have : (dotL a b : ℝ) ≤ 4 := by exact_mod_cast hab
    linarith
  refine ⟨{ points := (raw.map toA).toFinset
            unit_norm := ?_
            inner_le := ?_ }, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    have h := inner_toA a a
    rw [raw_norm a ha, real_inner_self_eq_norm_sq] at h
    have h0 := norm_nonneg (toA a)
    nlinarith
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
    have hab : a ≠ b := fun h => hxy (by rw [h])
    have : Std.Symm (fun u v : List ℤ => dotL u v ≤ 4) :=
      ⟨fun u v h => by rw [dotL_comm]; exact h⟩
    have hle := raw_pair.forall ha hb hab
    rw [inner_toA]
    have : (dotL a b : ℝ) ≤ 4 := by exact_mod_cast hle
    linarith
  · rw [List.toFinset_card_of_nodup hnodup, List.length_map, raw_len]

theorem solution : kissingNumber 8 = (240 : ℕ∞) := by
  obtain ⟨C, hC⟩ := e8_card_ge
  apply le_antisymm
  · refine iSup_le fun D => ?_
    exact_mod_cast card_le D
  · have := le_iSup (fun C : KissingConfig 8 => (C.points.card : ℕ∞)) C
    simp only [hC] at this
    exact_mod_cast this
