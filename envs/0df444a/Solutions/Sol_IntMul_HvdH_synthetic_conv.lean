-- Prove2me | solution 1 for IntMul.HvdH.synthetic_conv
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T21:05:48.310987+00:00
-- url     : https://prove2.me/submissions/579edef0-a846-43e3-8e4a-798e7de86565

import Mathlib

open Finset

namespace IntMul.HvdH.Syn

variable {R : Type*} [CommRing R]

/-- Radix-2 Cooley–Tukey, even outputs. -/
theorem ct_even (m : ℕ) (ω : R) (hω : ω ^ m = -1) (u : ℕ → R) (l : ℕ) :
    ∑ k ∈ range (2 * m), ω ^ (2 * l * k) * u k =
      ∑ k ∈ range m, (ω ^ 2) ^ (l * k) * (u k + u (k + m)) := by
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : ω ^ (2 * l * (m + k)) = ω ^ (2 * l * k) := by
    rw [show 2 * l * (m + k) = 2 * l * k + m * (2 * l) by ring, pow_add, pow_mul ω m, hω,
      pow_mul (-1 : R) 2, neg_one_sq, one_pow, mul_one]
  rw [this, ← pow_mul, show 2 * (l * k) = 2 * l * k by ring, add_comm m k]; ring

/-- Radix-2 Cooley–Tukey, odd outputs (with the twiddle factor `ω^k`). -/
theorem ct_odd (m : ℕ) (ω : R) (hω : ω ^ m = -1) (u : ℕ → R) (l : ℕ) :
    ∑ k ∈ range (2 * m), ω ^ ((2 * l + 1) * k) * u k =
      ∑ k ∈ range m, (ω ^ 2) ^ (l * k) * (ω ^ k * (u k - u (k + m))) := by
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : ω ^ ((2 * l + 1) * (m + k)) = -ω ^ ((2 * l + 1) * k) := by
    rw [show (2 * l + 1) * (m + k) = (2 * l + 1) * k + m * (2 * l + 1) by ring, pow_add, pow_mul ω m,
      hω, pow_succ, pow_mul (-1 : R) 2, neg_one_sq, one_pow]; ring
  have h2 : ω ^ ((2 * l + 1) * k) = (ω ^ 2) ^ (l * k) * ω ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [this, h2, add_comm m k]; ring

lemma sum_block (x : R) (L : ℕ) (hx : x ^ L = -1) (c : ℕ) :
    ∑ k ∈ range (2 * L * c), x ^ k = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [show 2 * L * (c + 1) = 2 * L * c + (L + L) by ring, Finset.sum_range_add, ih, zero_add,
      Finset.sum_range_add]
    have : ∑ i ∈ range L, x ^ (2 * L * c + (L + i)) =
        x ^ L * ∑ i ∈ range L, x ^ (2 * L * c + i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← pow_add]; congr 1; ring
    rw [this, hx]; ring

/-- If `ω^{2^e} = -1` then `ω` is a principal `2^{e+1}`-th root of unity. -/
theorem sum_pow_eq_zero (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (j : ℕ)
    (hj : ¬ 2 ^ (e + 1) ∣ j) : ∑ k ∈ range (2 ^ (e + 1)), ω ^ (j * k) = 0 := by
  have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero _)
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj0
  have ha : a ≤ e := by
    by_contra h
    exact hj (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) b)
  have hx : (ω ^ (2 ^ a * b)) ^ (2 ^ (e - a)) = -1 := by
    rw [← pow_mul, show 2 ^ a * b * 2 ^ (e - a) = 2 ^ e * b by
      rw [mul_comm (2 ^ a) b, mul_assoc, ← pow_add, Nat.add_sub_cancel' ha, mul_comm],
      pow_mul, hω, hb.neg_one_pow]
  have := sum_block (ω ^ (2 ^ a * b)) (2 ^ (e - a)) hx (2 ^ a)
  rw [show 2 * 2 ^ (e - a) * 2 ^ a = 2 ^ (e + 1) by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ha, pow_succ, mul_comm]] at this
  simpa [← pow_mul] using this

lemma pow_mod_eq (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (m : ℕ) :
    ω ^ m = ω ^ (m % 2 ^ (e + 1)) := by
  have h1 : ω ^ (2 ^ (e + 1)) = 1 := by
    rw [pow_succ, pow_mul, hω, neg_one_sq]
  conv_lhs => rw [← Nat.div_add_mod m (2 ^ (e + 1)), pow_add, pow_mul, h1, one_pow, one_mul]

lemma pow_val_add (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (a b : ZMod (2 ^ (e + 1))) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, ← pow_mod_eq e ω hω, pow_add]

lemma pow_val_mul (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (a b : ZMod (2 ^ (e + 1))) :
    ω ^ (a * b).val = ω ^ (a.val * b.val) := by
  rw [ZMod.val_mul, ← pow_mod_eq e ω hω]

lemma sum_char (e : ℕ) (ω : R) (hω : ω ^ (2 ^ e) = -1) (a : ZMod (2 ^ (e + 1))) :
    ∑ t : ZMod (2 ^ (e + 1)), ω ^ (t * a).val = if a = 0 then ((2 ^ (e + 1) : ℕ) : R) else 0 := by
  have e1 : ∑ t : ZMod (2 ^ (e + 1)), ω ^ (t * a).val =
      ∑ k ∈ range (2 ^ (e + 1)), ω ^ (a.val * k) := by
    refine Finset.sum_nbij' (fun t => t.val) (fun k => (k : ZMod (2 ^ (e + 1)))) (fun t _ => ?_)
      (fun k _ => Finset.mem_univ _) (fun t _ => ZMod.natCast_zmod_val t) (fun k hk => ?_)
      (fun t _ => ?_)
    · exact Finset.mem_range.2 (ZMod.val_lt t)
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hk)]
    · rw [pow_val_mul e ω hω, mul_comm]
  rw [e1]
  split_ifs with ha
  · subst ha; simp
  · apply sum_pow_eq_zero e ω hω
    intro hd
    have h1 := ZMod.val_lt a
    have h2 : a.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
    exact h2 (Nat.eq_zero_of_dvd_of_lt hd h1)

/-- **Convolution formula over a ring with principal power-of-two roots** (Lemma 2.3 / (2.1) of
Harvey–van der Hoeven, synthetic case). If `ω i ^ (2 ^ e i) = -1` then `ω i` is a principal
`2^(e i + 1)`-th root of unity and multidimensional cyclic convolution is computed by the
corresponding transforms: `N · (u ∗ v) = F_{ω⁻¹}(F_ω u · F_ω v)` (unnormalised). -/
theorem synthetic_conv {d : ℕ} (e : Fin d → ℕ) (ω : Fin d → R) (hω : ∀ i, ω i ^ (2 ^ e i) = -1)
    (u v : ((i : Fin d) → ZMod (2 ^ (e i + 1))) → R) (j : (i : Fin d) → ZMod (2 ^ (e i + 1))) :
    (∏ i, ((2 ^ (e i + 1) : ℕ) : R)) * ∑ k, u k * v (j - k) =
      ∑ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), (∏ i, ω i ^ (t i * j i).val) *
        ((∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * u k) *
          (∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * v k)) := by
  -- expand the right-hand side
  have hR : ∀ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), (∏ i, ω i ^ (t i * j i).val) *
      ((∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * u k) *
        (∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * v k)) =
      ∑ k, ∑ l, u k * v l * ∏ i, ω i ^ (t i * (j i - k i - l i)).val := by
    intro t
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hc : ∀ i, ω i ^ (t i * (j i - k i - l i)).val =
        ω i ^ (t i * j i).val * (ω i ^ (-(t i * k i)).val * ω i ^ (-(t i * l i)).val) := by
      intro i
      rw [← pow_val_add (e i) (ω i) (hω i), ← pow_val_add (e i) (ω i) (hω i)]
      congr 2; ring
    simp only [hc, Finset.prod_mul_distrib]
    ring
  simp only [hR]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hs : ∀ l : (i : Fin d) → ZMod (2 ^ (e i + 1)),
      ∑ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), ∏ i, ω i ^ (t i * (j i - k i - l i)).val =
        if j - k = l then ∏ i, ((2 ^ (e i + 1) : ℕ) : R) else 0 := by
    intro l
    rw [← Fintype.prod_sum (fun i (x : ZMod (2 ^ (e i + 1))) => ω i ^ (x * (j i - k i - l i)).val)]
    simp only [sum_char _ _ (hω _)]
    rw [Finset.prod_ite_zero]
    congr 1
    apply propext
    constructor
    · intro h; funext i; have := h i (Finset.mem_univ _)
      rw [sub_sub, sub_eq_zero] at this; rw [Pi.sub_apply, this]; ring
    · intro h i _; rw [← h]; simp
  simp only [hs, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

end IntMul.HvdH.Syn

theorem solution {R : Type*} [CommRing R] {d : ℕ} (e : Fin d → ℕ) (ω : Fin d → R) (hω : ∀ i, ω i ^ (2 ^ e i) = -1)
    (u v : ((i : Fin d) → ZMod (2 ^ (e i + 1))) → R) (j : (i : Fin d) → ZMod (2 ^ (e i + 1))) :
    (∏ i, ((2 ^ (e i + 1) : ℕ) : R)) * ∑ k, u k * v (j - k) =
      ∑ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), (∏ i, ω i ^ (t i * j i).val) *
        ((∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * u k) *
          (∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * v k)) :=
  IntMul.HvdH.Syn.synthetic_conv e ω hω u v j
