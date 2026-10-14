-- Prove2me | solution 1 for IntMul.HvdH.fermConv_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:01:22.31793+00:00
-- url     : https://prove2.me/submissions/7157544d-ad4a-4bb6-a668-765a507510d7

import Definitions.Def_IntMul_HvdH_KronMul
import Definitions.Def_IntMul_HvdH_Fermat
import Mathlib
import Definitions.Def_IntMul_HvdH_FermConv

open Finset

namespace IntMul.HvdH.KronPf
open IntMul.HvdH

lemma balanced_digit (B : ℤ) (hBe : Even B) (c W' : ℤ) (hc : 2 * |c| < B) :
    (c + B * W' + B / 2) % B - B / 2 = c := by
  obtain ⟨h, rfl⟩ := hBe
  have hh : (h + h) / 2 = h := by omega
  rw [hh]
  have : (c + (h + h) * W' + h) % (h + h) = c + h := by
    rw [show c + (h + h) * W' + h = (c + h) + (h + h) * W' by ring, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt <;> · have := abs_lt.1 (show |c| < h by omega); omega
  omega

theorem kunpack_kpack (B : ℤ) (hB : 0 < B) (hBe : Even B) (c : List ℤ)
    (hc : ∀ x ∈ c, 2 * |x| < B) : kunpack B c.length (kpack B c) = c := by
  induction c with
  | nil => rfl
  | cons a cs ih =>
    have ha : 2 * |a| < B := hc a (by simp)
    have hcs : ∀ x ∈ cs, 2 * |x| < B := fun x hx => hc x (by simp [hx])
    simp only [List.length_cons, kunpack, kpack]
    have hd : (a + B * kpack B cs + B / 2) % B - B / 2 = a := balanced_digit B hBe a _ ha
    rw [hd]
    have hq : (a + B * kpack B cs - a) / B = kpack B cs := by
      rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hB.ne']
    rw [hq, ih hcs]

lemma kpack_eq_sum (B : ℤ) (c : List ℤ) :
    kpack B c = ∑ i ∈ range c.length, c.getD i 0 * B ^ i := by
  induction c with
  | nil => simp [kpack]
  | cons a cs ih =>
    rw [kpack, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_); ring

/-- The polynomial with coefficient list `c`. -/
noncomputable def toPoly (c : List ℤ) : Polynomial ℤ :=
  ∑ i ∈ range c.length, Polynomial.C (c.getD i 0) * Polynomial.X ^ i

lemma coeff_toPoly (c : List ℤ) (k : ℕ) : (toPoly c).coeff k = c.getD k 0 := by
  unfold toPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hk; simp only [Finset.mem_range, not_lt] at hk
    rw [List.getD_eq_default _ _ hk]; simp

lemma eval_toPoly (B : ℤ) (c : List ℤ) : (toPoly c).eval B = kpack B c := by
  rw [kpack_eq_sum, toPoly, Polynomial.eval_finset_sum]
  simp

lemma toPoly_polyMul (a b : List ℤ) : toPoly (polyMul a b) = toPoly a * toPoly b := by
  ext k
  rw [coeff_toPoly, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_toPoly]
  unfold polyMul
  by_cases hk : k < a.length + b.length - 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  · push Not at hk
    rw [List.getD_eq_default _ _ (by simpa using hk)]
    symm
    refine Finset.sum_eq_zero (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    by_cases hia : i < a.length
    · have : b.length ≤ k - i := by omega
      rw [List.getD_eq_default _ _ this, mul_zero]
    · push Not at hia
      rw [List.getD_eq_default _ _ hia, zero_mul]

theorem kpack_polyMul (B : ℤ) (a b : List ℤ) :
    kpack B (polyMul a b) = kpack B a * kpack B b := by
  rw [← eval_toPoly, ← eval_toPoly, ← eval_toPoly, toPoly_polyMul, Polynomial.eval_mul]

lemma sum_abs_getD_le (a : List ℤ) (M : ℤ) (ha : ∀ x ∈ a, |x| ≤ M) (N : ℕ) :
    ∑ i ∈ range N, |a.getD i 0| ≤ a.length * M := by
  have hz : ∀ i ∈ range N, i ∉ range N ∩ range a.length → |a.getD i 0| = 0 := by
    intro i hi hni
    have : a.length ≤ i := by
      by_contra h; exact hni (Finset.mem_inter.2 ⟨hi, Finset.mem_range.2 (by omega)⟩)
    rw [List.getD_eq_default _ _ this, abs_zero]
  rw [← Finset.sum_subset Finset.inter_subset_left hz]
  calc ∑ i ∈ range N ∩ range a.length, |a.getD i 0| ≤ ∑ i ∈ range a.length, |a.getD i 0| :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i _ _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ range a.length, M := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.1 hi)]
        exact ha _ (List.getElem_mem _)
    _ = a.length * M := by simp

lemma polyMul_coeff_bound (a b : List ℤ) (M : ℤ) (hM0 : 0 ≤ M) (ha : ∀ x ∈ a, |x| ≤ M)
    (hb : ∀ x ∈ b, |x| ≤ M) : ∀ x ∈ polyMul a b, |x| ≤ a.length * M * M := by
  intro x hx
  unfold polyMul at hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  have hM : ∀ j, |b.getD j 0| ≤ M := by
    intro j
    by_cases hj : j < b.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hb _ (List.getElem_mem _)
    · push Not at hj
      rw [List.getD_eq_default _ _ hj, abs_zero]
      exact hM0
  calc |∑ i ∈ range (k + 1), a.getD i 0 * b.getD (k - i) 0|
      ≤ ∑ i ∈ range (k + 1), |a.getD i 0 * b.getD (k - i) 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (k + 1), |a.getD i 0| * M := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    _ = (∑ i ∈ range (k + 1), |a.getD i 0|) * M := by rw [Finset.sum_mul]
    _ ≤ a.length * M * M := by
        exact mul_le_mul_of_nonneg_right (sum_abs_getD_le a M ha _) hM0

lemma polyMul_length (a b : List ℤ) : (polyMul a b).length = a.length + b.length - 1 := by
  simp [polyMul]

theorem kronMul_eq (p r : ℕ) (a b : List ℤ) (ha : a.length = r) (hb : b.length = r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ p) (hbb : ∀ x ∈ b, |x| ≤ 2 ^ p) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p) :
    kronMul p r a b = polyMul a b := by
  have hB : (0 : ℤ) < 2 ^ (3 * p) := by positivity
  have hBe : Even ((2 : ℤ) ^ (3 * p)) := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp at hrp; omega
    · exact (Int.even_pow.2 ⟨even_two, by omega⟩)
  unfold kronMul
  rw [← kpack_polyMul]
  have hlen : 2 * r - 1 = (polyMul a b).length := by rw [polyMul_length, ha, hb]; omega
  rw [hlen]
  refine kunpack_kpack _ hB hBe _ (fun x hx => ?_)
  have h1 := polyMul_coeff_bound a b (2 ^ p) (by positivity) hab hbb x hx
  rw [ha] at h1
  have hrp' : (2 : ℤ) * r < 2 ^ p := by exact_mod_cast hrp
  have : (2 : ℤ) ^ (3 * p) = 2 ^ p * 2 ^ p * 2 ^ p := by ring
  rw [this]
  have hp0 : (0 : ℤ) < 2 ^ p := by positivity
  nlinarith [mul_pos hp0 hp0]

theorem mulR_eq_spec (p r : ℕ) (U0 U1 V0 V1 : List ℤ)
    (h0 : U0.length = r) (h1 : U1.length = r) (h2 : V0.length = r) (h3 : V1.length = r)
    (hU0 : ∀ x ∈ U0, |x| ≤ 2 ^ p) (hU1 : ∀ x ∈ U1, |x| ≤ 2 ^ p)
    (hV0 : ∀ x ∈ V0, |x| ≤ 2 ^ p) (hV1 : ∀ x ∈ V1, |x| ≤ 2 ^ p) (hr : 1 ≤ r)
    (hrp : 2 * r < 2 ^ p) :
    mulR p r U0 U1 V0 V1 = mulRSpec p r U0 U1 V0 V1 := by
  unfold mulR mulRSpec
  rw [kronMul_eq p r U0 V0 h0 h2 hU0 hV0 hr hrp, kronMul_eq p r U1 V1 h1 h3 hU1 hV1 hr hrp,
    kronMul_eq p r U0 V1 h0 h3 hU0 hV1 hr hrp, kronMul_eq p r U1 V0 h1 h2 hU1 hV0 hr hrp]

end IntMul.HvdH.KronPf


open Finset

namespace IntMul.HvdH.FermPf
open IntMul.HvdH IntMul.HvdH.KronPf

lemma negFold_length (n : ℕ) (l : List ℤ) : (negFold n l).length = n := by simp [negFold]

lemma negFold_getD (n : ℕ) (l : List ℤ) (i : ℕ) (hi : i < n) :
    (negFold n l).getD i 0 = l.getD i 0 - l.getD (i + n) 0 := by
  simp [negFold, List.getD_eq_getElem?_getD, hi]

/-- `kpack` of the negacyclic fold differs from `kpack` of the list by a multiple of `B^n + 1`. -/
lemma kpack_negFold (B : ℤ) (n : ℕ) (l : List ℤ) (hl : l.length ≤ 2 * n) :
    kpack B l = kpack B (negFold n l) +
      (B ^ n + 1) * ∑ i ∈ range n, l.getD (i + n) 0 * B ^ i := by
  rw [kpack_eq_sum, kpack_eq_sum, negFold_length]
  have h1 : ∑ i ∈ range l.length, l.getD i 0 * B ^ i = ∑ i ∈ range (2 * n), l.getD i 0 * B ^ i := by
    apply Finset.sum_subset (Finset.range_mono hl)
    intro i hi hni
    rw [List.getD_eq_default _ _ (by simpa using hni), zero_mul]
  rw [h1, two_mul, Finset.sum_range_add]
  have hN : ∑ i ∈ range n, (negFold n l).getD i 0 * B ^ i =
      ∑ i ∈ range n, (l.getD i 0 - l.getD (i + n) 0) * B ^ i :=
    Finset.sum_congr rfl (fun i hi => by rw [negFold_getD n l i (Finset.mem_range.1 hi)])
  rw [hN]
  simp_rw [sub_mul, Finset.sum_sub_distrib, add_mul, one_mul, Finset.mul_sum]
  have : ∀ i ∈ range n, l.getD (n + i) 0 * B ^ (n + i) = B ^ n * (l.getD (i + n) 0 * B ^ i) := by
    intro i _; rw [add_comm n i, pow_add]; ring
  rw [Finset.sum_congr rfl this]
  ring

lemma kpack_abs (B : ℤ) (hB : 0 < B) (c : List ℤ) (hc : ∀ x ∈ c, 2 * |x| < B) :
    2 * |kpack B c| ≤ B ^ c.length - 1 := by
  induction c with
  | nil => simp [kpack]
  | cons a cs ih =>
    have ha : 2 * |a| < B := hc a (by simp)
    have ih' := ih (fun x hx => hc x (by simp [hx]))
    simp only [kpack, List.length_cons]
    calc 2 * |a + B * kpack B cs| ≤ 2 * |a| + B * (2 * |kpack B cs|) := by
          have := abs_add_le a (B * kpack B cs)
          rw [abs_mul, abs_of_pos hB] at this; linarith
      _ ≤ (B - 1) + B * (B ^ cs.length - 1) := by gcongr; omega
      _ = B ^ (cs.length + 1) - 1 := by ring

lemma balMod_eq (F x y : ℤ) (hF : 0 < F) (hodd : Odd F) (hxy : x % F = y % F)
    (hy : 2 * |y| < F) : balMod F x = y := by
  unfold balMod
  have hc0 : 0 ≤ x % F := Int.emod_nonneg _ hF.ne'
  have hc1 : x % F < F := Int.emod_lt_of_pos _ hF
  have hy' := abs_lt.1 (show |y| < F by linarith [abs_nonneg y])
  have hd : F ∣ x % F - y := by
    rw [hxy, Int.emod_def]; exact ⟨-(y / F), by ring⟩
  obtain ⟨k, hk⟩ := hodd
  dsimp only
  split_ifs with h
  · have hd' : F ∣ (x % F - F) - y := by
      rw [show x % F - F - y = (x % F - y) - F by ring]; exact dvd_sub hd dvd_rfl
    have := Int.eq_zero_of_abs_lt_dvd hd' (by
      rw [abs_lt]; constructor
      · have := le_abs_self y; have := neg_abs_le y; omega
      · have := le_abs_self y; have := neg_abs_le y; omega)
    linarith
  · have := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]; constructor
      · have := le_abs_self y; have := neg_abs_le y; omega
      · have := le_abs_self y; have := neg_abs_le y; omega)
    linarith

/-- **Fermat-ring negacyclic multiplication.** For lists `u, v` of length `n ≥ 1` with entries
bounded by `M`, `P ≥ 1` and `4 n M² < 2^P`, one multiplication modulo `2^{nP} + 1` followed by balanced
digit extraction returns the exact product in `ℤ[y]/(yⁿ + 1)`. -/
theorem fermatNegaMul_eq (P n : ℕ) (u v : List ℤ) (M : ℤ) (hn : 1 ≤ n) (hP1 : 1 ≤ P)
    (hu : u.length = n) (hv : v.length = n) (hM0 : 0 ≤ M)
    (hub : ∀ x ∈ u, |x| ≤ M) (hvb : ∀ x ∈ v, |x| ≤ M) (hP : 4 * n * M ^ 2 < 2 ^ P) :
    fermatNegaMul P n u v = negFold n (polyMul u v) := by
  set B : ℤ := 2 ^ P
  set F : ℤ := B ^ n + 1
  have hB : 0 < B := by positivity
  have hBe : Even B := by simp only [B]; exact Int.even_pow.2 ⟨even_two, by omega⟩
  have hF : 0 < F := by positivity
  have hFodd : Odd F := by
    simp only [F]; exact (Int.even_pow.2 ⟨hBe, by omega⟩).add_one
  set w := negFold n (polyMul u v)
  have hlen : (polyMul u v).length ≤ 2 * n := by rw [polyMul_length]; omega
  have hcoef := polyMul_coeff_bound u v M hM0 hub hvb
  have hw : ∀ x ∈ w, 2 * |x| < B := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [negFold_length] at hi
    rw [← List.getD_eq_getElem _ 0 (by rwa [negFold_length]), negFold_getD n _ i hi]
    have hb : ∀ j, |(polyMul u v).getD j 0| ≤ n * M * M := by
      intro j
      by_cases hj : j < (polyMul u v).length
      · rw [List.getD_eq_getElem _ _ hj, ← hu]; exact hcoef _ (List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega), abs_zero]; positivity
    have := abs_sub ((polyMul u v).getD i 0) ((polyMul u v).getD (i + n) 0)
    have h1 := hb i; have h2 := hb (i + n)
    nlinarith
  have hkw := kpack_abs B hB w hw
  rw [negFold_length] at hkw
  have hcong : (kpack B u % F) * (kpack B v % F) % F % F = kpack B w % F := by
    rw [Int.emod_emod_of_dvd _ dvd_rfl, ← Int.mul_emod, ← kpack_polyMul, kpack_negFold B n _ hlen,
      Int.add_mul_emod_self_left]
  show kunpack B n (balMod F ((kpack B u % F) * (kpack B v % F) % F)) = w
  rw [balMod_eq F _ (kpack B w) hF hFodd hcong (by simp only [F]; omega)]
  have := kunpack_kpack B hB hBe w hw
  rwa [negFold_length] at this

end IntMul.HvdH.FermPf


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


open Finset

namespace IntMul.HvdH.FCPf
open IntMul.HvdH IntMul.HvdH.KronPf IntMul.HvdH.FermPf

/-- Orthogonality for `ω` with `ω^{2^{e-1}} = -1` over any commutative ring. -/
lemma orth_nat {R : Type*} [CommRing R] (e : ℕ) (he : 1 ≤ e) (ω : R) (hω : ω ^ (2 ^ (e - 1)) = -1)
    (a : ℕ) : ∑ m ∈ range (2 ^ e), ω ^ (a * m) = if 2 ^ e ∣ a then ((2 ^ e : ℕ) : R) else 0 := by
  have he' : e = (e - 1) + 1 := by omega
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    have h1 : ω ^ (2 ^ e) = 1 := by
      rw [he', pow_succ, pow_mul, hω]; norm_num
    have : ∀ m ∈ range (2 ^ e), ω ^ (2 ^ e * q * m) = 1 := by
      intro m _; rw [mul_assoc, pow_mul, h1, one_pow]
    rw [Finset.sum_congr rfl this]; simp
  · rw [he']
    exact IntMul.HvdH.Syn.sum_pow_eq_zero (e - 1) ω hω a (by rwa [← he'])

/-- The target index of the cyclic convolution. -/
def tgt {d : ℕ} (t : Fin d → ℕ) (j k : Fin d → ℕ) : Fin d → ℕ := fun i => (j i + t i - k i) % t i

lemma dvd_iff_tgt (t j k l : ℕ) (hj : j < t) (hk : k < t) (hl : l < t) :
    t ∣ j * (t - 1) + k + l ↔ l = (j + t - k) % t := by
  have ht : 0 < t := by omega
  set g := (j + t - k) % t with hg
  have hgt : g < t := Nat.mod_lt _ ht
  have e1 : (j + t - k) = t * ((j + t - k) / t) + g := (Nat.div_add_mod _ _).symm
  have key : ((j * (t - 1) + k + l : ℕ) : ℤ) = ((l : ℤ) - g) + t * (j + 1 - (j + t - k) / t : ℤ) := by
    have e2 : ((j + t - k : ℕ) : ℤ) = (t : ℤ) * (((j + t - k) / t : ℕ) : ℤ) + g := by exact_mod_cast e1
    push_cast [Nat.cast_sub (show k ≤ j + t by omega), Nat.cast_sub (show 1 ≤ t by omega)] at e2 ⊢
    linear_combination -e2
  rw [← Int.natCast_dvd_natCast, key, dvd_add_left (dvd_mul_right _ _)]
  constructor
  · intro h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  · intro h; rw [h, sub_self]; exact dvd_zero _

lemma conv_nat {R : Type*} [CommRing R] {d : ℕ} (t : Fin d → ℕ) (ω : Fin d → R)
    (horth : ∀ i (a : ℕ), ∑ m ∈ range (t i), ω i ^ (a * m) = if t i ∣ a then ((t i : ℕ) : R) else 0)
    (X Y : (Fin d → ℕ) → R) (j : Fin d → ℕ) (hj : ∀ i, j i < t i) :
    ∑ m ∈ Fintype.piFinset (fun i => range (t i)),
      (∏ i, ω i ^ (m i * j i * (t i - 1))) *
        ((∑ k ∈ Fintype.piFinset (fun i => range (t i)), (∏ i, ω i ^ (m i * k i)) * X k) *
          (∑ l ∈ Fintype.piFinset (fun i => range (t i)), (∏ i, ω i ^ (m i * l i)) * Y l)) =
      (∏ i, ((t i : ℕ) : R)) * ∑ k ∈ Fintype.piFinset (fun i => range (t i)), X k * Y (tgt t j k) := by
  classical
  set box := Fintype.piFinset (fun i => range (t i))
  have h1 : ∀ m : Fin d → ℕ, (∏ i, ω i ^ (m i * j i * (t i - 1))) *
      ((∑ k ∈ box, (∏ i, ω i ^ (m i * k i)) * X k) * (∑ l ∈ box, (∏ i, ω i ^ (m i * l i)) * Y l)) =
      ∑ k ∈ box, ∑ l ∈ box, X k * Y l * ∏ i, ω i ^ ((j i * (t i - 1) + k i + l i) * m i) := by
    intro m
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    have : ∏ i, ω i ^ ((j i * (t i - 1) + k i + l i) * m i) =
        (∏ i, ω i ^ (m i * j i * (t i - 1))) * (∏ i, ω i ^ (m i * k i)) * ∏ i, ω i ^ (m i * l i) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rw [← pow_add, ← pow_add]; congr 1; ring
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k hk
  rw [Finset.sum_comm]
  have hk' : ∀ i, k i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hk i)
  have h2 : ∀ l ∈ box, ∑ m ∈ box, X k * Y l * ∏ i, ω i ^ ((j i * (t i - 1) + k i + l i) * m i) =
      X k * Y l * (if l = tgt t j k then ∏ i, ((t i : ℕ) : R) else 0) := by
    intro l hl
    have hl' : ∀ i, l i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hl i)
    rw [← Finset.mul_sum]
    congr 1
    rw [show box = Fintype.piFinset (fun i => range (t i)) from rfl,
      ← Finset.prod_univ_sum (fun i => range (t i))
        (fun i mi => ω i ^ ((j i * (t i - 1) + k i + l i) * mi))]
    simp only [horth]
    rw [Fintype.prod_ite_zero (p := fun i => t i ∣ j i * (t i - 1) + k i + l i)
      (f := fun i => ((t i : ℕ) : R))]
    have hiff : (∀ i, t i ∣ j i * (t i - 1) + k i + l i) ↔ l = tgt t j k := by
      rw [funext_iff]
      exact forall_congr' (fun i => dvd_iff_tgt (t i) (j i) (k i) (l i) (hj i) (hk' i) (hl' i))
    by_cases h : l = tgt t j k
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (mt hiff.1 h), if_neg h]
  rw [Finset.sum_congr rfl h2]
  simp only [mul_ite, mul_zero]
  have htgt : tgt t j k ∈ box := by
    rw [Fintype.mem_piFinset]; intro i
    exact Finset.mem_range.2 (Nat.mod_lt _ (by have := hj i; omega))
  rw [Finset.sum_ite_eq' box (tgt t j k), if_pos htgt]
  ring

lemma polyMul_getD_all (a b : List ℤ) (c : ℕ) :
    (polyMul a b).getD c 0 = ∑ i ∈ range (c + 1), a.getD i 0 * b.getD (c - i) 0 := by
  by_cases hc : c < (polyMul a b).length
  · rw [List.getD_eq_getElem _ _ hc]
    simp [polyMul]
  · rw [List.getD_eq_default _ _ (by omega)]
    rw [polyMul_length] at hc
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.1 hi
    by_cases ha : i < a.length
    · rw [List.getD_eq_default b 0 (show b.length ≤ c - i by omega), mul_zero]
    · rw [List.getD_eq_default a 0 (by omega), zero_mul]

lemma fold_eq (a b : List ℤ) (r : ℕ) (ha : a.length = r) (hb : b.length = r) (c : ℕ) (hc : c < r) :
    (polyMul a b).getD c 0 + (polyMul a b).getD (c + r) 0 =
      ∑ i ∈ range r, a.getD i 0 * b.getD ((c + r - i) % r) 0 := by
  rw [polyMul_getD_all, polyMul_getD_all]
  rw [← Finset.sum_range_add_sum_Ico _ (show c + 1 ≤ r by omega)]
  rw [← Finset.sum_range_add_sum_Ico _ (show c + 1 ≤ c + r + 1 by omega),
    ← Finset.sum_Ico_consecutive _ (show c + 1 ≤ r by omega) (show r ≤ c + r + 1 by omega)]
  have z1 : ∑ i ∈ range (c + 1), a.getD i 0 * b.getD (c + r - i) 0 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have := Finset.mem_range.1 hi
    rw [List.getD_eq_default b 0 (by omega), mul_zero]
  have z2 : ∑ i ∈ Ico r (c + r + 1), a.getD i 0 * b.getD (c + r - i) 0 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have := (Finset.mem_Ico.1 hi).1
    rw [List.getD_eq_default a 0 (by omega), zero_mul]
  rw [z1, z2, zero_add, add_zero]
  congr 1
  · apply Finset.sum_congr rfl; intro i hi
    have := Finset.mem_range.1 hi
    rw [show (c + r - i) % r = c - i by
      rw [show c + r - i = (c - i) + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
  · apply Finset.sum_congr rfl; intro i hi
    have := Finset.mem_Ico.1 hi
    rw [Nat.mod_eq_of_lt (show c + r - i < r by omega)]

lemma rowList_getD {d : ℕ} (r : ℕ) (x : (Fin (d + 1) → ℕ) → ℤ) (k : Fin d → ℕ) (i : ℕ) (hi : i < r) :
    (rowList r x k).getD i 0 = x (Fin.snoc k i) := by
  simp [rowList, List.getD_eq_getElem?_getD, hi]

lemma rowList_length {d : ℕ} (r : ℕ) (x : (Fin (d + 1) → ℕ) → ℤ) (k : Fin d → ℕ) :
    (rowList r x k).length = r := by simp [rowList]

lemma rowList_bound {d : ℕ} (r : ℕ) (x : (Fin (d + 1) → ℕ) → ℤ) (M : ℤ) (k : Fin d → ℕ)
    (hx : ∀ c < r, |x (Fin.snoc k c)| ≤ M) : ∀ z ∈ rowList r x k, |z| ≤ M := by
  intro z hz
  simp only [rowList, List.mem_map, List.mem_range] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  exact hx c hc

/-- Casting `kpack` into any ring evaluates the list at the cast of the base. -/
lemma kpack_cast {A : Type*} [CommRing A] (B : ℤ) (l : List ℤ) :
    ((kpack B l : ℤ) : A) = ∑ i ∈ range l.length, ((l.getD i 0 : ℤ) : A) * ((B : ℤ) : A) ^ i := by
  rw [kpack_eq_sum]; push_cast; rfl

lemma pow_sum_split {A : Type*} [CommRing A] {d : ℕ} (P : ℕ) (f : Fin d → ℕ) :
    (2 : A) ^ (P * ∑ i, f i) = ∏ i, ((2 : A) ^ P) ^ (f i) := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]

theorem fermConv_eq {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (x y : (Fin (d + 1) → ℕ) → ℤ) (M : ℤ) (hM0 : 0 ≤ M)
    (hx : ∀ z : Fin (d + 1) → ℕ, (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |x z| ≤ M)
    (hy : ∀ z : Fin (d + 1) → ℕ, (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |y z| ≤ M)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * M ^ 2 < (2 : ℤ) ^ P)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    fermConv P r e x y j =
      ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)), ∑ c ∈ Finset.range r,
        x (Fin.snoc (fun i => k i) c) *
          y (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
            ((j (Fin.last d) + r - c) % r)) := by
  classical
  set B : ℤ := 2 ^ P with hB
  set T : ℕ := 2 ^ (∑ i, e i) with hT
  set t : Fin d → ℕ := fun i => 2 ^ e i with ht
  set box := Fintype.piFinset (fun i => range (t i))
  set jj : Fin d → ℕ := Fin.init j
  have hjj : ∀ i, jj i < t i := fun i => hj i
  set tg := tgt t jj
  set pm : (Fin d → ℕ) → List ℤ := fun k => polyMul (rowList r x k) (rowList r y (tg k))
  set Lc : List ℤ := (List.range (2 * r)).map (fun c => (T : ℤ) * ∑ k ∈ box, (pm k).getD c 0)
  have hBpos : 0 < B := by positivity
  have hBe : Even B := Int.even_pow.2 ⟨even_two, by omega⟩
  have hFz : fermMod P r = B ^ (2 * r) + 1 := by
    simp only [fermMod, B]; rw [← pow_mul]; ring_nf
  have hLclen : Lc.length = 2 * r := by simp [Lc]
  have hLcget : ∀ c < 2 * r, Lc.getD c 0 = (T : ℤ) * ∑ k ∈ box, (pm k).getD c 0 := by
    intro c hc'; simp [Lc, List.getD_eq_getElem?_getD, hc']
  have hpmlen : ∀ k, (pm k).length = 2 * r - 1 := by
    intro k; simp only [pm]; rw [polyMul_length, rowList_length, rowList_length]; omega
  -- coefficient bounds
  have hrow : ∀ (w : (Fin (d + 1) → ℕ) → ℤ), (∀ z : Fin (d + 1) → ℕ,
      (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |w z| ≤ M) →
      ∀ k : Fin d → ℕ, (∀ i, k i < t i) → ∀ c < r, |w (Fin.snoc k c)| ≤ M := by
    intro w hw k hk c hc'
    exact hw _ (fun i => by simpa using hk i) (by simpa using hc')
  have hpmb : ∀ k ∈ box, ∀ c, |(pm k).getD c 0| ≤ r * M * M := by
    intro k hkb c
    have hk : ∀ i, k i < t i := fun i => Finset.mem_range.1 (Fintype.mem_piFinset.1 hkb i)
    have htk : ∀ i, tg k i < t i := fun i => Nat.mod_lt _ (by simp only [t]; positivity)
    by_cases hcl : c < (pm k).length
    · rw [List.getD_eq_getElem _ _ hcl]
      have := polyMul_coeff_bound (rowList r x k) (rowList r y (tg k)) M hM0
        (rowList_bound r x M k (hrow x hx k hk)) (rowList_bound r y M (tg k) (hrow y hy _ htk)) _
        (List.getElem_mem hcl)
      rwa [rowList_length] at this
    · rw [List.getD_eq_default _ _ (by omega), abs_zero]; positivity
  have hcard : (box.card : ℤ) = T := by
    simp only [box, Fintype.card_piFinset, Finset.card_range, t, T]
    rw [Finset.prod_pow_eq_pow_sum]
  have hLcb : ∀ z ∈ Lc, 2 * |z| < B := by
    intro z hz
    obtain ⟨c, hc', rfl⟩ := List.mem_iff_getElem.1 hz
    rw [hLclen] at hc'
    rw [← List.getD_eq_getElem _ 0, hLcget c hc', abs_mul]
    have h1 : |∑ k ∈ box, (pm k).getD c 0| ≤ T * (r * M * M) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (fun k hk => hpmb k hk c)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hT0 : (0 : ℤ) ≤ T := by positivity
    rw [abs_of_nonneg hT0]
    calc 2 * ((T : ℤ) * |∑ k ∈ box, (pm k).getD c 0|) ≤ 2 * (T * (T * (r * M * M))) := by gcongr
      _ = 2 * (2 ^ (∑ i, e i)) ^ 2 * r * M ^ 2 := by simp only [T]; push_cast; ring
      _ < B := hPM
  -- the congruence `Z ≡ kpack B Lc` modulo `2^{2rP} + 1`
  set Fn : ℕ := 2 ^ (2 * r * P) + 1
  have hFn : (Fn : ℤ) = fermMod P r := by simp only [Fn, fermMod]; push_cast; ring
  set Z := fermIdft P r e
    (fun m => fermDft P r e (fermPack P r x) m * fermDft P r e (fermPack P r y) m % fermMod P r) jj
  have hcongr : ((Z : ℤ) : ZMod Fn) = ((kpack B Lc : ℤ) : ZMod Fn) := by
    have hm : ∀ z : ℤ, ((z % fermMod P r : ℤ) : ZMod Fn) = (z : ZMod Fn) := by
      intro z; rw [← hFn, ZMod.intCast_mod]
    set ζ : ZMod Fn := (2 : ZMod Fn) ^ P
    have hζ : ζ ^ (2 * r) = -1 := by
      have h0 : ((Fn : ℕ) : ZMod Fn) = 0 := ZMod.natCast_self Fn
      simp only [Fn] at h0; push_cast at h0
      rw [← pow_mul, show P * (2 * r) = 2 * r * P by ring]
      exact eq_neg_of_add_eq_zero_left h0
    set ω : Fin d → ZMod Fn := fun i => ζ ^ (4 * r / 2 ^ e i)
    have hωh : ∀ i, ω i ^ (2 ^ (e i - 1)) = -1 := by
      intro i
      simp only [ω]; rw [← pow_mul]
      have h2 : 4 * r / 2 ^ e i * 2 ^ (e i - 1) = 2 * r := by
        obtain ⟨q, hq⟩ := he i
        have hpos : 0 < 2 ^ e i := by positivity
        have h4 : 4 * r = 2 ^ e i * (2 * q) := by
          rw [show 4 * r = 2 * (2 * r) by ring, hq]; ring
        rw [h4, Nat.mul_div_cancel_left _ hpos]
        have : 2 ^ e i = 2 * 2 ^ (e i - 1) := by
          rw [← pow_succ']; congr 1; have := he1 i; omega
        rw [this] at hq; rw [hq]; ring
      rw [h2, hζ]
    have horth : ∀ i (a : ℕ), ∑ m ∈ range (t i), ω i ^ (a * m) =
        if t i ∣ a then ((t i : ℕ) : ZMod Fn) else 0 :=
      fun i a => orth_nat (e i) (he1 i) (ω i) (hωh i) a
    have hpow : ∀ (f : Fin d → ℕ → ℕ), (2 : ZMod Fn) ^ (P * ∑ i, 4 * r / 2 ^ e i * f i (0)) =
        ∏ i, ω i ^ (f i 0) := by
      intro f
      rw [pow_sum_split]; apply Finset.prod_congr rfl; intro i _
      simp only [ω, ζ, ← pow_mul, mul_assoc]
    have hDft : ∀ (X : (Fin d → ℕ) → ℤ) (m : Fin d → ℕ), ((fermDft P r e X m : ℤ) : ZMod Fn) =
        ∑ k ∈ box, (∏ i, ω i ^ (m i * k i)) * ((X k : ℤ) : ZMod Fn) := by
      intro X m
      unfold fermDft; rw [hm]; push_cast
      apply Finset.sum_congr rfl; intro k _
      congr 1
      exact hpow (fun i _ => m i * k i)
    have hZ : ((Z : ℤ) : ZMod Fn) = ∑ m ∈ box, (∏ i, ω i ^ (m i * jj i * (t i - 1))) *
        ((∑ k ∈ box, (∏ i, ω i ^ (m i * k i)) * ((fermPack P r x k : ℤ) : ZMod Fn)) *
          (∑ l ∈ box, (∏ i, ω i ^ (m i * l i)) * ((fermPack P r y l : ℤ) : ZMod Fn))) := by
      simp only [Z]; unfold fermIdft; rw [hm]; push_cast
      apply Finset.sum_congr rfl; intro m _
      rw [hm, Int.cast_mul, hDft, hDft]
      congr 1
      exact hpow (fun i _ => m i * jj i * (2 ^ e i - 1))
    rw [hZ, conv_nat t ω horth _ _ jj hjj]
    have hpack : ∀ (w : (Fin (d + 1) → ℕ) → ℤ) k, ((fermPack P r w k : ℤ) : ZMod Fn) =
        ((kpack B (rowList r w k) : ℤ) : ZMod Fn) := by
      intro w k; unfold fermPack; rw [hm]
    simp_rw [hpack, ← Int.cast_mul, ← kpack_polyMul]
    -- kpack of Lc
    have hkL : kpack B Lc = (T : ℤ) * ∑ k ∈ box, kpack B (pm k) := by
      have hk : ∀ k, kpack B (pm k) = ∑ c ∈ range (2 * r), (pm k).getD c 0 * B ^ c := by
        intro k; rw [kpack_eq_sum, hpmlen]
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro c _ hnc
        rw [List.getD_eq_default _ _ (by rw [hpmlen]; simpa using hnc)]; ring
      simp_rw [hk]
      rw [kpack_eq_sum, hLclen]
      rw [Finset.sum_congr rfl (fun c hc => by rw [hLcget c (Finset.mem_range.1 hc)])]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro c _
      ring
    · rw [hkL]; push_cast
      congr 1
      · simp only [t, T]; push_cast; rw [Finset.prod_pow_eq_pow_sum]
  have hZmod : Z % fermMod P r = kpack B Lc % fermMod P r := by
    rw [← hFn]; exact (ZMod.intCast_eq_intCast_iff' _ _ _).1 hcongr
  have hkLb := kpack_abs B hBpos Lc hLcb
  rw [hLclen] at hkLb
  have hbal : balMod (fermMod P r) Z = kpack B Lc :=
    balMod_eq _ Z _ (by rw [hFz]; positivity)
      (by rw [hFz]; exact (Int.even_pow.2 ⟨hBe, by omega⟩).add_one) hZmod (by rw [hFz]; omega)
  have hunpack : kunpack B (2 * r) (kpack B Lc) = Lc := by
    have := kunpack_kpack B hBpos hBe Lc hLcb; rwa [hLclen] at this
  -- assemble
  show ((kunpack (2 ^ P) (2 * r) (balMod (fermMod P r) Z)).getD (j (Fin.last d)) 0 +
      (kunpack (2 ^ P) (2 * r) (balMod (fermMod P r) Z)).getD (j (Fin.last d) + r) 0) /
        2 ^ (∑ i, e i) = _
  rw [hbal, hunpack, hLcget _ (by omega), hLcget _ (by omega), ← mul_add, ← Finset.sum_add_distrib]
  have hfold : ∀ k ∈ box, (pm k).getD (j (Fin.last d)) 0 + (pm k).getD (j (Fin.last d) + r) 0 =
      ∑ c ∈ range r, x (Fin.snoc (fun i => k i) c) *
        y (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i) ((j (Fin.last d) + r - c) % r)) := by
    intro k _
    simp only [pm]
    rw [fold_eq _ _ r (rowList_length r x k) (rowList_length r y _) _ hc]
    apply Finset.sum_congr rfl; intro c hcr
    rw [rowList_getD r x k c (Finset.mem_range.1 hcr),
      rowList_getD r y _ _ (Nat.mod_lt _ (by omega))]
    rfl
  rw [Finset.sum_congr rfl hfold]
  have hT0 : (2 : ℤ) ^ (∑ i, e i) ≠ 0 := by positivity
  rw [show ((T : ℕ) : ℤ) = 2 ^ (∑ i, e i) by simp [T], Int.mul_ediv_cancel_left _ hT0]

end IntMul.HvdH.FCPf


open IntMul.HvdH

theorem solution {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (x y : (Fin (d + 1) → ℕ) → ℤ) (M : ℤ) (hM0 : 0 ≤ M)
    (hx : ∀ z : Fin (d + 1) → ℕ, (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |x z| ≤ M)
    (hy : ∀ z : Fin (d + 1) → ℕ, (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |y z| ≤ M)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * M ^ 2 < (2 : ℤ) ^ P)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    fermConv P r e x y j =
      ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)), ∑ c ∈ Finset.range r,
        x (Fin.snoc (fun i => k i) c) *
          y (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
            ((j (Fin.last d) + r - c) % r)) := IntMul.HvdH.FCPf.fermConv_eq P r e hr hP he1 he x y M hM0 hx hy hPM j hj hc
