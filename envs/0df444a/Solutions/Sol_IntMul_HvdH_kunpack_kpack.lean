-- Prove2me | solution 1 for IntMul.HvdH.kunpack_kpack
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T22:50:51.864641+00:00
-- url     : https://prove2.me/submissions/e67ab914-fa32-4dd4-bf91-55faabd6b819

import Definitions.Def_IntMul_HvdH_KronMul

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

open IntMul.HvdH in
theorem solution (B : ℤ) (hB : 0 < B) (hBe : Even B) (c : List ℤ)
    (hc : ∀ x ∈ c, 2 * |x| < B) : kunpack B c.length (kpack B c) = c :=
  IntMul.HvdH.KronPf.kunpack_kpack B hB hBe c hc
