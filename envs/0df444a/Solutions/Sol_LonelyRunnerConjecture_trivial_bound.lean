-- Prove2me | solution 1 for LonelyRunnerConjecture.trivial_bound
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:49:38.658659+00:00
-- url     : https://prove2.me/submissions/d9d40e87-aeb8-4153-8107-dd7d5fb06f09

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

open Finset LonelyRunnerConjecture

lemma mul_mod_eq (j v Q : ℕ) (hv : 0 < v) : (j * v) % (Q * v) = (j % Q) * v := by
  rw [Nat.mul_mod_mul_right]

lemma bad_card (k a v : ℕ) (hk : 1 ≤ k) (hv : 0 < v) (ha : 0 < a) :
    ((range (2 * k * a * v)).filter (fun j => (j * v) % (2 * k * a * v) < a * v ∨
      2 * k * a * v - a * v < (j * v) % (2 * k * a * v))).card ≤ 2 * (a * v) - 1 := by
  set Q := 2 * k * a with hQ
  have hN : 2 * k * a * v = Q * v := by rw [hQ]
  rw [hN]
  simp_rw [mul_mod_eq _ v Q hv]
  -- inject into range v ×ˢ badS
  set badS := (range Q).filter (fun s => s * v < a * v ∨ Q * v - a * v < s * v) with hbadS
  have hinj : ((range (Q * v)).filter (fun j => (j % Q) * v < a * v ∨
      Q * v - a * v < (j % Q) * v)).card ≤ (range v ×ˢ badS).card := by
    apply card_le_card_of_injOn (fun j => (j / Q, j % Q))
    · intro j hj
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hj
      simp only [coe_product, coe_range, hbadS, coe_filter, mem_range, Set.mem_prod, Set.mem_Iio,
        Set.mem_setOf_eq]
      have hQ0 : 0 < Q := by rw [hQ]; positivity
      refine ⟨?_, Nat.mod_lt _ hQ0, hj.2⟩
      rw [Nat.div_lt_iff_lt_mul hQ0]; linarith [hj.1]
    · intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      rw [← Nat.div_add_mod x Q, ← Nat.div_add_mod y Q, hxy.1, hxy.2]
  have hS1 : (badS).card ≤ 2 * a - 1 := by
    have hsub : badS ⊆ range a ∪ Ioo (Q - a) Q := by
      intro s hs
      simp only [hbadS, mem_filter, mem_range] at hs
      simp only [mem_union, mem_range, mem_Ioo]
      rcases hs.2 with h | h
      · left; exact lt_of_mul_lt_mul_right h (Nat.zero_le v)
      · right
        refine ⟨?_, hs.1⟩
        have : (Q - a) * v < s * v := by rw [Nat.sub_mul]; exact h
        exact lt_of_mul_lt_mul_right this (Nat.zero_le v)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    rw [card_range, Nat.card_Ioo]
    have : a ≤ Q := by rw [hQ]; nlinarith
    omega
  calc _ ≤ (range v ×ˢ badS).card := hinj
    _ = v * badS.card := by rw [card_product, card_range]
    _ ≤ v * (2 * a - 1) := Nat.mul_le_mul_left _ hS1
    _ ≤ 2 * (a * v) - 1 := by
        have : 1 ≤ v := hv
        have h2a : 1 ≤ 2 * a := by omega
        rw [Nat.mul_sub, mul_one]
        have : v * (2 * a) = 2 * (a * v) := by ring
        omega

theorem solution (k : ℕ) (hk : 1 ≤ k) (S : Finset ℕ) (hS : S.card = k)
    (hpos : ∀ v ∈ S, 0 < v) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (2 * k : ℝ) ≤ distToNearestInt (t * (v : ℝ)) := by
  classical
  set P := ∏ v ∈ S, v with hP
  have hP0 : 0 < P := Finset.prod_pos hpos
  set N := 2 * k * P with hN
  have hN0 : 0 < N := by positivity
  let Bad : ℕ → Finset ℕ := fun v => (range N).filter (fun j => (j * v) % N < P ∨ N - P < (j * v) % N)
  have hBad : ∀ v ∈ S, (Bad v).card ≤ 2 * P - 1 := by
    intro v hv
    obtain ⟨a, ha⟩ : v ∣ P := Finset.dvd_prod_of_mem _ hv
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, mul_zero] at ha; omega
      · exact h
    have hPa : P = a * v := by rw [ha]; ring
    have hNa : N = 2 * k * a * v := by rw [hN, hPa]; ring
    have := bad_card k a v hk (hpos v hv) ha0
    simp only [Bad]
    rw [hNa, hPa]; exact this
  have hunion : (S.biUnion Bad).card < (range N).card := by
    calc (S.biUnion Bad).card ≤ ∑ v ∈ S, (Bad v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S, (2 * P - 1) := sum_le_sum hBad
      _ = k * (2 * P - 1) := by rw [sum_const, hS, smul_eq_mul]
      _ < (range N).card := by rw [card_range, hN]; have : 1 ≤ 2 * P := by omega
                               have : 0 < k := hk
                               rw [Nat.mul_sub, mul_one]; nlinarith [Nat.sub_lt (by nlinarith : 0 < k * (2 * P)) this]
  obtain ⟨j, hjN, hjnot⟩ := exists_mem_notMem_of_card_lt_card hunion
  refine ⟨(j : ℝ) / N, fun v hv => ?_⟩
  have hjv : j ∉ Bad v := fun h => hjnot (mem_biUnion.mpr ⟨v, hv, h⟩)
  simp only [Bad, mem_filter, not_and, not_or, not_lt] at hjv
  obtain ⟨h1, h2⟩ := hjv (by simpa using hjN)
  set r := (j * v) % N with hr
  have hrN : r < N := Nat.mod_lt _ hN0
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hfract : Int.fract ((j : ℝ) / N * v) = (r : ℝ) / N := by
    rw [Int.fract_eq_iff]
    refine ⟨by positivity, by rw [div_lt_one (by exact_mod_cast hN0)]; exact_mod_cast hrN, ?_⟩
    set q := (j * v) / N with hq
    refine ⟨(q : ℤ), ?_⟩
    rw [Int.cast_natCast]
    have hdm := Nat.div_add_mod (j * v) N
    have h' : (j : ℝ) * v = (N : ℝ) * q + r := by
      rw [hr, hq]; exact_mod_cast hdm.symm
    field_simp
    linarith
  rw [distToNearestInt, hfract]
  have hPN : (1 : ℝ) / (2 * k) = (P : ℝ) / N := by
    rw [hN]; push_cast; field_simp
  rw [hPN]
  apply le_min
  · apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast h1
  · rw [le_sub_iff_add_le, ← add_div, div_le_one (by exact_mod_cast hN0)]
    have : P + r ≤ N := by omega
    exact_mod_cast this
