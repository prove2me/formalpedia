-- Prove2me | solution 1 for JRPHard.Shor.appendix_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T23:29:33.177248+00:00
-- url     : https://prove2.me/submissions/a26bfba2-6849-4441-ba8b-dc74bb0a1bd6

import Mathlib
import Definitions.Def_JRPHard_Shor_Setting

set_option autoImplicit false

namespace JRPHardShorAux

open Finset JRPHard.Shor

lemma dvd_prod_primes_sub {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) :
    ∀ (s : Finset (Fin n)) (q : ℕ), q ∣ ∏ i ∈ s, p i → ∃ S ⊆ s, q = ∏ i ∈ S, p i := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    simpa using hq
  | insert j s hj ih =>
    intro q hq
    rw [Finset.prod_insert hj] at hq
    by_cases hd : p j ∣ q
    · obtain ⟨q', rfl⟩ := hd
      have hq' : q' ∣ ∏ i ∈ s, p i :=
        Nat.dvd_of_mul_dvd_mul_left (hp j).pos hq
      obtain ⟨S, hS, hSq⟩ := ih q' hq'
      refine ⟨insert j S, Finset.insert_subset_insert _ hS, ?_⟩
      have hjS : j ∉ S := fun h => hj (hS h)
      rw [Finset.prod_insert hjS, hSq]
    · have hcop : Nat.Coprime q (p j) :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hp j)).mpr hd)
      have h2 : q ∣ ∏ i ∈ s, p i := by
        exact hcop.dvd_of_dvd_mul_left hq
      obtain ⟨S, hS, hSq⟩ := ih q h2
      exact ⟨S, hS.trans (Finset.subset_insert _ _), hSq⟩

lemma two_mul_le_two_pow (B : ℕ) (hB : 1 ≤ B) : 2 * B ≤ 2 ^ B := by
  induction B with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have := ih hk
      rw [pow_succ]
      linarith

lemma scale_pos {B : ℕ} (hB : 1 ≤ B) : 0 < scale B := by
  unfold scale
  have : (0:ℝ) < B := by exact_mod_cast hB
  positivity

lemma scale_le {B : ℕ} (hB : 1 ≤ B) : scale B ≤ 3 / 2 := by
  unfold scale
  have h : 2 * B ≤ 2 ^ B := two_mul_le_two_pow B hB
  have h' : (2:ℝ) * B ≤ (2:ℝ) ^ B := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma two_rpow_neg_lt {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 3 / 2) :
    (2:ℝ) ^ (-(lam / 2)) < 1 - lam / 4 := by
  rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
  have h := rpow_one_add_lt_one_add_mul_self (s := -(1/2:ℝ)) (p := lam / 2)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
  have e : (1 + -(1/2:ℝ)) = 2⁻¹ := by norm_num
  rw [e] at h
  linarith

lemma key_bounds {n : ℕ} (B : ℕ) (hn : 0 < n) (hB : 1 ≤ B) (a : Fin n → ℕ) (c : ℝ)
    (hc : ∀ i, c * expo B a i <
      scale B * (2 : ℝ) ^ (expo B a i / 2) / (4 * (n : ℝ)))
    (p : Fin n → ℕ)
    (hwin : ∀ i,
      (2 : ℝ) ^ (expo B a i) - c * expo B a i *
        (2 : ℝ) ^ (expo B a i / 2) < (p i : ℝ) ∧
      (p i : ℝ) < (2 : ℝ) ^ (expo B a i) + c * expo B a i *
        (2 : ℝ) ^ (expo B a i / 2))
    (S : Finset (Fin n)) :
    ∃ P : ℝ, ((∏ i ∈ S, p i : ℕ) : ℝ) =
        (2:ℝ) ^ (scale B * ((∑ i ∈ S, a i : ℕ) : ℝ)) * P ∧
      (2:ℝ) ^ (-(scale B / 2)) < P ∧ P < (2:ℝ) ^ (scale B / 2) := by
  have hlam0 := scale_pos hB
  have hlam1 := scale_le hB
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  set lam := scale B with hlamdef
  set δ : ℝ := lam / (4 * n) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hnδ : (n:ℝ) * δ = lam / 4 := by rw [hδ]; field_simp
  have hδ1 : δ < 1 := by
    have : δ ≤ lam / 4 := by rw [← hnδ]; nlinarith
    linarith
  have hr : ∀ i, 1 - δ < (p i : ℝ) / (2:ℝ) ^ (expo B a i) ∧
      (p i : ℝ) / (2:ℝ) ^ (expo B a i) < 1 + δ := by
    intro i
    have hE : (0:ℝ) < (2:ℝ) ^ (expo B a i) := Real.rpow_pos_of_pos two_pos _
    have hE2 : (0:ℝ) < (2:ℝ) ^ (expo B a i / 2) := Real.rpow_pos_of_pos two_pos _
    have hsq : (2:ℝ) ^ (expo B a i / 2) * (2:ℝ) ^ (expo B a i / 2) = (2:ℝ) ^ (expo B a i) := by
      rw [← Real.rpow_add two_pos, add_halves]
    have hdev : c * expo B a i * (2:ℝ) ^ (expo B a i / 2) < δ * (2:ℝ) ^ (expo B a i) := by
      have h1 := mul_lt_mul_of_pos_right (hc i) hE2
      rw [hδ, ← hsq]
      calc c * expo B a i * (2:ℝ) ^ (expo B a i / 2)
          < lam * (2 : ℝ) ^ (expo B a i / 2) / (4 * (n : ℝ)) * (2:ℝ) ^ (expo B a i / 2) := h1
        _ = lam / (4 * n) * ((2:ℝ) ^ (expo B a i / 2) * (2:ℝ) ^ (expo B a i / 2)) := by ring
    obtain ⟨h1, h2⟩ := hwin i
    constructor
    · rw [lt_div_iff₀ hE]; linarith
    · rw [div_lt_iff₀ hE]; linarith
  set r : Fin n → ℝ := fun i => (p i : ℝ) / (2:ℝ) ^ (expo B a i) with hrdef
  have hr' : ∀ i, 1 - δ < r i ∧ r i < 1 + δ := hr
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hpos : ∀ i ∈ S, 0 ≤ r i := fun i _ => by linarith [(hr' i).1]
  refine ⟨∏ i ∈ S, r i, ?_, ?_, ?_⟩
  · rw [Nat.cast_prod]
    have hpe : ∀ i ∈ S, ((p i : ℕ) : ℝ) = (2:ℝ) ^ (expo B a i) * r i := by
      intro i _
      have hEne : (2:ℝ) ^ (expo B a i) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
      simp only [hrdef]
      rw [mul_div_assoc']
      exact (mul_div_cancel_left₀ _ hEne).symm
    rw [Finset.prod_congr rfl hpe, Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos two_pos]
    congr 2
    simp only [expo, ← Finset.mul_sum, Nat.cast_sum]
    rfl
  · have hlo1 : (1 - δ) ^ S.card ≤ ∏ i ∈ S, r i := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => by linarith) (fun i _ => (hr' i).1.le)
    have hlo2 : (1 - δ) ^ n ≤ (1 - δ) ^ S.card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hS
    have hlo3 : 1 + (n:ℝ) * (-δ) ≤ (1 + -δ) ^ n := one_add_mul_le_pow (by linarith) n
    have hlo4 : (2:ℝ) ^ (-(lam / 2)) < 1 - lam / 4 := two_rpow_neg_lt hlam0 hlam1
    have e : (1 + -δ) = 1 - δ := by ring
    rw [e] at hlo3
    nlinarith
  · have hup1 : ∏ i ∈ S, r i ≤ (1 + δ) ^ S.card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod hpos (fun i _ => (hr' i).2.le)
    have hup2 : (1 + δ) ^ S.card ≤ (1 + δ) ^ n := pow_le_pow_right₀ (by linarith) hS
    have hup3 : (1 + δ) ^ n ≤ (Real.exp δ) ^ n :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp δ]) n
    have hup4 : (Real.exp δ) ^ n = Real.exp (lam / 4) := by rw [← Real.exp_nat_mul, hnδ]
    have hup5 : Real.exp (lam / 4) < (2:ℝ) ^ (lam / 2) := by
      rw [Real.rpow_def_of_pos two_pos]
      apply Real.exp_lt_exp.mpr
      have := Real.log_two_gt_d9
      nlinarith
    linarith

end JRPHardShorAux

open JRPHard.Shor Finset in
theorem solution (n B : ℕ) (hn : 0 < n) (hB : 1 ≤ B)
    (a : Fin n → ℕ) (ha : ∀ i, 2 ^ B ≤ a i ∧ a i < 2 ^ (B + 1))
    (heven : Even (∑ i, a i)) (c : ℝ)
    (hc : ∀ i, c * expo B a i <
      scale B * (2 : ℝ) ^ (expo B a i / 2) / (4 * (n : ℝ)))
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hwin : ∀ i,
      (2 : ℝ) ^ (expo B a i) - c * expo B a i *
        (2 : ℝ) ^ (expo B a i / 2) < (p i : ℝ) ∧
      (p i : ℝ) < (2 : ℝ) ^ (expo B a i) + c * expo B a i *
        (2 : ℝ) ^ (expo B a i / 2))
    (hlam : (2 : ℝ) ^ (scale B / 2) +
      (2 : ℝ) ^ (-(scale B / 2)) < 2 * Real.sqrt 2) :
    JRPHard.RangeDiv.IsRangeDivisorInstance (∏ i, p i) ⌈lowL B a⌉₊ ⌊highU B a⌋₊ ∧
      (JRPHard.RangeDiv.HasDivisorIn (∏ i, p i) ⌈lowL B a⌉₊ ⌊highU B a⌋₊ ↔
        PartitionYes a) := by
  classical
  obtain ⟨m, hm⟩ := heven
  have hlam0 := JRPHardShorAux.scale_pos hB
  have hlam1 := JRPHardShorAux.scale_le hB
  have hsum_ge : 2 ^ B ≤ ∑ i, a i :=
    le_trans (ha ⟨0, hn⟩).1
      (Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ _))
  have h2B : 2 ≤ 2 ^ B := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB
  have hm1 : 1 ≤ m := by omega
  have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have h2m : (2:ℝ) ^ B ≤ 2 * (m:ℝ) := by
    have : 2 ^ B ≤ 2 * m := by omega
    exact_mod_cast this
  set lam := scale B with hlamdef
  have hhalf : halfSum a = (m:ℝ) := by
    unfold halfSum; rw [hm]; push_cast; ring
  -- divisor bounds
  have hq : ∀ S : Finset (Fin n),
      (2:ℝ) ^ (lam * ((∑ i ∈ S, a i : ℕ) : ℝ) - lam / 2) < ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
      ((∏ i ∈ S, p i : ℕ) : ℝ) < (2:ℝ) ^ (lam * ((∑ i ∈ S, a i : ℕ) : ℝ) + lam / 2) := by
    intro S
    obtain ⟨P, hPe, hP1, hP2⟩ := JRPHardShorAux.key_bounds B hn hB a c hc p hwin S
    have hEpos : (0:ℝ) < (2:ℝ) ^ (lam * ((∑ i ∈ S, a i : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos two_pos _
    rw [hPe]
    constructor
    · rw [sub_eq_add_neg, Real.rpow_add two_pos]
      exact mul_lt_mul_of_pos_left hP1 hEpos
    · rw [Real.rpow_add two_pos]
      exact mul_lt_mul_of_pos_left hP2 hEpos
  have hLdef : lowL B a = (2:ℝ) ^ (lam * ((m:ℝ) - 1 / 2)) := by
    unfold lowL; rw [hhalf]
  have hUdef : highU B a = (2:ℝ) ^ (lam * ((m:ℝ) + 1 / 2)) := by
    unfold highU; rw [hhalf]
  have hL0 : 0 < lowL B a := by rw [hLdef]; exact Real.rpow_pos_of_pos two_pos _
  have hU0 : 0 < highU B a := by rw [hUdef]; exact Real.rpow_pos_of_pos two_pos _
  have mono : ∀ x y : ℝ, x ≤ y → (2:ℝ) ^ x ≤ (2:ℝ) ^ y :=
    fun x y h => Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  constructor
  · -- instance condition
    have hEm : (2:ℝ) ^ (lam * (m:ℝ)) ≥ (2:ℝ) ^ B := by
      rw [← Real.rpow_natCast]
      apply mono
      have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
      rw [hlamdef]; unfold scale
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h2m (show (0:ℝ) ≤ B by positivity)]
    have hlamE : (2:ℝ) ^ B * lam = 3 * B := by
      rw [hlamdef]; unfold scale; field_simp
    have hLm : lowL B a = (2:ℝ) ^ (lam * (m:ℝ)) * (2:ℝ) ^ (-(lam / 2)) := by
      rw [hLdef, ← Real.rpow_add two_pos]; congr 1; ring
    have hUm : highU B a = (2:ℝ) ^ (lam * (m:ℝ)) * (2:ℝ) ^ (lam / 2) := by
      rw [hUdef, ← Real.rpow_add two_pos]; congr 1; ring
    have hE1 : 1 + lam / 4 ≤ (2:ℝ) ^ (lam / 2) := by
      rw [Real.rpow_def_of_pos two_pos]
      have h1 := Real.add_one_le_exp (Real.log 2 * (lam / 2))
      have h2 := Real.log_two_gt_d9
      nlinarith
    have hE2 : (2:ℝ) ^ (-(lam / 2)) < 1 - lam / 4 := JRPHardShorAux.two_rpow_neg_lt hlam0 hlam1
    have hEmpos : (0:ℝ) < (2:ℝ) ^ (lam * (m:ℝ)) := Real.rpow_pos_of_pos two_pos _
    have hgap : lowL B a + 1 ≤ highU B a := by
      have hdiff : highU B a - lowL B a =
          (2:ℝ) ^ (lam * (m:ℝ)) * ((2:ℝ) ^ (lam / 2) - (2:ℝ) ^ (-(lam / 2))) := by
        rw [hLm, hUm]; ring
      have hd : lam / 2 ≤ (2:ℝ) ^ (lam / 2) - (2:ℝ) ^ (-(lam / 2)) := by linarith
      have k1 := mul_le_mul_of_nonneg_left hd hEmpos.le
      have k2 := mul_le_mul_of_nonneg_right hEm (show (0:ℝ) ≤ lam / 2 by positivity)
      have hB1 : (1:ℝ) ≤ B := by exact_mod_cast hB
      nlinarith
    have hUM : highU B a ≤ ((∏ i, p i : ℕ) : ℝ) := by
      have h := (hq Finset.univ).1
      have hsumR : ((∑ i ∈ Finset.univ, a i : ℕ) : ℝ) = 2 * (m:ℝ) := by
        rw [hm]; push_cast; ring
      rw [hsumR] at h
      rw [hUdef]
      refine le_trans (mono _ _ ?_) h.le
      nlinarith
    have h3 : highU B a ≤ 3 * lowL B a := by
      have hUL : highU B a = lowL B a * (2:ℝ) ^ lam := by
        rw [hUdef, hLdef, ← Real.rpow_add two_pos]; congr 1; ring
      have h32 : (2:ℝ) ^ ((3:ℝ) / 2) = 2 * Real.sqrt 2 := by
        rw [show (3:ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add two_pos, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have hs2 : Real.sqrt 2 < 3 / 2 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hEl : (2:ℝ) ^ lam ≤ 3 := by
        have := mono _ _ hlam1
        rw [h32] at this
        linarith
      rw [hUL]
      nlinarith
    have hxy : ⌈lowL B a⌉₊ ≤ ⌊highU B a⌋₊ := by
      apply Nat.le_floor
      have := Nat.ceil_lt_add_one hL0.le
      linarith
    refine ⟨Nat.ceil_pos.mpr hL0, hxy, ?_, ?_⟩
    · have h1 : (⌊highU B a⌋₊ : ℝ) ≤ ((∏ i, p i : ℕ) : ℝ) :=
        le_trans (Nat.floor_le hU0.le) hUM
      exact_mod_cast h1
    · have hx1 : lowL B a ≤ (⌈lowL B a⌉₊ : ℝ) := Nat.le_ceil _
      have hy1 : (⌊highU B a⌋₊ : ℝ) ≤ highU B a := Nat.floor_le hU0.le
      have hxyR : (⌈lowL B a⌉₊ : ℝ) ≤ (⌊highU B a⌋₊ : ℝ) := by exact_mod_cast hxy
      generalize (⌈lowL B a⌉₊ : ℝ) = x at hx1 hxyR ⊢
      generalize (⌊highU B a⌋₊ : ℝ) = y at hy1 hxyR ⊢
      have hx0 : 0 < x := by linarith
      have hy3 : y ≤ 3 * x := by linarith
      have hy0 : 0 < y := by linarith
      have hprod : 0 ≤ 2 * x * y := by positivity
      have hs := Real.sq_sqrt hprod
      have hs0 := Real.sqrt_nonneg (2 * x * y)
      set s := Real.sqrt (2 * x * y)
      by_contra hcon
      push Not at hcon
      have k1 : (2 * s) * (2 * s) ≤ (x + y) * (x + y) :=
        mul_self_le_mul_self (by positivity) hcon
      nlinarith [mul_nonneg (sub_nonneg.2 hxyR) (sub_nonneg.2 hy3), mul_pos hx0 hx0]
  · -- the equivalence
    have hcard : ∀ S : Finset (Fin n), ∀ k : ℕ, (∑ i ∈ S, a i) = k →
        ((k = m → lowL B a < ((∏ i ∈ S, p i : ℕ) : ℝ) ∧
            ((∏ i ∈ S, p i : ℕ) : ℝ) < highU B a) ∧
         (k < m → ((∏ i ∈ S, p i : ℕ) : ℝ) < lowL B a) ∧
         (m < k → highU B a < ((∏ i ∈ S, p i : ℕ) : ℝ))) := by
      intro S k hk
      obtain ⟨h1, h2⟩ := hq S
      rw [hk] at h1 h2
      refine ⟨?_, ?_, ?_⟩
      · intro hkm
        subst hkm
        constructor
        · rw [hLdef]
          convert h1 using 2
          ring
        · rw [hUdef]
          convert h2 using 2
          ring
      · intro hkm
        have : (k:ℝ) + 1 ≤ m := by exact_mod_cast hkm
        rw [hLdef]
        refine lt_of_lt_of_le h2 (mono _ _ ?_)
        nlinarith
      · intro hkm
        have : (m:ℝ) + 1 ≤ k := by exact_mod_cast hkm
        rw [hUdef]
        refine lt_of_le_of_lt (mono _ _ ?_) h1
        nlinarith
    constructor
    · rintro ⟨q, hqd, hLq, hqU⟩
      obtain ⟨S, -, rfl⟩ := JRPHardShorAux.dvd_prod_primes_sub p hp Finset.univ q hqd
      have hLq' : lowL B a ≤ ((∏ i ∈ S, p i : ℕ) : ℝ) := Nat.ceil_le.mp hLq
      have hqU' : ((∏ i ∈ S, p i : ℕ) : ℝ) ≤ highU B a := (Nat.le_floor_iff hU0.le).mp hqU
      obtain ⟨hA, hB', hC⟩ := hcard S _ rfl
      rcases lt_trichotomy (∑ i ∈ S, a i) m with h | h | h
      · exact absurd (hB' h) (not_lt.mpr hLq')
      · exact ⟨S, by omega⟩
      · exact absurd (hC h) (not_lt.mpr hqU')
    · rintro ⟨S, hS⟩
      have hk : ∑ i ∈ S, a i = m := by omega
      obtain ⟨hA, -, -⟩ := hcard S _ hk
      obtain ⟨h1, h2⟩ := hA rfl
      refine ⟨∏ i ∈ S, p i, Finset.prod_dvd_prod_of_subset S Finset.univ p (Finset.subset_univ S),
        Nat.ceil_le.mpr h1.le, Nat.le_floor h2.le⟩
