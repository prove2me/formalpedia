-- Prove2me | solution 1 for NConjecture.bb94_theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T15:16:45.545994+00:00
-- url     : https://prove2.me/submissions/9c5f246d-8d6c-4b53-a0ba-66ab1a8c10af

import Mathlib
import Definitions.Def_NConjecture_Defs
namespace NConjecture

theorem AuxSH_N (m : ℕ) : ∃ q, 3 ^ (2 ^ (m + 1)) = 2 ^ (m + 3) * q + 1 := by
  induction m with
  | zero => exact ⟨1, by norm_num⟩
  | succ m ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨2 ^ (m + 2) * q ^ 2 + q, ?_⟩
    rw [show 2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 by ring, pow_mul, hq]
    ring

theorem AuxSH_rad_le (n : ℕ) (hn : n ≠ 0) : Brocard.radical n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)


section BBP
open Polynomial
noncomputable def AuxBB_TV : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1, 2)
  | k + 1 => (X * (AuxBB_TV k).1 + (AuxBB_TV k).1 + (AuxBB_TV k).2, X * (AuxBB_TV k).1 + (AuxBB_TV k).2)

noncomputable def AuxBB_H (k : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (k + 1), C (f.coeff j) * X ^ (k - j) * (X - 1) ^ (2 * j)

theorem AuxBB_cx (p : Polynomial ℤ) (j : ℕ) : (X * p).coeff j = if j = 0 then 0 else p.coeff (j - 1) := by
  cases j with
  | zero => simp
  | succ j => simp [coeff_X_mul]

theorem AuxBB_inv (k : ℕ) :
    (∀ j, k < j → (AuxBB_TV k).1.coeff j = 0) ∧ (∀ j, k < j → (AuxBB_TV k).2.coeff j = 0) ∧
    (∀ j ≤ k, 0 < (AuxBB_TV k).1.coeff j) ∧ (∀ j, 0 ≤ (AuxBB_TV k).1.coeff j) ∧
    (∀ j, 0 ≤ (AuxBB_TV k).2.coeff j) := by
  induction k with
  | zero =>
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun j => ?_⟩
    · simp only [AuxBB_TV, coeff_one]; rw [if_neg (by omega)]
    · simp only [AuxBB_TV]
      rw [show (2 : Polynomial ℤ) = C 2 by simp, coeff_C, if_neg (by omega)]
    · simp only [AuxBB_TV, coeff_one]; rw [if_pos (by omega)]; norm_num
    · simp only [AuxBB_TV, coeff_one]; split_ifs <;> norm_num
    · simp only [AuxBB_TV]
      rw [show (2 : Polynomial ℤ) = C 2 by simp, coeff_C]; split_ifs <;> norm_num
  | succ k ih =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := ih
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun j => ?_⟩
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      rw [if_neg (by omega), a1 (j - 1) (by omega), a1 j (by omega), a2 j (by omega)]; norm_num
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      rw [if_neg (by omega), a1 (j - 1) (by omega), a2 j (by omega)]; norm_num
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      have := a5 j
      split_ifs with h
      · have := a3 j (by omega); linarith
      · rcases Nat.lt_or_ge k j with h' | h'
        · have := a3 (j - 1) (by omega); have := a4 j; linarith
        · have := a3 j h'; have := a4 (j - 1); linarith
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      have := a4 j; have := a5 j; have := a4 (j - 1)
      split_ifs <;> linarith
    · simp only [AuxBB_TV, coeff_add, AuxBB_cx]
      have := a5 j; have := a4 (j - 1)
      split_ifs <;> linarith

theorem AuxBB_Hadd (k : ℕ) (f g : Polynomial ℤ) : AuxBB_H k (f + g) = AuxBB_H k f + AuxBB_H k g := by
  unfold AuxBB_H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [coeff_add, C_add]; ring

theorem AuxBB_HX (k : ℕ) (f : Polynomial ℤ) : AuxBB_H (k + 1) (X * f) = (X - 1) ^ 2 * AuxBB_H k f := by
  unfold AuxBB_H
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [coeff_X_mul, coeff_X_mul_zero, C_0, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show k + 1 - (j + 1) = k - j by omega, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  ring

theorem AuxBB_H1 (k : ℕ) (f : Polynomial ℤ) (hf : f.coeff (k + 1) = 0) :
    AuxBB_H (k + 1) f = X * AuxBB_H k f := by
  unfold AuxBB_H
  rw [Finset.sum_range_succ (n := k + 1), hf, C_0, zero_mul, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := Finset.mem_range.mp hj
  rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
  ring

theorem AuxBB_id (k : ℕ) :
    AuxBB_H k (AuxBB_TV k).1 = ∑ i ∈ Finset.range (2 * k + 1), (X : Polynomial ℤ) ^ i ∧
    AuxBB_H k (AuxBB_TV k).2 = X ^ (2 * k) + 1 := by
  induction k with
  | zero =>
    have h2 : (2 : Polynomial ℤ).coeff 0 = 2 := by
      rw [show (2 : Polynomial ℤ) = C 2 by simp, coeff_C_zero]
    refine ⟨by simp [AuxBB_H, AuxBB_TV], ?_⟩
    simp only [AuxBB_H, AuxBB_TV, zero_add, Finset.sum_range_one, h2, Nat.sub_self, pow_zero,
      mul_zero, mul_one]
    rw [show (C 2 : Polynomial ℤ) = 2 by simp]; norm_num
  | succ k ih =>
    obtain ⟨i1, i2⟩ := ih
    obtain ⟨a1, a2, -, -, -⟩ := AuxBB_inv k
    have g := geom_sum_mul (X : Polynomial ℤ) (2 * k + 1)
    have hT := AuxBB_H1 k _ (a1 (k + 1) (by omega))
    have hV := AuxBB_H1 k _ (a2 (k + 1) (by omega))
    simp only [AuxBB_TV]
    rw [AuxBB_Hadd, AuxBB_Hadd, AuxBB_Hadd, AuxBB_HX, hT, hV, i1, i2]
    have e : ∑ i ∈ Finset.range (2 * (k + 1) + 1), (X : Polynomial ℤ) ^ i =
        (∑ i ∈ Finset.range (2 * k + 1), (X : Polynomial ℤ) ^ i) + X ^ (2 * k + 1) + X ^ (2 * k + 2) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring, Finset.sum_range_succ _ (2 * k + 2),
        Finset.sum_range_succ _ (2 * k + 1)]
    constructor
    · rw [e]
      linear_combination X * g
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      linear_combination (X - 1) * g

theorem bb94_lemma_1 (k : ℕ) :
    ∃ f : Polynomial ℤ, f.natDegree = k ∧ (∀ j ≤ k, 0 < f.coeff j) ∧
      (∑ i ∈ Finset.range (2 * k + 1), (Polynomial.X : Polynomial ℤ) ^ i) =
        ∑ j ∈ Finset.range (k + 1),
          Polynomial.C (f.coeff j) * Polynomial.X ^ (k - j) * (Polynomial.X - 1) ^ (2 * j) := by
  obtain ⟨a1, -, a3, -, -⟩ := AuxBB_inv k
  refine ⟨(AuxBB_TV k).1, ?_, a3, ?_⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr a1)
      (ne_of_gt (a3 k le_rfl))
  · exact (AuxBB_id k).1.symm


end BBP

theorem AuxT_main (k : ℕ) (c : ℕ → ℕ) (hc : ∀ j ≤ k, 0 < c j)
    (hid : ∀ x : ℤ, ∑ i ∈ Finset.range (2*k+1), x^i =
      ∑ j ∈ Finset.range (k+1), (c j : ℤ) * x^(k-j) * (x-1)^(2*j))
    (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {a : Fin (k+3) → ℤ | admissible (k+3) a ∧
      (Brocard.radical (∏ i, (a i).natAbs) : ℝ) ^ (2 * ((k+3 : ℕ) : ℝ) - 5 - ε) <
        ((Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℝ)} := by
  set S : ℕ := ∏ j ∈ Finset.range (k+1), c j with hSdef
  have hS : 0 < S := Finset.prod_pos (fun j hj => hc j (by simp at hj; omega))
  set xx : ℕ → ℕ := fun m => 3 ^ (2 ^ (m + 6*S + 1)) with hxx
  set T : ℕ → ℕ → ℕ := fun x j => c j * x^(k-j) * (x-1)^(2*j+1) with hT
  set A : ℕ → Fin (k+3) → ℤ := fun m i =>
    if i.val = 0 then ((xx m : ℕ) : ℤ)^(2*k+1) else if i.val = 1 then -1
    else -((T (xx m) (i.val - 2) : ℕ) : ℤ) with hA
  refine Set.infinite_of_injective_forall_mem (f := A) ?_ ?_
  · intro m m' h
    have h0 := congrFun h 0
    simp only [hA, Fin.val_zero, if_true] at h0
    have h1 : xx m ^ (2*k+1) = xx m' ^ (2*k+1) := by exact_mod_cast h0
    have h2 : xx m = xx m' := Nat.pow_left_injective (by omega) h1
    have h2' : 3 ^ (2 ^ (m + 6*S + 1)) = 3 ^ (2 ^ (m' + 6*S + 1)) := h2
    have h3 : 2 ^ (m + 6*S + 1) = 2 ^ (m' + 6*S + 1) := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2'
    have := Nat.pow_right_injective (le_refl 2) h3
    omega
  · intro m
    obtain ⟨q, hq⟩ := AuxSH_N (m + 6*S)
    set x := xx m with hxdef
    have hxq : x = 2 ^ (m + 6*S + 3) * q + 1 := by
      rw [hxdef, hxx]; simp only; rw [hq]
    have hx3 : 3 ≤ x := by
      rw [hxdef, hxx]; exact Nat.le_self_pow (pow_ne_zero _ two_ne_zero) 3
    have hq0 : q ≠ 0 := by rintro rfl; omega
    have hx1 : 1 ≤ x := by omega
    -- integer identity
    have hidx : ((x:ℤ))^(2*k+1) - 1 =
        ∑ j ∈ Finset.range (k+1), (c j : ℤ) * (x:ℤ)^(k-j) * ((x:ℤ)-1)^(2*j+1) := by
      rw [← geom_sum_mul, hid, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    have hTc : ∀ j, ((T x j : ℕ) : ℤ) = (c j : ℤ) * (x:ℤ)^(k-j) * ((x:ℤ)-1)^(2*j+1) := by
      intro j; simp only [hT]; push_cast [Nat.cast_sub hx1]; ring
    have hA0 : A m 0 = (x:ℤ)^(2*k+1) := by simp [hA, hxdef]
    have hA1 : A m 1 = -1 := by simp [hA]
    have hAj : ∀ i : Fin (k+3), i.val ≠ 0 → i.val ≠ 1 → A m i = -((T x (i.val - 2) : ℕ) : ℤ) := by
      intro i h0 h1
      have h0' : i ≠ 0 := fun h => h0 (by simp [h])
      simp [hA, h0', h1, hxdef]
    have hsum : ∑ i, A m i = 0 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have e : ∀ i : Fin (k+1), A m i.succ.succ = -((T x i.val : ℕ) : ℤ) := by
        intro i; rw [hAj _ (by simp) (by simp)]; simp
      simp only [e]
      rw [Fin.sum_univ_eq_sum_range (fun j => -((T x j : ℕ) : ℤ)) (k+1)]
      have e0 : A m 0 = (x:ℤ)^(2*k+1) := hA0
      have e1 : A m (Fin.succ 0) = -1 := hA1
      rw [e0, e1, Finset.sum_neg_distrib]
      simp only [hTc]
      rw [← hidx]; ring
    have hneg : ∀ i : Fin (k+3), i.val ≠ 0 → A m i < 0 := by
      intro i h0
      by_cases h1 : i.val = 1
      · rw [show i = 1 from Fin.ext (by simp [h1])]; rw [hA1]; norm_num
      · rw [hAj i h0 h1]
        have hj : i.val - 2 ≤ k := by omega
        have : 0 < T x (i.val - 2) := by
          simp only [hT]
          have := hc _ hj
          have : 0 < x - 1 := by omega
          positivity
        omega
    have hnegsum : ∀ s : Finset (Fin (k+3)), s.Nonempty → (0 : Fin (k+3)) ∉ s →
        ∑ i ∈ s, A m i < 0 := by
      intro s hs h0
      have := Finset.sum_pos (s := s) (f := fun i => -A m i)
        (fun i hi => neg_pos.mpr (hneg i (fun h => h0 (by rwa [show i = 0 from Fin.ext h] at hi)))) hs
      simp only [Finset.sum_neg_distrib] at this
      linarith
    refine ⟨⟨hsum, ?_, ?_⟩, ?_⟩
    · have := Finset.gcd_dvd (s := Finset.univ) (f := fun i => (A m i).natAbs) (Finset.mem_univ 1)
      simp only [hA1] at this
      simpa using this
    · intro s hs hne hz
      by_cases h0 : (0 : Fin (k+3)) ∈ s
      · have ht : (Finset.univ \ s).Nonempty := by
          rw [Finset.sdiff_nonempty]; intro hu; exact hne (Finset.eq_univ_of_forall (fun i => hu (Finset.mem_univ i)))
        have h0t : (0 : Fin (k+3)) ∉ Finset.univ \ s := by simp [h0]
        have := Finset.sum_sdiff (f := fun i => A m i) (Finset.subset_univ s)
        rw [hz, hsum, add_zero] at this
        have := hnegsum _ ht h0t
        linarith
      · exact absurd hz (ne_of_lt (hnegsum s hs h0))
    · -- radical bound
      set N := ∏ i, (A m i).natAbs with hN
      have h6 : 6 * q * S ≠ 0 := by positivity
      have hsub : N.primeFactors ⊆ (6 * q * S).primeFactors := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpd := Nat.dvd_of_mem_primeFactors hp
        rw [Nat.mem_primeFactors]
        refine ⟨hpp, ?_, h6⟩
        obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpd
        have hx : p ∣ x → p ∣ 6 * q * S := by
          intro h
          have : p ∣ 3 := by
            rw [hxdef, hxx] at h; exact hpp.dvd_of_dvd_pow h
          exact dvd_trans (dvd_trans this (by norm_num : (3:ℕ) ∣ 6)) (dvd_mul_of_dvd_left (dvd_mul_right 6 q) S)
        by_cases h0 : i.val = 0
        · rw [show i = 0 from Fin.ext h0, hA0] at hi
          simp only [Int.natAbs_pow, Int.natAbs_natCast] at hi
          exact hx (hpp.dvd_of_dvd_pow hi)
        by_cases h1 : i.val = 1
        · rw [show i = 1 from Fin.ext (by simp [h1]), hA1] at hi
          simp at hi; exact absurd hi hpp.ne_one
        rw [hAj i h0 h1, Int.natAbs_neg, Int.natAbs_natCast] at hi
        simp only [hT] at hi
        rcases (Nat.Prime.dvd_mul hpp).mp hi with hi | hi
        · rcases (Nat.Prime.dvd_mul hpp).mp hi with hi | hi
          · have : c (i.val - 2) ∣ S := Finset.dvd_prod_of_mem _ (by simp; omega)
            exact dvd_trans (dvd_trans hi this) (dvd_mul_left _ _)
          · exact hx (hpp.dvd_of_dvd_pow hi)
        · have hi := hpp.dvd_of_dvd_pow hi
          rw [show x - 1 = 2 ^ (m + 6*S + 3) * q by omega] at hi
          rcases (Nat.Prime.dvd_mul hpp).mp hi with hi | hi
          · have : p ∣ 2 := hpp.dvd_of_dvd_pow hi
            exact dvd_trans (dvd_trans this (by norm_num : (2:ℕ) ∣ 6)) (dvd_mul_of_dvd_left (dvd_mul_right 6 q) S)
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hi 6) S
      have hR : Brocard.radical N ≤ 6 * q * S := by
        refine le_trans ?_ (AuxSH_rad_le _ h6)
        unfold Brocard.radical
        exact Finset.prod_le_prod_of_subset_of_one_le' hsub
          (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      have h6S : 6 * S ≤ 2 ^ (m + 6*S + 3) :=
        le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hRx : Brocard.radical N < x := by
        have : 6 * q * S ≤ 2 ^ (m + 6*S + 3) * q := by
          calc 6 * q * S = q * (6 * S) := by ring
            _ ≤ q * 2 ^ (m + 6*S + 3) := Nat.mul_le_mul_left _ h6S
            _ = _ := by ring
        omega
      have hR1 : 1 ≤ Brocard.radical N := by
        unfold Brocard.radical
        exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
      have hsup : x ^ (2*k+1) ≤ Finset.univ.sup (fun i => (A m i).natAbs) := by
        have := Finset.le_sup (f := fun i => (A m i).natAbs) (Finset.mem_univ 0)
        simp only [hA0, Int.natAbs_pow, Int.natAbs_natCast] at this
        exact this
      have hexp : 2 * ((k+3 : ℕ) : ℝ) - 5 - ε = (2*k+1 : ℝ) - ε := by push_cast; ring
      rw [hexp]
      have hsupR : ((x:ℝ))^(2*k+1) ≤ ((Finset.univ.sup (fun i => (A m i).natAbs) : ℕ) : ℝ) := by
        exact_mod_cast hsup
      have hRxR : (Brocard.radical N : ℝ) < x := by exact_mod_cast hRx
      have hR1R : (1:ℝ) ≤ Brocard.radical N := by exact_mod_cast hR1
      have hx1R : (1:ℝ) ≤ x := by exact_mod_cast hx1
      refine lt_of_lt_of_le ?_ hsupR
      rcases le_or_gt ((2*k+1 : ℝ) - ε) 0 with he | he
      · calc (Brocard.radical N : ℝ) ^ ((2*k+1 : ℝ) - ε) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos hR1R he
          _ < x := by
              have : (3:ℝ) ≤ x := by exact_mod_cast hx3
              linarith
          _ ≤ (x:ℝ) ^ (2*k+1) := le_self_pow₀ hx1R (by omega)
      · calc (Brocard.radical N : ℝ) ^ ((2*k+1 : ℝ) - ε) < (x:ℝ) ^ ((2*k+1 : ℝ) - ε) :=
              Real.rpow_lt_rpow (by positivity) hRxR he
          _ ≤ (x:ℝ) ^ ((2*k+1 : ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx1R (by push_cast; linarith)
          _ = (x:ℝ) ^ (2*k+1) := Real.rpow_natCast _ _

theorem bb94_theorem_1 (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {a : Fin n → ℤ | admissible n a ∧
      (Brocard.radical (∏ i, (a i).natAbs) : ℝ) ^ (2 * (n : ℝ) - 5 - ε) <
        ((Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℝ)} := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨f, -, hpos, hf⟩ := bb94_lemma_1 k
  refine AuxT_main k (fun j => (f.coeff j).toNat) (fun j hj => by simpa using hpos j hj) ?_ ε hε
  intro x
  have := congrArg (Polynomial.eval x) hf
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one] at this
  rw [this]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Int.toNat_of_nonneg (le_of_lt (hpos j (by simp at hj; omega)))]

end NConjecture

theorem solution (n : ℕ) (hn : 3 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {a : Fin n → ℤ | NConjecture.admissible n a ∧
      (Brocard.radical (∏ i, (a i).natAbs) : ℝ) ^ (2 * (n : ℝ) - 5 - ε) <
        ((Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℝ)} :=
  NConjecture.bb94_theorem_1 n hn ε hε
