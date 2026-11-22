-- Prove2me | solution 1 for NConjecture.abc_false_implies_n_false
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T15:22:13.772073+00:00
-- url     : https://prove2.me/submissions/7ffeaf4c-377f-4676-aed1-cd3629ee58f2

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

theorem AuxSH_union (s t : Finset ℕ) (hs : ∀ p ∈ s ∩ t, 0 < p) :
    ∏ p ∈ s ∪ t, p ≤ (∏ p ∈ s, p) * ∏ p ∈ t, p := by
  rw [← Finset.prod_union_inter]
  exact Nat.le_mul_of_pos_right _ (Finset.prod_pos hs)

theorem AuxF_tuple (k : ℕ) (c : ℕ → ℕ) (hc : ∀ j ≤ k, 0 < c j)
    (hid : ∀ x : ℚ, ∑ i ∈ Finset.range (2*k+1), x^i =
      ∑ j ∈ Finset.range (k+1), (c j : ℚ) * x^(k-j) * (x-1)^(2*j))
    (a b cc : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a cc) (hs : a + b = cc) :
    ∃ t : Fin (k+3) → ℤ, admissible (k+3) t ∧
      cc ^ (2*k+1) ≤ Finset.univ.sup (fun i => (t i).natAbs) ∧
      Brocard.radical (∏ i, (t i).natAbs) ≤ (∏ j ∈ Finset.range (k+1), c j) * Brocard.radical (a*b*cc) := by
  set S : ℕ := ∏ j ∈ Finset.range (k+1), c j with hSdef
  have hS : 0 < S := Finset.prod_pos (fun j hj => hc j (by simp at hj; omega))
  set T : ℕ → ℕ := fun j => c j * (a*cc)^(k-j) * b^(2*j+1) with hT
  set A : Fin (k+3) → ℤ := fun i =>
    if i.val = 0 then ((cc : ℕ) : ℤ)^(2*k+1) else if i.val = 1 then -((a:ℤ)^(2*k+1))
    else -((T (i.val - 2) : ℕ) : ℤ) with hA
  refine ⟨A, ?_⟩
  have hidQ : ((cc:ℚ))^(2*k+1) - (a:ℚ)^(2*k+1) =
      ∑ j ∈ Finset.range (k+1), ((T j : ℕ) : ℚ) := by
    have haQ : (a:ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have h1 := hid ((cc:ℚ)/a)
    have h2 : ((cc:ℚ)/a)^(2*k+1) - 1 = ∑ j ∈ Finset.range (k+1),
        (c j : ℚ) * ((cc:ℚ)/a)^(k-j) * ((cc:ℚ)/a-1)^(2*j+1) := by
      rw [← geom_sum_mul, h1, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    have h3 : ((cc:ℚ))^(2*k+1) - (a:ℚ)^(2*k+1) = (a:ℚ)^(2*k+1) * (((cc:ℚ)/a)^(2*k+1) - 1) := by
      have e : (a:ℚ)^(2*k+1) * ((cc:ℚ)/a)^(2*k+1) = (cc:ℚ)^(2*k+1) := by
        rw [← mul_pow]; congr 1; field_simp
      linear_combination (-1 : ℚ) * e
    rw [h3, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj : j ≤ k := by simp at hj; omega
    have hbq : (cc:ℚ)/a - 1 = (b:ℚ)/a := by
      rw [← hs]; push_cast; field_simp; ring
    rw [hbq]
    simp only [hT]; push_cast
    rw [show 2*k+1 = (k-j) + (k-j) + (2*j+1) by omega, pow_add, pow_add]
    rw [div_pow, div_pow]
    field_simp
    ring
  have hidZ : ((cc:ℤ))^(2*k+1) - (a:ℤ)^(2*k+1) = ∑ j ∈ Finset.range (k+1), ((T j : ℕ) : ℤ) := by
    exact_mod_cast hidQ
  have hA0 : A 0 = (cc:ℤ)^(2*k+1) := by simp [hA]
  have hA1 : A 1 = -((a:ℤ)^(2*k+1)) := by simp [hA]
  have hAj : ∀ i : Fin (k+3), i.val ≠ 0 → i.val ≠ 1 → A i = -((T (i.val - 2) : ℕ) : ℤ) := by
    intro i h0 h1
    have h0' : i ≠ 0 := fun h => h0 (by simp [h])
    simp [hA, h0', h1]
  have hsum : ∑ i, A i = 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have e : ∀ i : Fin (k+1), A i.succ.succ = -((T i.val : ℕ) : ℤ) := by
      intro i; rw [hAj _ (by simp) (by simp)]; simp
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun j => -((T j : ℕ) : ℤ)) (k+1)]
    have e1 : A (Fin.succ 0) = -((a:ℤ)^(2*k+1)) := hA1
    rw [hA0, e1, Finset.sum_neg_distrib, ← hidZ]; ring
  have hneg : ∀ i : Fin (k+3), i.val ≠ 0 → A i < 0 := by
    intro i h0
    by_cases h1 : i.val = 1
    · rw [show i = 1 from Fin.ext (by simp [h1]), hA1]
      have : 0 < (a:ℤ)^(2*k+1) := by positivity
      linarith
    · rw [hAj i h0 h1]
      have hj : i.val - 2 ≤ k := by omega
      have : 0 < T (i.val - 2) := by
        simp only [hT]
        have := hc _ hj
        have : 0 < cc := by omega
        positivity
      omega
  have hnegsum : ∀ s : Finset (Fin (k+3)), s.Nonempty → (0 : Fin (k+3)) ∉ s →
      ∑ i ∈ s, A i < 0 := by
    intro s hs h0
    have := Finset.sum_pos (s := s) (f := fun i => -A i)
      (fun i hi => neg_pos.mpr (hneg i (fun h => h0 (by rwa [show i = 0 from Fin.ext h] at hi)))) hs
    simp only [Finset.sum_neg_distrib] at this
    linarith
  refine ⟨⟨hsum, ?_, ?_⟩, ?_, ?_⟩
  · have g0 := Finset.gcd_dvd (s := Finset.univ) (f := fun i => (A i).natAbs) (Finset.mem_univ 0)
    have g1 := Finset.gcd_dvd (s := Finset.univ) (f := fun i => (A i).natAbs) (Finset.mem_univ 1)
    simp only [hA0, hA1, Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_natCast] at g0 g1
    have hcop : Nat.Coprime (cc^(2*k+1)) (a^(2*k+1)) := (Nat.Coprime.pow _ _ hab.symm)
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd g0 g1)
  · intro s hs hne hz
    by_cases h0 : (0 : Fin (k+3)) ∈ s
    · have ht : (Finset.univ \ s).Nonempty := by
        rw [Finset.sdiff_nonempty]; intro hu; exact hne (Finset.eq_univ_of_forall (fun i => hu (Finset.mem_univ i)))
      have h0t : (0 : Fin (k+3)) ∉ Finset.univ \ s := by simp [h0]
      have := Finset.sum_sdiff (f := fun i => A i) (Finset.subset_univ s)
      rw [hz, hsum, add_zero] at this
      have := hnegsum _ ht h0t
      linarith
    · exact absurd hz (ne_of_lt (hnegsum s hs h0))
  · have := Finset.le_sup (f := fun i => (A i).natAbs) (Finset.mem_univ 0)
    simp only [hA0, Int.natAbs_pow, Int.natAbs_natCast] at this
    exact this
  · set N := ∏ i, (A i).natAbs with hN
    have hcc : 0 < cc := by omega
    have habc : a * b * cc ≠ 0 := by positivity
    have hsub : N.primeFactors ⊆ S.primeFactors ∪ (a*b*cc).primeFactors := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      rw [Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpd
      have hR : p ∣ a * b * cc → (p.Prime ∧ p ∣ S ∧ S ≠ 0) ∨ (p.Prime ∧ p ∣ a * b * cc ∧ a * b * cc ≠ 0) :=
        fun h => Or.inr ⟨hpp, h, habc⟩
      by_cases h0 : i.val = 0
      · rw [show i = 0 from Fin.ext h0, hA0] at hi
        simp only [Int.natAbs_pow, Int.natAbs_natCast] at hi
        exact hR (dvd_mul_of_dvd_right (hpp.dvd_of_dvd_pow hi) _)
      by_cases h1 : i.val = 1
      · rw [show i = 1 from Fin.ext (by simp [h1]), hA1] at hi
        simp only [Int.natAbs_neg, Int.natAbs_pow, Int.natAbs_natCast] at hi
        exact hR (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hpp.dvd_of_dvd_pow hi) _) _)
      rw [hAj i h0 h1, Int.natAbs_neg, Int.natAbs_natCast] at hi
      simp only [hT] at hi
      rcases (Nat.Prime.dvd_mul hpp).mp hi with hi | hi
      · rcases (Nat.Prime.dvd_mul hpp).mp hi with hi | hi
        · have : c (i.val - 2) ∣ S := Finset.dvd_prod_of_mem _ (by simp; omega)
          exact Or.inl ⟨hpp, dvd_trans hi this, hS.ne'⟩
        · have hi := hpp.dvd_of_dvd_pow hi
          rcases (Nat.Prime.dvd_mul hpp).mp hi with hi | hi
          · exact hR (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hi _) _)
          · exact hR (dvd_mul_of_dvd_right hi _)
      · exact hR (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hpp.dvd_of_dvd_pow hi) _) _)
    unfold Brocard.radical
    calc ∏ p ∈ N.primeFactors, p ≤ ∏ p ∈ S.primeFactors ∪ (a*b*cc).primeFactors, p :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub
            (fun p hp _ => by
              rcases Finset.mem_union.mp hp with h | h <;> exact (Nat.prime_of_mem_primeFactors h).one_lt.le)
      _ ≤ (∏ p ∈ S.primeFactors, p) * ∏ p ∈ (a*b*cc).primeFactors, p :=
          AuxSH_union _ _ (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos)
      _ ≤ S * ∏ p ∈ (a*b*cc).primeFactors, p :=
          Nat.mul_le_mul_right _ (AuxSH_rad_le S hS.ne')

theorem abc_false_implies_n_false (n : ℕ) (hn : 4 ≤ n)
    (h : ¬ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε)) :
    ¬ conjAt n := by
  intro hconj
  apply h
  intro ε0 hε0
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨f, -, hpos, hf⟩ := bb94_lemma_1 k
  set c : ℕ → ℕ := fun j => (f.coeff j).toNat with hcdef
  have hc : ∀ j ≤ k, 0 < c j := fun j hj => by simpa [hcdef] using hpos j hj
  have hcz : ∀ j ≤ k, ((c j : ℕ) : ℤ) = f.coeff j := fun j hj => by
    simp only [hcdef]; exact Int.toNat_of_nonneg (le_of_lt (hpos j hj))
  have hidQ : ∀ x : ℚ, ∑ i ∈ Finset.range (2*k+1), x^i =
      ∑ j ∈ Finset.range (k+1), (c j : ℚ) * x^(k-j) * (x-1)^(2*j) := by
    intro x
    have := congrArg (Polynomial.eval₂ (Int.castRingHom ℚ) x) hf
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_sub, Polynomial.eval₂_one,
      eq_intCast] at this
    rw [this]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj : j ≤ k := by simp at hj; omega
    have e : ((c j : ℕ) : ℚ) = ((f.coeff j : ℤ) : ℚ) := by
      rw [← hcz j hj]; push_cast; rfl
    have e2 : Polynomial.eval₂ (Int.castRingHom ℚ) x ((f.coeff j : ℤ) : Polynomial ℤ) = ((f.coeff j : ℤ) : ℚ) := by
      rw [← Polynomial.C_eq_intCast, Polynomial.eval₂_C]; rfl
    rw [e, e2]
  set S : ℕ := ∏ j ∈ Finset.range (k+1), c j with hSdef
  have hS : 0 < S := Finset.prod_pos (fun j hj => hc j (by simp at hj; omega))
  obtain ⟨C, hC, hCb⟩ := hconj ((2*k+1 : ℝ) * ε0) (by positivity)
  set E : ℝ := (2*k+1 : ℝ) * (1 + ε0) with hE
  have hE0 : 0 < E := by positivity
  set K : ℝ := C * (S:ℝ)^E + 1 with hK
  have hSpos : (0:ℝ) < S := by exact_mod_cast hS
  have hK1 : 1 ≤ K := by have := Real.rpow_pos_of_pos hSpos E; nlinarith
  refine ⟨K, by linarith, ?_⟩
  intro a b cc ha hb hc0 hab hbc hac hs
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, ht, hsup, hrad⟩ := AuxF_tuple k c hc hidQ a b cc ha hb hac hs
  have h1 := hCb t ht
  set R : ℝ := ∏ p ∈ (a * b * cc).primeFactors, (p : ℝ) with hR
  have hRn : R = ((Brocard.radical (a*b*cc) : ℕ) : ℝ) := by
    simp only [hR, Brocard.radical]; push_cast; rfl
  have hR1 : 1 ≤ R := by
    rw [hRn]
    have : 1 ≤ Brocard.radical (a*b*cc) := by
      unfold Brocard.radical
      exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast this
  have hexp : 2 * ((k + 3 : ℕ) : ℝ) - 5 + (2*k+1 : ℝ) * ε0 = E := by
    rw [hE]; push_cast; ring
  rw [hexp] at h1
  have hradR : ((Brocard.radical (∏ i, (t i).natAbs) : ℕ) : ℝ) ≤ (S:ℝ) * R := by
    rw [hRn]; exact_mod_cast hrad
  have hsupR : ((cc:ℝ))^(2*k+1) ≤ ((Finset.univ.sup (fun i => (t i).natAbs) : ℕ) : ℝ) := by
    exact_mod_cast hsup
  have h2 : ((cc:ℝ))^(2*k+1) ≤ C * ((S:ℝ)^E * R^E) := by
    rw [← Real.mul_rpow hSpos.le (by linarith)]
    refine le_trans hsupR (le_trans h1 ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hradR hE0.le) hC.le
  have hRE : 0 < R^E := Real.rpow_pos_of_pos (by linarith) E
  have h3 : K^(2*k+1) * R^E ≤ ((cc:ℝ))^(2*k+1) := by
    have hpow : (K * R^(1+ε0))^(2*k+1) = K^(2*k+1) * R^E := by
      rw [mul_pow, ← Real.rpow_natCast (R^(1+ε0)), ← Real.rpow_mul (by linarith)]
      congr 2; rw [hE]; push_cast; ring
    rw [← hpow]
    exact pow_le_pow_left₀ (by positivity) hlt _
  have h4 : K ≤ K^(2*k+1) := le_self_pow₀ hK1 (by omega)
  have h5 : K * R^E ≤ C * (S:ℝ)^E * R^E := by nlinarith
  have h6 : K ≤ C * (S:ℝ)^E := le_of_mul_le_mul_right h5 hRE
  linarith

end NConjecture

theorem solution (n : ℕ) (hn : 4 ≤ n)
    (h : ¬ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε)) :
    ¬ NConjecture.conjAt n :=
  NConjecture.abc_false_implies_n_false n hn h
