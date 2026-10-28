-- Prove2me | solution 1 for LL_Decomp1528a.log_factorial_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:36:23.241993+00:00
-- url     : https://prove2.me/submissions/3ae6fa3d-2b20-47f0-a38c-3ab394349570

import Mathlib

open Real Finset Chebyshev

namespace S218LM

lemma Icc_one_eq (n : ℕ) : Icc 1 n = Ioc 0 n := by ext; simp; omega

lemma log_factorial_eq (n : ℕ) :
    log (n.factorial : ℝ) =
      ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ) := by
  rw [Icc_one_eq, ← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum,
    ArithmeticFunction.vonMangoldt_mul_zeta]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      ih, Finset.sum_Ioc_succ_top (Nat.zero_le k), add_comm]
    simp [ArithmeticFunction.log_apply]

lemma mem_primesLE' {n p : ℕ} : p ∈ Nat.primesLE n ↔ p ≤ n ∧ p.Prime := by
  simp [Nat.primesLE, Nat.mem_primesBelow, Nat.lt_succ_iff]

lemma primesLE_sub (n : ℕ) : Nat.primesLE n ⊆ Icc 1 n := by
  intro p hp
  rw [mem_primesLE'] at hp
  exact mem_Icc.2 ⟨hp.2.one_lt.le, hp.1⟩

lemma div_le_floor_add_one (n m : ℕ) (hm : 0 < m) :
    (n : ℝ) / m ≤ ((n / m : ℕ) : ℝ) + 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  have h := Nat.div_add_mod n m
  have hlt := Nat.mod_lt n hm
  have : (n : ℝ) = m * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by exact_mod_cast h.symm
  have : ((n % m : ℕ) : ℝ) ≤ m := by exact_mod_cast hlt.le
  nlinarith

lemma psi_nat (n : ℕ) : ψ (n : ℝ) = ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m := by
  rw [Chebyshev.psi, Nat.floor_natCast, Icc_one_eq]

lemma pp_inj (n : ℕ) : Set.InjOn (fun x : ℕ × ℕ => x.1 ^ x.2)
    ((Nat.primesLE n ×ˢ Icc 1 n : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  rintro ⟨p, k⟩ hx ⟨q, j⟩ hy hpq
  simp only [coe_product, Set.mem_prod, mem_coe, mem_Icc] at hx hy
  have hp := (mem_primesLE'.1 hx.1).2
  have hq := (mem_primesLE'.1 hy.1).2
  simp only at hpq
  have hpq' : p = q := by
    have : p ∣ q ^ j := hpq ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow this)
  subst hpq'
  have := Nat.pow_right_injective hp.two_le hpq
  simp [this]

lemma geom_le (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / (p : ℝ) ^ k ≤ 1 / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx0 : (0:ℝ) ≤ 1 / p := by positivity
  have hx1 : (1:ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) hx0 hx1
  have he : Icc 1 n = Ico 1 (n + 1) := by ext; simp
  simp_rw [one_div_pow] at h
  rw [he]
  calc ∑ k ∈ Ico 1 (n + 1), (1 : ℝ) / (p : ℝ) ^ k ≤ (1 / (p:ℝ)) ^ 1 / (1 - 1 / p) := by
        simpa [one_div] using h
    _ = 1 / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have : (p:ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring

lemma vm_sum_le (n : ℕ) :
    ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m ≤
      ∑ p ∈ Nat.primesLE n, (log p / p + log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
  set T := (Nat.primesLE n ×ˢ Icc 1 n : Finset (ℕ × ℕ))
  have hsub : (Icc 1 n).filter IsPrimePow ⊆ T.image (fun x => x.1 ^ x.2) := by
    intro m hm
    rw [mem_filter, mem_Icc] at hm
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hm.2
    rw [mem_image]
    refine ⟨(p, k), ?_, rfl⟩
    rw [mem_product, mem_primesLE', mem_Icc]
    have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have h2 : k ≤ p ^ k := (Nat.lt_pow_self hp.one_lt).le
    exact ⟨⟨by omega, hp⟩, by omega, by omega⟩
  have hnn : ∀ m : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt m / m :=
    fun m => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg m)
  calc ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m
      = ∑ m ∈ (Icc 1 n).filter IsPrimePow, ArithmeticFunction.vonMangoldt m / m := by
        rw [sum_filter]
        apply sum_congr rfl
        intro m _
        split_ifs with h
        · rfl
        · rw [ArithmeticFunction.vonMangoldt_apply, if_neg h, zero_div]
    _ ≤ ∑ m ∈ T.image (fun x => x.1 ^ x.2), ArithmeticFunction.vonMangoldt m / m :=
        sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hnn m)
    _ = ∑ x ∈ T, ArithmeticFunction.vonMangoldt (x.1 ^ x.2) / ((x.1 ^ x.2 : ℕ) : ℝ) :=
        sum_image (pp_inj n)
    _ = ∑ p ∈ Nat.primesLE n, ∑ k ∈ Icc 1 n, log p * (1 / (p : ℝ) ^ k) := by
        rw [sum_product]
        apply sum_congr rfl
        intro p hp
        apply sum_congr rfl
        intro k hk
        have hp' := (mem_primesLE'.1 hp).2
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by simp at hk; omega),
          ArithmeticFunction.vonMangoldt_apply_prime hp']
        push_cast; ring
    _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        have hp' := (mem_primesLE'.1 hp).2
        rw [← mul_sum]
        have := mul_le_mul_of_nonneg_left (geom_le p hp' n) (Real.log_natCast_nonneg p)
        calc log p * ∑ k ∈ Icc 1 n, (1 : ℝ) / (p : ℝ) ^ k
            ≤ log p * (1 / p + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := this
          _ = _ := by ring

end S218LM

theorem solution (n : ℕ) :
    log (n.factorial : ℝ) ≤
      (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p +
        (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [← mul_add, ← sum_add_distrib]
  calc log (n.factorial : ℝ) ≤ (n : ℝ) * ∑ m ∈ Icc 1 n, ArithmeticFunction.vonMangoldt m / m := by
        rw [S218LM.log_factorial_eq, mul_sum]
        apply sum_le_sum
        intro m _
        have h := mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ) (m := n) (n := m))
          (ArithmeticFunction.vonMangoldt_nonneg (n := m))
        calc ArithmeticFunction.vonMangoldt m * ((n / m : ℕ) : ℝ)
            ≤ ArithmeticFunction.vonMangoldt m * ((n : ℝ) / m) := h
          _ = (n : ℝ) * (ArithmeticFunction.vonMangoldt m / m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (S218LM.vm_sum_le n) (Nat.cast_nonneg n)
