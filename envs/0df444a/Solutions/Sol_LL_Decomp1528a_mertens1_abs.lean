-- Prove2me | solution 1 for LL_Decomp1528a.mertens1_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:54:05.468869+00:00
-- url     : https://prove2.me/submissions/3e09a88d-e073-4ab6-85cc-3b7a85edb652

import Mathlib

open Real Finset Chebyshev


namespace S218MH

def L2 : ℚ := 6931471808 / 10^10
def L3 : ℚ := 109861228877 / 10^11

lemma log2_le : Real.log 2 ≤ ((L2 : ℚ) : ℝ) := by
  have := Real.log_two_lt_d9; unfold L2; push_cast; norm_num at this ⊢; linarith

lemma log3_le : Real.log 3 ≤ ((L3 : ℚ) : ℝ) := by
  have := (abs_sub_le_iff.1 Real.log_three_near_10).1; unfold L3; push_cast; norm_num at this ⊢; linarith

lemma log_one_add_le {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ t - t^2/2 + t^3/3 := by
  let g : ℝ → ℝ := fun t => t - t^2/2 + t^3/3 - Real.log (1 + t)
  have hd : ∀ s, 0 ≤ s → HasDerivAt g (1 - s + s^2 - 1/(1+s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 s := by simpa using (hasDerivAt_id s).const_add 1
    have h2 := h1.log (by linarith)
    have h3 : HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3) (1 - s + s^2) s := by
      have := (((hasDerivAt_id' s).sub ((hasDerivAt_pow 2 s).div_const 2)).add
        ((hasDerivAt_pow 3 s).div_const 3))
      exact this.congr_deriv (by norm_num)
    exact (h3.sub h2).congr_deriv (by ring)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Ici] at hs; exact (hd s (le_of_lt hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs' : (0:ℝ) < s := hs
      rw [(hd s hs'.le).deriv]
      have : 1 - s + s^2 - 1/(1+s) = s^3/(1+s) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp [g] at this
  linarith

def B (p a b : ℕ) : ℚ :=
  let t : ℚ := (p : ℚ) / (2^a * 3^b) - 1
  a * L2 + b * L3 + (t - t^2/2 + t^3/3)

lemma log_le_B (p a b : ℕ) (h : 2^a * 3^b ≤ p) : Real.log p ≤ ((B p a b : ℚ) : ℝ) := by
  have hm : (0:ℝ) < 2^a * 3^b := by positivity
  have hmp : (2:ℝ)^a * 3^b ≤ p := by exact_mod_cast h
  set t : ℝ := (p : ℝ) / (2^a * 3^b) - 1 with ht
  have ht0 : 0 ≤ t := by rw [ht, sub_nonneg, le_div_iff₀ hm]; linarith
  have hp : (p : ℝ) = (2^a * 3^b) * (1 + t) := by rw [ht]; field_simp; ring
  have hlog : Real.log p = a * Real.log 2 + b * Real.log 3 + Real.log (1 + t) := by
    rw [hp, Real.log_mul hm.ne' (by linarith), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  rw [hlog]
  have e : ((B p a b : ℚ) : ℝ) = a * ((L2:ℚ):ℝ) + b * ((L3:ℚ):ℝ) + (t - t^2/2 + t^3/3) := by
    simp only [B, ht]; push_cast; ring
  rw [e]
  have := log_one_add_le ht0
  have h2 := log2_le; have h3 := log3_le
  have : (a:ℝ) * Real.log 2 ≤ a * ((L2:ℚ):ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have : (b:ℝ) * Real.log 3 ≤ b * ((L3:ℚ):ℝ) := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

def best (p : ℕ) : ℕ × ℕ :=
  (List.range 11).foldl (fun acc a => (List.range 7).foldl (fun acc b =>
    if 2^a*3^b ≤ p ∧ 2^acc.1*3^acc.2 < 2^a*3^b then (a,b) else acc) acc) (0,0)

def T (p : ℕ) : ℕ :=
  if 2^(best p).1 * 3^(best p).2 ≤ p then
    (⌈B p (best p).1 (best p).2 * 10^12 / (p * (p - 1))⌉).toNat
  else 10^15

lemma term_le (p : ℕ) (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (T p : ℝ) / 10^12 := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0:ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  rw [div_le_div_iff₀ hden (by norm_num)]
  unfold T
  split_ifs with h
  · have h1 := log_le_B p _ _ h
    set q : ℚ := B p (best p).1 (best p).2 * 10^12 / (p * (p - 1)) with hq
    have hc : q ≤ ((⌈q⌉.toNat : ℕ) : ℚ) := by
      have := Int.le_ceil q
      have h2 : (⌈q⌉ : ℚ) ≤ ((⌈q⌉.toNat : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
      push_cast at h2 ⊢; linarith
    have hc' : (q : ℝ) ≤ ((⌈q⌉.toNat : ℕ) : ℝ) := by exact_mod_cast hc
    have hqr : (q : ℝ) = ((B p (best p).1 (best p).2 : ℚ) : ℝ) * 10^12 / (p * (p - 1)) := by
      rw [hq]; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [hqr, div_le_iff₀ hden] at hc'
    nlinarith
  · have : Real.log p ≤ p := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    push_cast
    nlinarith

def isP (n : ℕ) : Bool := 2 ≤ n && (List.range 32).all (fun d => d < 2 || n ≤ d || n % d != 0)

lemma isP_of_prime {n : ℕ} (h : n.Prime) : isP n = true := by
  simp only [isP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨h.two_le, fun d _ => ?_⟩
  by_cases h1 : d < 2
  · simp [h1]
  by_cases h2 : n ≤ d
  · simp [h2]
  right; intro hmod
  have := (Nat.prime_def.1 h).2 d (Nat.dvd_of_mod_eq_zero hmod)
  omega

lemma check : ∑ n ∈ (range 1001).filter (fun n => isP n = true), T n ≤ 754500000000 := by
  decide +kernel

theorem head_le :
    ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7545 := by
  have hsub : Nat.primesLE 1000 ⊆ (range 1001).filter (fun n => isP n = true) := by
    intro p hp
    simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
    simp only [mem_filter, mem_range]
    exact ⟨hp.1, isP_of_prime hp.2⟩
  calc ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ Nat.primesLE 1000, (T p : ℝ) / 10^12 := by
        apply sum_le_sum; intro p hp
        simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
        exact term_le p hp.2.two_le
    _ ≤ ∑ p ∈ (range 1001).filter (fun n => isP n = true), (T p : ℝ) / 10^12 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ((∑ p ∈ (range 1001).filter (fun n => isP n = true), T p : ℕ) : ℝ) / 10^12 := by
        rw [Nat.cast_sum, sum_div]
    _ ≤ (754500000000 : ℝ) / 10^12 := by
        gcongr; exact_mod_cast check
    _ = 0.7545 := by norm_num

end S218MH



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

theorem fact_le (n : ℕ) :
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

theorem fact_ge (n : ℕ) :
    (n : ℝ) * ∑ p ∈ Nat.primesLE n, log p / p - θ n ≤ log (n.factorial : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, mul_sum, ← sum_sub_distrib, S218LM.log_factorial_eq]
  calc ∑ p ∈ Nat.primesLE n, ((n:ℝ) * (log p / p) - log p)
      ≤ ∑ p ∈ Nat.primesLE n, ArithmeticFunction.vonMangoldt p * ((n / p : ℕ) : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpp := (S218LM.mem_primesLE'.1 hp).2
        rw [ArithmeticFunction.vonMangoldt_apply_prime hpp]
        have := S218LM.div_le_floor_add_one n p hpp.pos
        have hl : 0 ≤ log (p:ℝ) := Real.log_natCast_nonneg p
        have : (n:ℝ) * (log p / p) = log p * ((n:ℝ) / p) := by ring
        rw [this]; nlinarith
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (S218LM.primesLE_sub n)
        (fun _ _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))

theorem head_split (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) +
        ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
  have hnn : ∀ m : ℕ, 0 ≤ log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
    intro m
    apply div_nonneg (Real.log_natCast_nonneg m)
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : (1:ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE n) (fun p => p ≤ 1000)]
  refine add_le_add ?_ ?_
  · apply sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => hnn m)
    intro p hp
    rw [mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    rw [Nat.primesLE, Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.2⟩
  · apply sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => hnn m)
    intro p hp
    rw [mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    rw [mem_Ioc]
    omega

theorem small_case {x : ℝ} (hx : 1 ≤ x) (hx5 : x < 5) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  have hfl : ⌊x⌋₊ ≤ 4 := by
    have : ⌊x⌋₊ < 5 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast hx5)
    omega
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ {2, 3} := by
    intro p hp
    simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
    have : p < 5 := by omega
    interval_cases p <;> simp_all <;> norm_num at hp
  have hterm : ∀ p : ℕ, 0 ≤ log p / p ∧ log p / p ≤ 1 := by
    intro p
    refine ⟨div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p), ?_⟩
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp
    · have hp : (0:ℝ) < p := by exact_mod_cast h
      rw [div_le_one hp]
      linarith [Real.log_le_sub_one_of_pos hp]
  have hS0 : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p := sum_nonneg fun p _ => (hterm p).1
  have hS2 : ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p ≤ 2 := by
    calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p ≤ ∑ p ∈ ({2, 3} : Finset ℕ), log p / p :=
          sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => (hterm p).1)
      _ ≤ 2 := by
        rw [sum_pair (by norm_num)]
        linarith [(hterm 2).2, (hterm 3).2]
  have hl0 : 0 ≤ log x := Real.log_nonneg hx
  have hl2 : log x ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := x / 3) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    have h3 : log 3 < 1.11 := by
      have := Real.log_le_sub_one_of_pos (x := 3 / Real.exp 1) (by positivity)
      rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
      have : 3 / Real.exp 1 < 1.1037 := by
        rw [div_lt_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
      linarith
    linarith
  rw [abs_le]; constructor <;> linarith

theorem log_floor {x : ℝ} (hx : 5 ≤ x) : log x ≤ log (⌊x⌋₊ : ℝ) + 0.2 := by
  have hf5 : (5:ℝ) ≤ ⌊x⌋₊ := by
    have : 5 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have hfpos : (0:ℝ) < ⌊x⌋₊ := by linarith
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have h := Real.log_le_sub_one_of_pos (x := x / ⌊x⌋₊) (by positivity)
  rw [Real.log_div (by linarith) hfpos.ne'] at h
  have : x / ⌊x⌋₊ - 1 ≤ 0.2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hfpos]; nlinarith
  linarith

end S218LM


namespace S218LT

noncomputable def f (m : ℝ) : ℝ := (log m + 2) / m

lemma step {m : ℝ} (hm : 2 ≤ m) :
    log m / (m * (m - 1)) ≤ f (m - 1) - f m := by
  unfold f
  have h1 : 0 < m - 1 := by linarith
  have h0 : 0 < m := by linarith
  have hkey : m * (log m - log (m - 1)) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (x := m / (m - 1)) (by positivity)
    rw [Real.log_div h0.ne' h1.ne'] at h
    have he : m / (m - 1) - 1 = 1 / (m - 1) := by field_simp; ring
    rw [he] at h
    have : m * (1 / (m - 1)) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ h1]; linarith
    calc m * (log m - log (m - 1)) ≤ m * (1 / (m - 1)) := mul_le_mul_of_nonneg_left h h0.le
      _ ≤ 2 := this
  rw [le_sub_iff_add_le, div_add_div _ _ (by positivity) h0.ne', div_le_div_iff₀ (by positivity) h1]
  nlinarith [mul_pos h0 h1]

lemma f_nonneg {m : ℝ} (hm : 1 ≤ m) : 0 ≤ f m :=
  div_nonneg (by linarith [Real.log_nonneg hm]) (by linarith)

lemma tele (k : ℕ) :
    ∑ m ∈ Ioc 1000 (1000 + k), log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ f 1000 - f ((1000 + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 1000 + (k + 1) = (1000 + k) + 1 by ring, sum_Ioc_succ_top (by omega)]
    have := step (m := ((1000 + k + 1 : ℕ) : ℝ)) (by push_cast; linarith)
    have hc : ((1000 + k + 1 : ℕ) : ℝ) - 1 = ((1000 + k : ℕ) : ℝ) := by push_cast; ring
    rw [hc] at this ⊢
    linarith

theorem tail_le (n : ℕ) :
    ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 0.009 := by
  have hf : S218LT.f 1000 ≤ 0.009 := by
    unfold S218LT.f
    have hl : log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h7]
      have := Real.exp_one_gt_d9
      calc (1000:ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
        _ ≤ Real.exp 1 ^ 7 := by gcongr
    rw [div_le_iff₀ (by norm_num)]; linarith
  rcases le_or_gt n 1000 with h | h
  · rw [Ioc_eq_empty (by omega), sum_empty]; norm_num
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have := S218LT.tele k
    have := S218LT.f_nonneg (m := ((1000 + k : ℕ) : ℝ)) (by push_cast; linarith)
    linarith

end S218LT

open S218LM in
theorem solution {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  rcases lt_or_ge x 5 with h5 | h5
  · exact small_case hx h5
  set n := ⌊x⌋₊ with hn
  set S := ∑ p ∈ Nat.primesLE n, log p / p with hS
  have hn5 : (5:ℝ) ≤ n := by
    have : 5 ≤ n := Nat.le_floor (by exact_mod_cast h5)
    exact_mod_cast this
  have hnpos : (0:ℝ) < n := by linarith
  have hnx : (n:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hH : ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7635 := by
    have := head_split n; have := S218MH.head_le; have := S218LT.tail_le n; linarith
  have hA := fact_ge n
  have hB := fact_le n
  have hlo : (n:ℝ) * log n - n ≤ log (n.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := (n:ℝ)) hnpos.le n
    have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [div_le_iff₀ hf] at h
    have := Real.log_le_log (by positivity) h
    rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp, Real.log_pow] at this
    linarith
  have hhi : log (n.factorial : ℝ) ≤ n * log n := by
    have h : (n.factorial : ℝ) ≤ (n:ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    have := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h
    rwa [Real.log_pow] at this
  have hθ : θ (n:ℝ) ≤ log 4 * n := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  have h4 : log 4 < 1.39 := by
    have : log (4:ℝ) = 2 * log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have hlx : log (n:ℝ) ≤ log x := Real.log_le_log hnpos hnx
  have hxl := log_floor h5
  have hup : S ≤ log n + 1.39 := by
    have : (n:ℝ) * S ≤ n * (log n + 1.39) := by nlinarith
    exact le_of_mul_le_mul_left this hnpos
  have hdn : S ≥ log n - 1.7635 := by
    have : (n:ℝ) * (log n - 1.7635) ≤ n * S := by nlinarith
    exact le_of_mul_le_mul_left this hnpos
  rw [abs_le]; constructor <;> linarith
