-- Prove2me | solution 1 for LL_Decomp1528b.mertens_prod_lower
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:08.535901+00:00
-- url     : https://prove2.me/submissions/1bdffd8d-0bac-4c3a-a9aa-d7696066cb12

import Mathlib

open Real Finset Filter Topology

theorem ChMeAux.log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : log y ≤ (y - y⁻¹) / 2 := by
  have hmono : MonotoneOn (fun y : ℝ => (y - y⁻¹) / 2 - log y) (Set.Ici 1) := by
    have hd : ∀ y : ℝ, 1 < y → HasDerivAt (fun y : ℝ => (y - y⁻¹) / 2 - log y)
        ((1 + (y ^ 2)⁻¹) / 2 - y⁻¹) y := by
      intro y hy
      have hy0 : y ≠ 0 := by positivity
      have h1 := ((hasDerivAt_id y).sub (hasDerivAt_inv hy0)).div_const 2
      have h2 := h1.sub (Real.hasDerivAt_log hy0)
      exact h2.congr_deriv (by ring)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro y hy
      have : 1 ≤ y := hy
      have hy0 : y ≠ 0 := by positivity
      have h1 := ((hasDerivAt_id y).sub (hasDerivAt_inv hy0)).div_const 2
      have h2 := h1.sub (Real.hasDerivAt_log hy0)
      exact h2.continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : (1 : ℝ) < y := hy
      rw [(hd y hy').deriv]
      have hy0 : 0 < y := by positivity
      have : (1 + (y ^ 2)⁻¹) / 2 - y⁻¹ = (1 - y⁻¹) ^ 2 / 2 := by
        field_simp
        ring
      rw [this]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  simp at this
  linarith

theorem ChMeAux.neg_log_one_sub_inv_bounds {p : ℝ} (hp : 2 ≤ p) :
    0 ≤ -log (1 - 1 / p) - 1 / p ∧ -log (1 - 1 / p) - 1 / p ≤ 1 / (2 * p * (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq : 0 < 1 - 1 / p := by
    rw [sub_pos, div_lt_one hp0]; linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hq
    linarith
  · have hy : (1 : ℝ) ≤ p / (p - 1) := by
      rw [le_div_iff₀ hp1]; linarith
    have h := ChMeAux.log_le_half_sub_inv hy
    have e1 : -log (1 - 1 / p) = log (p / (p - 1)) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [e1]
    have e2 : (p / (p - 1) - (p / (p - 1))⁻¹) / 2 - 1 / p = 1 / (2 * p * (p - 1)) := by
      field_simp
      ring
    linarith

theorem ChMeAux.log_factorial_eq (N : ℕ) :
    Real.log (Nat.factorial N) = ∑ p ∈ Nat.primesLE N, ((Nat.factorial N).factorization p : ℝ) * Real.log p := by
  have h : (Nat.factorial N) = ∏ p ∈ Nat.primesLE N, p ^ ((Nat.factorial N).factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero N)]
    rw [Finsupp.prod]
    apply Finset.prod_subset
    · intro p hp
      rw [Nat.support_factorization] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      exact Nat.mem_primesLE.mpr ⟨(hpp.dvd_factorial.mp hd), hpp⟩
    · intro p _ hp
      simp [Finsupp.notMem_support_iff.mp hp]
  conv_lhs => rw [h]
  rw [Nat.cast_prod, Real.log_prod]
  · refine sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Nat.prime_of_mem_primesLE hp).pos
    positivity

theorem ChMeAux.div_le_factorization (N p : ℕ) (hp : p ∈ Nat.primesLE N) :
    N / p ≤ (Nat.factorial N).factorization p := by
  obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
  rw [Nat.factorization_factorial hpp (Nat.lt_succ_self (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N).succ := by
    simp only [mem_Ico, Nat.succ_eq_add_one]
    have : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
    omega
  have := single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

theorem ChMeAux.sum_log_div_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Nat.primesLE, Nat.primesBelow]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤
      Real.log (Nat.factorial N) + Chebyshev.theta N := by
    rw [ChMeAux.log_factorial_eq, Finset.mul_sum, Chebyshev.theta_eq_sum_primesLE_log, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hq := ChMeAux.div_le_factorization N p hp
    have hq' : ((N / p : ℕ) : ℝ) ≤ ((Nat.factorial N).factorization p : ℝ) := by exact_mod_cast hq
    have hN1 : (N : ℝ) ≤ p * ((N / p : ℕ) : ℝ) + p := by
      have h := Nat.div_add_mod N p
      have h2 := Nat.mod_lt N hpp.pos
      have : N ≤ p * (N / p) + p := by omega
      exact_mod_cast this
    have : (N : ℝ) * (Real.log p / p) ≤ (((N / p : ℕ) : ℝ) + 1) * Real.log p := by
      rw [mul_div_assoc', div_le_iff₀ hp0]
      nlinarith
    nlinarith
  have h2 : Real.log (Nat.factorial N) ≤ N * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
      (by exact_mod_cast Nat.factorial_le_pow N)
  have h3 := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

theorem ChMeAux.primesLE_succ_sum (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      ∑ p ∈ Nat.primesLE N, f p + if (N + 1).Prime then f (N + 1) else 0 := by
  by_cases hp : (N + 1).Prime
  · have : Nat.primesLE (N + 1) = insert (N + 1) (Nat.primesLE N) := by
      ext q
      simp only [Nat.mem_primesLE, mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_eq_of_le h1 with h | h
        · right; exact ⟨by omega, h2⟩
        · left; exact h
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨le_rfl, hp⟩
        · exact ⟨by omega, h2⟩
    rw [this, sum_insert (by simp [Nat.mem_primesLE]), if_pos hp, add_comm]
  · have : Nat.primesLE (N + 1) = Nat.primesLE N := by
      ext q
      simp only [Nat.mem_primesLE]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_eq_of_le h1 with h | h
        · exact ⟨by omega, h2⟩
        · subst h; exact absurd h2 hp
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rw [this, if_neg hp, add_zero]

theorem ChMeAux.step_alg {S A a b L L' C K M : ℝ} (hL : 0 < L) (hLL : L ≤ L')
    (hb : b = a / L') (hA : A ≤ L + C)
    (ih : S - A / L ≤ Real.log L - K + C * (M - 1 / L)) :
    (S + b) - (A + a) / L' ≤ Real.log L' - K + C * (M - 1 / L') := by
  have hL' : 0 < L' := lt_of_lt_of_le hL hLL
  have e1 : (S + b) - (A + a) / L' = (S - A / L) + A * (1 / L - 1 / L') := by
    rw [hb]; field_simp; ring
  have h1 : 1 / L' ≤ 1 / L := one_div_le_one_div_of_le hL hLL
  have e2 : A * (1 / L - 1 / L') ≤ (L + C) * (1 / L - 1 / L') :=
    mul_le_mul_of_nonneg_right hA (by linarith)
  have e3 : (L + C) * (1 / L - 1 / L') = (1 - L / L') + C * (1 / L - 1 / L') := by
    field_simp
  have e4 : 1 - L / L' ≤ Real.log L' - Real.log L := by
    have := Real.log_le_sub_one_of_pos (div_pos hL hL')
    rw [Real.log_div hL.ne' hL'.ne'] at this
    linarith
  linarith

theorem ChMeAux.sum_inv_aux (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - (∑ p ∈ Nat.primesLE N, Real.log p / p) / Real.log N
      ≤ Real.log (Real.log N) - Real.log (Real.log 2) +
        Real.log 4 * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h2 : Nat.primesLE 2 = {2} := by
      ext q
      simp only [Nat.mem_primesLE, mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        have := h2.two_le
        omega
      · rintro rfl; exact ⟨le_rfl, Nat.prime_two⟩
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [h2]
    simp only [sum_singleton, Nat.cast_ofNat]
    have : (Real.log 2 / 2) / Real.log 2 = 1 / 2 := by field_simp
    rw [this]
    norm_num
  | succ N hN ih =>
    have hNr : (1 : ℝ) < N := by exact_mod_cast hN
    have hL : 0 < Real.log N := Real.log_pos hNr
    have hLL : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have hL' : 0 < Real.log ((N + 1 : ℕ) : ℝ) := lt_of_lt_of_le hL hLL
    rw [ChMeAux.primesLE_succ_sum (fun p => (1 : ℝ) / p),
      ChMeAux.primesLE_succ_sum (fun p => Real.log p / p)]
    refine ChMeAux.step_alg (a := if (N + 1).Prime then Real.log ((N + 1 : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ) else 0)
      hL hLL ?_ (ChMeAux.sum_log_div_le N) ih
    split_ifs
    · field_simp
    · simp

theorem ChMeAux.sum_inv_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤ 4 + Real.log (Real.log N) := by
  have h := ChMeAux.sum_inv_aux N hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos hNr
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA := ChMeAux.sum_log_div_le N
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2a := Real.log_two_gt_d9
  have hlog2b := Real.log_two_lt_d9
  have hll : -1 ≤ Real.log (Real.log 2) := by
    have : Real.log (1 / 2) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [one_div, Real.log_inv] at this
    linarith
  have h5 : (∑ p ∈ Nat.primesLE N, Real.log p / p) / Real.log N ≤ 1 + Real.log 4 / Real.log N := by
    rw [div_le_iff₀ hL]
    have : (1 + Real.log 4 / Real.log N) * Real.log N = Real.log N + Real.log 4 := by
      field_simp
    linarith
  have h6 : Real.log 4 * (1 / Real.log 2 - 1 / Real.log N) = 2 - Real.log 4 / Real.log N := by
    rw [h4]; field_simp
  linarith

theorem ChMeAux.sum_inv_mul_sub_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (2 * p * (p - 1)) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Nat.primesLE 0 = ∅ := by
      ext q
      simp only [Nat.mem_primesLE, notMem_empty, iff_false]
      rintro ⟨h1, h2⟩
      have := h2.two_le
      omega
    rw [this]; simp
  have key : ∀ N : ℕ, 1 ≤ N →
      ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (2 * p * (p - 1)) ≤ (1 / 2) * (1 - 1 / (N : ℝ)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have : Nat.primesLE 1 = ∅ := by
        ext q
        simp only [Nat.mem_primesLE, notMem_empty, iff_false]
        rintro ⟨h1, h2⟩
        have := h2.two_le
        omega
      rw [this]; simp
    | succ N hN ih =>
      rw [ChMeAux.primesLE_succ_sum (fun p => (1 : ℝ) / (2 * p * (p - 1)))]
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpos : (0 : ℝ) < N := by linarith
      by_cases hp : (N + 1).Prime
      · rw [if_pos hp]
        have : (1 : ℝ) / (2 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) - 1)) =
            (1 / 2) * (1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) := by
          have hne : (N : ℝ) ≠ 0 := hpos.ne'
          push_cast
          rw [add_sub_cancel_right]
          field_simp
          ring
        rw [this]
        linarith
      · rw [if_neg hp, add_zero]
        have : 1 / ((N + 1 : ℕ) : ℝ) ≤ 1 / (N : ℝ) := by
          apply one_div_le_one_div_of_le hpos; push_cast; linarith
        linarith
  have := key N hN
  have h2 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  linarith

theorem solution {x : ℝ} (hx : 2 ≤ x) :
    1 / (1500 * log x) ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (1 : ℝ) / p) := by
  set M := ⌊x⌋₊ with hM
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hx)
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hMx : (M : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hLM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogMx : Real.log M ≤ Real.log x := Real.log_le_log (by linarith) hMx
  have hlx : 0 < Real.log x := lt_of_lt_of_le hLM hlogMx
  have hq : ∀ p ∈ Nat.primesLE M, 0 < 1 - (1 : ℝ) / p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    rw [sub_pos, div_lt_one (by linarith)]
    exact hp1
  have hP0 : 0 < ∏ p ∈ Nat.primesLE M, (1 - (1 : ℝ) / p) := prod_pos hq
  have hlogP : Real.log (∏ p ∈ Nat.primesLE M, (1 - (1 : ℝ) / p)) =
      ∑ p ∈ Nat.primesLE M, Real.log (1 - (1 : ℝ) / p) :=
    Real.log_prod (fun p hp => (hq p hp).ne')
  have hsum : -(∑ p ∈ Nat.primesLE M, (1 : ℝ) / p + ∑ p ∈ Nat.primesLE M, (1 : ℝ) / (2 * p * (p - 1)))
      ≤ ∑ p ∈ Nat.primesLE M, Real.log (1 - (1 : ℝ) / p) := by
    rw [← sum_add_distrib, ← sum_neg_distrib]
    refine sum_le_sum fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have := (ChMeAux.neg_log_one_sub_inv_bounds hp2).2
    linarith
  have hS := ChMeAux.sum_inv_le M hM2
  have hC := ChMeAux.sum_inv_mul_sub_le M
  have hlog1500 : 5 ≤ Real.log 1500 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 : Real.exp 5 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    calc Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 :=
          pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 5
      _ ≤ 1500 := by norm_num
  have hllog : Real.log (Real.log M) ≤ Real.log (Real.log x) := Real.log_le_log hLM hlogMx
  rw [← Real.log_le_log_iff (by positivity) hP0, hlogP]
  rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hlx.ne']
  linarith
