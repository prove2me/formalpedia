-- Prove2me | solution 1 for LL_Decomp1528b.integral_A_sub
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:10.669201+00:00
-- url     : https://prove2.me/submissions/a2741b68-9280-4be3-bd57-a4d5437feb87

import Mathlib

open Real Finset Filter Topology

theorem MxAux.log_factorial_eq (N : ℕ) :
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

theorem MxAux.div_le_factorization (N p : ℕ) (hp : p ∈ Nat.primesLE N) :
    N / p ≤ (Nat.factorial N).factorization p := by
  obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
  rw [Nat.factorization_factorial hpp (Nat.lt_succ_self (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N).succ := by
    simp only [mem_Ico, Nat.succ_eq_add_one]
    have : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
    omega
  have := single_le_sum (f := fun i => N / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using this

theorem MxAux.sum_log_div_le (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Nat.primesLE, Nat.primesBelow]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤
      Real.log (Nat.factorial N) + Chebyshev.theta N := by
    rw [MxAux.log_factorial_eq, Finset.mul_sum, Chebyshev.theta_eq_sum_primesLE_log, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hq := MxAux.div_le_factorization N p hp
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

theorem MxAux.primesLE_succ_sum (f : ℕ → ℝ) (N : ℕ) :
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

theorem MxAux.log_le_two_pow {p : ℝ} (hp : 0 < p) (k : ℕ) :
    Real.log p ≤ k * Real.log 2 + p / 2 ^ k - 1 := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hp h2)
  rw [Real.log_div hp.ne' h2.ne', Real.log_pow] at h
  linarith

theorem MxAux.T19 :
    ∑ p ∈ Nat.primesLE 19, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.73 := by
  have hP : Nat.primesLE 19 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hP]
  have hl2 := Real.log_two_lt_d9
  have h3 := MxAux.log_le_two_pow (p := 3) (by norm_num) 2
  have h5 := MxAux.log_le_two_pow (p := 5) (by norm_num) 2
  have h7 := MxAux.log_le_two_pow (p := 7) (by norm_num) 3
  have h11 := MxAux.log_le_two_pow (p := 11) (by norm_num) 3
  have h13 := MxAux.log_le_two_pow (p := 13) (by norm_num) 4
  have h17 := MxAux.log_le_two_pow (p := 17) (by norm_num) 4
  have h19 := MxAux.log_le_two_pow (p := 19) (by norm_num) 4
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num at *
  linarith

theorem MxAux.T_le_one (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have key : ∀ N : ℕ, 19 ≤ N →
      ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) + (Real.log N + 20 / 19) / N
      ≤ ∑ p ∈ Nat.primesLE 19, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) +
        (Real.log (19 : ℕ) + 20 / 19) / (19 : ℕ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => exact le_rfl
    | succ N hN ih =>
      rw [MxAux.primesLE_succ_sum (fun p => Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))]
      have hNr : (19 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < N := by linarith
      have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
        have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < N + 1) hN0)
        rw [Real.log_div (by linarith) hN0.ne'] at h
        have : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
        linarith
      have h1 : ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log N) ≤ 20 / 19 := by
        have h2 : ((N : ℝ) + 1) * (1 / N) ≤ 20 / 19 := by
          rw [mul_one_div, div_le_iff₀ hN0]; nlinarith
        calc ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log N)
            ≤ ((N : ℝ) + 1) * (1 / N) := mul_le_mul_of_nonneg_left hlog (by linarith)
          _ ≤ 20 / 19 := h2
      have hL : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
      have hq : Real.log ((N : ℝ) + 1) / (((N : ℝ) + 1) * (((N : ℝ) + 1) - 1))
          + (Real.log ((N : ℝ) + 1) + 20 / 19) / ((N : ℝ) + 1) ≤ (Real.log N + 20 / 19) / N := by
        have e : (Real.log N + 20 / 19) / N - (Real.log ((N : ℝ) + 1) / (((N : ℝ) + 1) * (((N : ℝ) + 1) - 1))
            + (Real.log ((N : ℝ) + 1) + 20 / 19) / ((N : ℝ) + 1)) =
            (20 / 19 - ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log N)) / (N * ((N : ℝ) + 1)) := by
          rw [add_sub_cancel_right]
          field_simp
          ring
        have : 0 ≤ (20 / 19 - ((N : ℝ) + 1) * (Real.log ((N : ℝ) + 1) - Real.log N)) / (N * ((N : ℝ) + 1)) :=
          div_nonneg (by linarith) (by positivity)
        linarith
      push_cast
      have hq0 : 0 ≤ Real.log ((N : ℝ) + 1) / (((N : ℝ) + 1) * (((N : ℝ) + 1) - 1)) := by
        apply div_nonneg hL
        have : (0 : ℝ) ≤ (N : ℝ) + 1 - 1 := by linarith
        positivity
      split_ifs
      · linarith
      · linarith
  by_cases hN : 19 ≤ N
  · have h := key N hN
    have hA := MxAux.T19
    have hl2 := Real.log_two_lt_d9
    have h19 := MxAux.log_le_two_pow (p := 19) (by norm_num) 4
    have hnn : 0 ≤ (Real.log N + 20 / 19) / N := by
      have : 0 ≤ Real.log N := Real.log_natCast_nonneg N
      positivity
    norm_num at h h19
    linarith
  · rw [not_le] at hN
    refine le_trans ?_ (le_trans MxAux.T19 (by norm_num))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      have hpp := Nat.prime_of_mem_primesLE hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      apply div_nonneg this
      nlinarith

theorem MxAux.sum_log_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 2 + (Real.log N + Real.log (2 * π)) / (2 * N) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hst := Stirling.le_log_factorial_stirling (n := N) (by omega)
  have hup : Real.log (Nat.factorial N) ≤ N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
      ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [MxAux.log_factorial_eq, ← sum_add_distrib, Finset.mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hpp := Nat.prime_of_mem_primesLE hp
    have := Fact.mk hpp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hv : (((Nat.factorial N).factorization p : ℕ) : ℝ) * ((p : ℝ) - 1) ≤ N := by
      have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := N) (by omega)
      rw [← Nat.factorization_def _ hpp] at h
      have h' : ((p - 1) * (Nat.factorial N).factorization p : ℕ) ≤ N := h.le
      have : (((p - 1 : ℕ) : ℝ)) * (((Nat.factorial N).factorization p : ℕ) : ℝ) ≤ N := by
        exact_mod_cast h'
      rw [Nat.cast_sub hpp.one_le] at this
      simpa [mul_comm] using this
    have e : (N : ℝ) * (Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) =
        N * Real.log p / ((p : ℝ) - 1) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e, le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right hv hlog]
  have hT := MxAux.T_le_one N
  have h2 : (N : ℝ) * Real.log N - N + Real.log N / 2 + Real.log (2 * π) / 2 ≤
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p + 1) := by
    have : (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log p / p +
      ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        N * (∑ p ∈ Nat.primesLE N, Real.log p / p + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hNr.le
    linarith
  have e2 : (N : ℝ) * (Real.log N - 2 + (Real.log N + Real.log (2 * π)) / (2 * N)) =
      N * Real.log N - 2 * N + (Real.log N + Real.log (2 * π)) / 2 := by
    field_simp
  have : (N : ℝ) * (Real.log N - 2 + (Real.log N + Real.log (2 * π)) / (2 * N)) ≤
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    rw [e2]; nlinarith
  exact le_of_mul_le_mul_left this hNr

theorem MxAux.abs_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log p / p) - Real.log t| ≤ 2 := by
  set N := ⌊t⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast ht)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htN : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have hN0 : (0 : ℝ) < N := by linarith
  have hl2 := Real.log_two_lt_d9
  rw [abs_le]
  constructor
  · have hlow := MxAux.sum_log_div_ge (N := N) (by omega)
    have hlogt : Real.log t ≤ Real.log N + 1 / N := by
      have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < N + 1) hN0)
      rw [Real.log_div (by linarith) hN0.ne'] at h
      have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      have := Real.log_le_log (by linarith) htN.le
      linarith
    have h12 : 2 ≤ Real.log N + Real.log (2 * π) := by
      have : (2 : ℝ) ≤ Real.log (N * (2 * π)) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
        have := Real.exp_one_lt_d9
        have := Real.pi_gt_three
        have h3 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) 2
        nlinarith
      rwa [Real.log_mul hN0.ne' (by positivity)] at this
    have h13 : 1 / (N : ℝ) ≤ (Real.log N + Real.log (2 * π)) / (2 * N) := by
      rw [div_le_div_iff₀ hN0 (by positivity)]
      nlinarith
    linarith
  · have hup := MxAux.sum_log_div_le N
    have hlogN : Real.log N ≤ Real.log t := Real.log_le_log hN0 hNt
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith

theorem MxAux.hasDerivAt_inv_log {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun t : ℝ => (Real.log t)⁻¹) (-(t⁻¹) / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  exact (Real.hasDerivAt_log ht0).inv hl

theorem solution {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |(∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2)) -
        (log (log x) - log (log y))| ≤ 2 * (1 / log y - 1 / log x) := by
  set g : ℝ → ℝ := fun t => (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2) with hg
  set k : ℝ → ℝ := fun t => t⁻¹ / Real.log t with hk
  set m : ℝ → ℝ := fun t => 2 * (t⁻¹ / Real.log t ^ 2) with hm
  have hge2 : ∀ t ∈ Set.uIcc y x, 2 ≤ t := by
    intro t ht
    rw [Set.uIcc_of_le hyx] at ht
    linarith [ht.1]
  have hpos : ∀ t, 2 ≤ t → 0 < Real.log t := fun t ht => Real.log_pos (by linarith)
  -- continuity of k and m
  have hkc : ContinuousOn k (Set.uIcc y x) := by
    intro t ht
    have ht2 := hge2 t ht
    have ht0 : t ≠ 0 := by positivity
    have hl := (hpos t ht2).ne'
    exact (((continuousAt_inv₀ ht0).div (Real.continuousAt_log ht0) hl)).continuousWithinAt
  have hmc : ContinuousOn m (Set.uIcc y x) := by
    intro t ht
    have ht2 := hge2 t ht
    have ht0 : t ≠ 0 := by positivity
    have hl := (hpos t ht2).ne'
    have : ContinuousAt (fun t : ℝ => 2 * (t⁻¹ / Real.log t ^ 2)) t :=
      continuousAt_const.mul
        ((continuousAt_inv₀ ht0).div ((Real.continuousAt_log ht0).pow 2) (pow_ne_zero 2 hl))
    exact this.continuousWithinAt
  have hki : IntervalIntegrable k MeasureTheory.volume y x := hkc.intervalIntegrable
  have hmi : IntervalIntegrable m MeasureTheory.volume y x := hmc.intervalIntegrable
  -- pointwise bound
  have hdiff : ∀ t, 2 ≤ t → |g t - k t| ≤ m t := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hl := hpos t ht
    have e : g t - k t = ((∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) - Real.log t) / (t * Real.log t ^ 2) := by
      simp only [hg, hk]
      field_simp
    rw [e, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2), div_le_iff₀ (by positivity)]
    have := MxAux.abs_sub_log_le ht
    simp only [hm]
    have e2 : 2 * (t⁻¹ / Real.log t ^ 2) * (t * Real.log t ^ 2) = 2 := by
      field_simp
    rw [e2]
    exact this
  -- integrability of g
  have hgm : Measurable g := by
    have h1 : Measurable (fun t : ℝ => ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log p / p) :=
      (measurable_from_top (f := fun n : ℕ => ∑ p ∈ Nat.primesLE n, Real.log p / p)).comp
        Nat.measurable_floor
    exact h1.div (measurable_id.mul (Real.measurable_log.pow_const 2))
  have hkm : Measurable k := measurable_inv.div Real.measurable_log
  have hgk : MeasureTheory.IntegrableOn (fun t => g t - k t) (Set.Ioc y x) := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := 2 / Real.log 2 ^ 2)
      measure_Ioc_lt_top.ne (hgm.sub hkm).aestronglyMeasurable ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have hti : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have h1 : t⁻¹ / Real.log t ^ 2 ≤ 1 / Real.log 2 ^ 2 :=
      div_le_div₀ (by norm_num) hti (by positivity) (pow_le_pow_left₀ hl2.le hL 2)
    rw [Real.norm_eq_abs]
    refine (hdiff t ht2).trans ?_
    simp only [hm]
    rw [div_eq_mul_one_div 2]
    linarith
  have hgi : IntervalIntegrable g MeasureTheory.volume y x := by
    have h := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hyx).mpr hgk).add hki
    simpa using h
  have hIk : ∫ t in y..x, k t = Real.log (Real.log x) - Real.log (Real.log y) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => Real.log (Real.log t)) (f' := k) (fun t ht => ?_) hki
    have ht2 := hge2 t ht
    have ht0 : t ≠ 0 := by positivity
    exact (Real.hasDerivAt_log ht0).log (hpos t ht2).ne'
  have hIm : ∫ t in y..x, m t = 2 * (1 / Real.log y - 1 / Real.log x) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => -2 * (Real.log t)⁻¹)
      (f' := m) (a := y) (b := x) (fun t ht => ?_) hmi
    · rw [this]; simp only [one_div]; ring
    · have ht2 := hge2 t ht
      exact ((MxAux.hasDerivAt_inv_log ht2).const_mul (-2)).congr_deriv (by simp only [hm]; ring)
  have hmain : ‖∫ t in y..x, (g t - k t)‖ ≤ ∫ t in y..x, m t :=
    intervalIntegral.norm_integral_le_of_norm_le hyx
      (Filter.Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]; exact hdiff t (by linarith [ht.1])) hmi
  rw [intervalIntegral.integral_sub hgi hki, hIk, hIm, Real.norm_eq_abs] at hmain
  exact hmain
