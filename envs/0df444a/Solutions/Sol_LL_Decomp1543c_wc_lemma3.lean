-- Prove2me | solution 1 for LL_Decomp1543c.wc_lemma3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:50:01.638903+00:00
-- url     : https://prove2.me/submissions/bb7e71c5-a5ed-48f3-b6c5-568b523c390c

import Mathlib
import Definitions.Def_LL_Decomp1543c_nint
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_Dioph
import Definitions.Def_LL_Decomp1543c_WCLemma3

open Real Finset ArithmeticFunction LL_Decomp1543c

private lemma minK_nonneg (X θ : ℝ) (hX : 0 ≤ X) : 0 ≤ minK X θ := by
  unfold minK
  split_ifs
  · exact hX
  · apply le_min hX
    have hn : 0 ≤ nint θ := by unfold nint; exact abs_nonneg _
    positivity

private lemma minK_le_left (X θ : ℝ) : minK X θ ≤ X := by
  unfold minK
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

private lemma minK_le_inv (X θ : ℝ) (hpos : 0 < nint θ) :
    minK X θ ≤ 1 / (2 * nint θ) := by
  unfold minK
  rw [if_neg (ne_of_gt hpos)]
  exact min_le_right _ _

private lemma minK_mono_left {X₁ X₂ θ : ℝ} (h : X₁ ≤ X₂) :
    minK X₁ θ ≤ minK X₂ θ := by
  unfold minK
  split_ifs
  · exact h
  · exact min_le_min_right _ h

private lemma abs_sub_div_ge_symmMod (q : ℕ) (hq : 1 ≤ q) (M m : ℤ) :
    ((min (M % (q : ℤ)).toNat (q - (M % (q : ℤ)).toNat) : ℕ) : ℝ) / q ≤
      |(M : ℝ) / q - (m : ℝ)| := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqz : (0 : ℤ) < (q : ℤ) := by omega
  have hr_nonneg : 0 ≤ M % (q : ℤ) := Int.emod_nonneg M (ne_of_gt hqz)
  have hr_lt : M % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos M hqz
  set v : ℕ := (M % (q : ℤ)).toNat
  have hv_cast : (v : ℤ) = M % (q : ℤ) := Int.toNat_of_nonneg hr_nonneg
  have hv_lt : v < q := by omega
  have hdiv_eq : (M : ℝ) / q - (m : ℝ) = ((M - (q : ℤ) * m : ℤ) : ℝ) / q := by
    push_cast; field_simp
  rw [hdiv_eq, abs_div, abs_of_pos hqpos]
  apply div_le_div_of_nonneg_right _ (le_of_lt hqpos)
  have hM : M = (q : ℤ) * (M / (q : ℤ)) + (v : ℤ) := by
    have := Int.mul_ediv_add_emod M (q : ℤ)
    omega
  set t : ℤ := M / (q : ℤ) - m
  have hdiff : M - (q : ℤ) * m = (q : ℤ) * t + (v : ℤ) := by
    dsimp [t]; linarith
  have habs_int : ((min v (q - v) : ℕ) : ℤ) ≤ |M - (q : ℤ) * m| := by
    rw [hdiff]
    by_cases ht : 0 ≤ t
    · have hge : (v : ℤ) ≤ (q : ℤ) * t + (v : ℤ) := by nlinarith
      have hpos : 0 ≤ (q : ℤ) * t + (v : ℤ) := by omega
      rw [abs_of_nonneg hpos]
      have hle : ((min v (q - v) : ℕ) : ℤ) ≤ (v : ℤ) :=
        Nat.cast_le.mpr (Nat.min_le_left v (q - v))
      omega
    · have ht' : t ≤ -1 := by omega
      have hle : (q : ℤ) * t + (v : ℤ) ≤ -((q - v : ℕ) : ℤ) := by
        have hqv : ((q - v : ℕ) : ℤ) = (q : ℤ) - (v : ℤ) := by omega
        nlinarith
      have hneg : (q : ℤ) * t + (v : ℤ) ≤ 0 := by omega
      rw [abs_of_nonpos hneg]
      have hle2 : ((min v (q - v) : ℕ) : ℤ) ≤ ((q - v : ℕ) : ℤ) :=
        Nat.cast_le.mpr (Nat.min_le_right v (q - v))
      omega
  have habs_real : (((min v (q - v) : ℕ) : ℤ) : ℝ) ≤ (|M - (q : ℤ) * m| : ℤ) :=
    Int.cast_le.mpr habs_int
  simpa using habs_real

private lemma nint_ge_of_approx (q : ℕ) (hq : 1 ≤ q) (M : ℤ) (x err : ℝ)
    (herr : |x - (M : ℝ) / q| ≤ err) :
    ((min (M % (q : ℤ)).toNat (q - (M % (q : ℤ)).toNat) : ℕ) : ℝ) / q - err ≤ nint x := by
  unfold nint
  set m : ℤ := round x
  have h1 := abs_sub_div_ge_symmMod q hq M m
  have htri : |(M : ℝ) / q - (m : ℝ)| ≤ |x - (m : ℝ)| + |x - (M : ℝ) / q| := by
    have hsplit : (M : ℝ) / q - (m : ℝ) = (x - (m : ℝ)) - (x - (M : ℝ) / q) := by ring
    rw [hsplit]
    exact abs_sub _ _
  linarith

private lemma odd_harmonic_bound (m : ℕ) (hm : 1 ≤ m) :
    2 * ∑ r ∈ Icc 1 m, (1 : ℝ) / (2 * (r : ℝ) - 1) ≤ 2 + Real.log (2 * (m : ℝ) - 1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp; norm_num
  | succ k hk ih =>
    have hk_pos : (0 : ℝ) < 2 * (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hk1_pos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by linarith
    have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, sum_insert (by simp)]
    have hstep : 2 / (2 * ((k + 1 : ℕ) : ℝ) - 1) ≤
        Real.log (2 * ((k + 1 : ℕ) : ℝ) - 1) - Real.log (2 * (k : ℝ) - 1) := by
      push_cast
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
      rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk1_pos)] at hlog
      have hcalc : (2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1) - 1 = -(2 / (2 * (k : ℝ) + 1)) := by
        field_simp; ring
      rw [hcalc] at hlog
      have hsimp : 2 * ((k : ℝ) + 1) - 1 = 2 * (k : ℝ) + 1 := by ring
      rw [hsimp]
      linarith
    have hmul : 2 * (1 / (2 * ((k + 1 : ℕ) : ℝ) - 1) + ∑ r ∈ Icc 1 k, (1 : ℝ) / (2 * (r : ℝ) - 1)) =
        2 / (2 * ((k + 1 : ℕ) : ℝ) - 1) + 2 * ∑ r ∈ Icc 1 k, (1 : ℝ) / (2 * (r : ℝ) - 1) := by
      ring
    rw [hmul]
    linarith

private lemma exp_one_lt_272 : Real.exp 1 < (2.72 : ℝ) := by
  linarith [Real.exp_one_lt_d9]

private lemma harmonic_ge6_bound (m : ℕ) (hm : 6 ≤ m) :
    ∑ j ∈ Icc 1 m, (1 : ℝ) / (j : ℝ) ≤ Real.log (2 * (m : ℝ)) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have hsum : ∑ j ∈ Icc (1 : ℕ) 6, (1 : ℝ) / (j : ℝ) = 49 / 20 := by
      have : Icc (1 : ℕ) 6 = {1, 2, 3, 4, 5, 6} := by decide
      rw [this]; norm_num
    rw [hsum]
    have hexp : Real.exp (49 / 20 : ℝ) ≤ (12 : ℝ) := by
      have hpow : (Real.exp (49 / 20 : ℝ)) ^ 20 ≤ (12 : ℝ) ^ 20 := by
        rw [← Real.exp_nat_mul]
        have h49 : (20 : ℕ) * (49 / 20 : ℝ) = (49 : ℕ) * (1 : ℝ) := by norm_num
        rw [h49, Real.exp_nat_mul]
        calc (Real.exp 1) ^ 49 ≤ (2.72 : ℝ) ^ 49 := by
              gcongr; exact le_of_lt exp_one_lt_272
          _ ≤ (12 : ℝ) ^ 20 := by norm_num
      exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
    have := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at this
    rw [show (2 : ℝ) * ((6 : ℕ) : ℝ) = 12 by norm_num]
    exact this
  | succ k hk ih =>
    have hsplit : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, sum_insert (by simp)]
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
        Real.log (2 * ((k + 1 : ℕ) : ℝ)) - Real.log (2 * (k : ℝ)) := by
      push_cast
      have hk_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
      have hk1_pos : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk_pos hk1_pos)
      rw [Real.log_div (ne_of_gt hk_pos) (ne_of_gt hk1_pos)] at hlog
      have hcalc : (2 * (k : ℝ)) / (2 * ((k : ℝ) + 1)) - 1 = -(1 / ((k : ℝ) + 1)) := by
        field_simp; ring
      rw [hcalc] at hlog
      linarith
    linarith

private lemma harmonic_half_le_log (q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Icc 1 (q / 2 - 1), (1 : ℝ) / (j : ℝ) ≤ Real.log (q : ℝ) := by
  set m := q / 2 - 1
  by_cases hm0 : m = 0
  · rw [hm0]
    simp only [show Icc (1 : ℕ) 0 = ∅ by decide, sum_empty]
    exact Real.log_nonneg (by exact_mod_cast hq)
  · have hm_pos : 1 ≤ m := by omega
    have hq_ge : 2 * m + 2 ≤ q := by omega
    have hq_ge_r : (2 : ℝ) * (m : ℝ) + 2 ≤ (q : ℝ) := by exact_mod_cast hq_ge
    by_cases hm6 : 6 ≤ m
    · calc ∑ j ∈ Icc 1 m, (1 : ℝ) / (j : ℝ)
          ≤ Real.log (2 * (m : ℝ)) := harmonic_ge6_bound m hm6
        _ ≤ Real.log (q : ℝ) := Real.log_le_log (by positivity) (by linarith)
    · have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
      rcases hm_cases with hm | hm | hm | hm | hm
      · rw [hm] at hq_ge_r ⊢
        have hsum : ∑ j ∈ Icc (1 : ℕ) 1, (1 : ℝ) / (j : ℝ) = 1 := by simp
        rw [hsum]
        have h4 : Real.exp 1 ≤ (4 : ℝ) := by linarith [exp_one_lt_272]
        have := Real.log_le_log (Real.exp_pos _) h4
        rw [Real.log_exp] at this
        exact le_trans this (Real.log_le_log (by norm_num) (by push_cast at hq_ge_r; linarith))
      · rw [hm] at hq_ge_r ⊢
        have hsum : ∑ j ∈ Icc (1 : ℕ) 2, (1 : ℝ) / (j : ℝ) = 3 / 2 := by
          have : Icc (1 : ℕ) 2 = {1, 2} := by decide
          rw [this]; norm_num
        rw [hsum]
        have hexp : Real.exp (3 / 2 : ℝ) ≤ (6 : ℝ) := by
          have hpow : (Real.exp (3 / 2 : ℝ)) ^ 2 ≤ (6 : ℝ) ^ 2 := by
            rw [← Real.exp_nat_mul]
            have : (2 : ℕ) * (3 / 2 : ℝ) = (3 : ℕ) * (1 : ℝ) := by norm_num
            rw [this, Real.exp_nat_mul]
            calc (Real.exp 1) ^ 3 ≤ (2.72 : ℝ) ^ 3 := by gcongr; exact le_of_lt exp_one_lt_272
              _ ≤ (6 : ℝ) ^ 2 := by norm_num
          exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
        have := Real.log_le_log (Real.exp_pos _) hexp
        rw [Real.log_exp] at this
        exact le_trans this (Real.log_le_log (by norm_num) (by push_cast at hq_ge_r; linarith))
      · rw [hm] at hq_ge_r ⊢
        have hsum : ∑ j ∈ Icc (1 : ℕ) 3, (1 : ℝ) / (j : ℝ) = 11 / 6 := by
          have : Icc (1 : ℕ) 3 = {1, 2, 3} := by decide
          rw [this]; norm_num
        rw [hsum]
        have hexp : Real.exp (11 / 6 : ℝ) ≤ (8 : ℝ) := by
          have hpow : (Real.exp (11 / 6 : ℝ)) ^ 6 ≤ (8 : ℝ) ^ 6 := by
            rw [← Real.exp_nat_mul]
            have : (6 : ℕ) * (11 / 6 : ℝ) = (11 : ℕ) * (1 : ℝ) := by norm_num
            rw [this, Real.exp_nat_mul]
            calc (Real.exp 1) ^ 11 ≤ (2.72 : ℝ) ^ 11 := by gcongr; exact le_of_lt exp_one_lt_272
              _ ≤ (8 : ℝ) ^ 6 := by norm_num
          exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
        have := Real.log_le_log (Real.exp_pos _) hexp
        rw [Real.log_exp] at this
        exact le_trans this (Real.log_le_log (by norm_num) (by push_cast at hq_ge_r; linarith))
      · rw [hm] at hq_ge_r ⊢
        have hsum : ∑ j ∈ Icc (1 : ℕ) 4, (1 : ℝ) / (j : ℝ) = 25 / 12 := by
          have : Icc (1 : ℕ) 4 = {1, 2, 3, 4} := by decide
          rw [this]; norm_num
        rw [hsum]
        have hexp : Real.exp (25 / 12 : ℝ) ≤ (10 : ℝ) := by
          have hpow : (Real.exp (25 / 12 : ℝ)) ^ 12 ≤ (10 : ℝ) ^ 12 := by
            rw [← Real.exp_nat_mul]
            have : (12 : ℕ) * (25 / 12 : ℝ) = (25 : ℕ) * (1 : ℝ) := by norm_num
            rw [this, Real.exp_nat_mul]
            calc (Real.exp 1) ^ 25 ≤ (2.72 : ℝ) ^ 25 := by gcongr; exact le_of_lt exp_one_lt_272
              _ ≤ (10 : ℝ) ^ 12 := by norm_num
          exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
        have := Real.log_le_log (Real.exp_pos _) hexp
        rw [Real.log_exp] at this
        exact le_trans this (Real.log_le_log (by norm_num) (by push_cast at hq_ge_r; linarith))
      · rw [hm] at hq_ge_r ⊢
        have h56 : ∑ j ∈ Icc (1 : ℕ) 5, (1 : ℝ) / (j : ℝ) ≤ ∑ j ∈ Icc (1 : ℕ) 6, (1 : ℝ) / (j : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx; simp only [mem_Icc] at hx ⊢; omega
          · intros; positivity
        calc ∑ j ∈ Icc (1 : ℕ) 5, (1 : ℝ) / (j : ℝ)
            ≤ ∑ j ∈ Icc (1 : ℕ) 6, (1 : ℝ) / (j : ℝ) := h56
          _ ≤ Real.log (2 * ((6 : ℕ) : ℝ)) := harmonic_ge6_bound 6 le_rfl
          _ ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) (by push_cast at hq_ge_r ⊢; linarith)

private lemma block_minK_bound (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q)
    (X : ℝ) (hX : 0 < X) (n₀ : ℤ) (S : Finset ℤ)
    (hS : ∀ n ∈ S, n₀ ≤ n ∧ n < n₀ + (q : ℤ)) :
    ∑ n ∈ S, minK X (α * (n : ℝ)) ≤ 3 * X + (q : ℝ) * Real.log (q : ℝ) := by
  rcases hD with ⟨hq1, hgcd, happrox⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqz : (0 : ℤ) < (q : ℤ) := by omega
  set hqhalf : ℕ := (q - 1) / 2
  set m₀ : ℤ := n₀ + (hqhalf : ℤ)
  set b : ℤ := round ((q : ℝ) * (α * (m₀ : ℝ)))
  let M : ℤ → ℤ := fun n => b + a * (n - m₀)
  let rval : ℤ → ℕ := fun n => (M n % (q : ℤ)).toNat
  have hrval_mem : ∀ n, rval n ∈ Finset.range q := by
    intro n
    rw [Finset.mem_range]
    have hlt := Int.emod_lt_of_pos (M n) hqz
    have hnn := Int.emod_nonneg (M n) (ne_of_gt hqz)
    have hcast : ((rval n : ℕ) : ℤ) = M n % (q : ℤ) := Int.toNat_of_nonneg hnn
    omega
  have hrval_inj : Set.InjOn rval S := by
    intro n₁ hn₁ n₂ hn₂ heq
    have hnn₁ := Int.emod_nonneg (M n₁) (ne_of_gt hqz)
    have hnn₂ := Int.emod_nonneg (M n₂) (ne_of_gt hqz)
    have hmod : M n₁ % (q : ℤ) = M n₂ % (q : ℤ) := by
      have : ((rval n₁ : ℕ) : ℤ) = ((rval n₂ : ℕ) : ℤ) := by exact_mod_cast heq
      dsimp [rval] at this
      rwa [Int.toNat_of_nonneg hnn₁, Int.toNat_of_nonneg hnn₂] at this
    have hdvd : (q : ℤ) ∣ (M n₁ - M n₂) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, hmod, sub_self, Int.zero_emod]
    have hdiff : M n₁ - M n₂ = a * (n₁ - n₂) := by dsimp [M]; ring
    rw [hdiff] at hdvd
    have hcop : IsCoprime (q : ℤ) a := by
      have : IsCoprime a (q : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.natAbs_natCast] using hgcd
      exact this.symm
    have hdvd' : (q : ℤ) ∣ (n₁ - n₂) := hcop.dvd_of_dvd_mul_left hdvd
    have h1 := hS n₁ hn₁
    have h2 := hS n₂ hn₂
    rcases hdvd' with ⟨k, hk⟩
    have hk0 : k = 0 := by nlinarith
    rw [hk0, mul_zero] at hk
    omega
  let g : ℕ → ℝ := fun v =>
    if min v (q - v) ≤ 1 then X else (q : ℝ) / (2 * (((min v (q - v) : ℕ) : ℝ) - 1))
  have hg_nonneg : ∀ v, 0 ≤ g v := by
    intro v
    dsimp [g]
    split_ifs with h
    · exact le_of_lt hX
    · have h2 : (2 : ℝ) ≤ ((min v (q - v) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (show 2 ≤ min v (q - v) by omega)
      apply div_nonneg (le_of_lt hqpos) (by linarith)
  have hterm : ∀ n ∈ S, minK X (α * (n : ℝ)) ≤ g (rval n) := by
    intro n hn
    dsimp [g]
    split_ifs with hle
    · exact minK_le_left _ _
    · have hge2 : 2 ≤ min (rval n) (q - rval n) := by omega
      have hge2r : (2 : ℝ) ≤ ((min (rval n) (q - rval n) : ℕ) : ℝ) := Nat.cast_le.mpr hge2
      have hnm_bound : |(n : ℝ) - (m₀ : ℝ)| ≤ (q : ℝ) / 2 := by
        have h1 := hS n hn
        have h1' : (n₀ : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (n₀ : ℝ) + (q : ℝ) - 1 := by
          constructor
          · exact_mod_cast h1.1
          · have : n ≤ n₀ + (q : ℤ) - 1 := by omega
            have : (n : ℝ) ≤ ((n₀ + (q : ℤ) - 1 : ℤ) : ℝ) := Int.cast_le.mpr this
            push_cast at this; linarith
        have hhalf : ((((q - 1) / 2 : ℕ) : ℝ)) ≤ ((q : ℝ) - 1) / 2 ∧
            ((q : ℝ) - 2) / 2 ≤ ((((q - 1) / 2 : ℕ) : ℝ)) := by
          have hq1' : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
            rw [Nat.cast_sub hq1]; simp
          constructor
          · have : 2 * ((q - 1) / 2) ≤ q - 1 := Nat.mul_div_le (q - 1) 2
            have : (2 : ℝ) * (((q - 1) / 2 : ℕ) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast this
            linarith
          · have : q - 1 ≤ 2 * ((q - 1) / 2) + 1 := by omega
            have : ((q - 1 : ℕ) : ℝ) ≤ (2 : ℝ) * (((q - 1) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
            linarith
        have hm0r : (m₀ : ℝ) = (n₀ : ℝ) + (hqhalf : ℝ) := by
          dsimp [m₀]; rw [Int.cast_add, Int.cast_natCast]
        rw [abs_le]
        constructor <;> linarith
      have herr : |α * (n : ℝ) - (M n : ℝ) / q| ≤ 1 / (q : ℝ) := by
        have hsplit : α * (n : ℝ) - (M n : ℝ) / q =
            ((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ) +
              (α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ)) := by
          dsimp [M]; push_cast; field_simp; ring
        rw [hsplit]
        have h1 : |((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
          rw [abs_div, abs_of_pos hqpos]
          have hround : |(q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)| ≤ 1 / 2 := abs_sub_round _
          calc |(q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)| / (q : ℝ)
              ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right hround (le_of_lt hqpos)
            _ = 1 / (2 * (q : ℝ)) := by ring
        have h2 : |(α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ))| ≤ 1 / (2 * (q : ℝ)) := by
          rw [abs_mul]
          calc |α - (a : ℝ) / (q : ℝ)| * |(n : ℝ) - (m₀ : ℝ)|
              ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) :=
                mul_le_mul happrox hnm_bound (abs_nonneg _) (by positivity)
            _ = 1 / (2 * (q : ℝ)) := by field_simp
        calc |((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ) +
                (α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ))|
            ≤ |((q : ℝ) * (α * (m₀ : ℝ)) - (b : ℝ)) / (q : ℝ)| +
                |(α - (a : ℝ) / (q : ℝ)) * ((n : ℝ) - (m₀ : ℝ))| := abs_add_le _ _
          _ ≤ 1 / (2 * (q : ℝ)) + 1 / (2 * (q : ℝ)) := add_le_add h1 h2
          _ = 1 / (q : ℝ) := by ring
      have hnint := nint_ge_of_approx q hq1 (M n) (α * (n : ℝ)) (1 / (q : ℝ)) herr
      have hpos : 0 < (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ) := by
        apply div_pos (by linarith) hqpos
      have hnint' : (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ) ≤ nint (α * (n : ℝ)) := by
        have : ((min (rval n) (q - rval n) : ℕ) : ℝ) / (q : ℝ) - 1 / (q : ℝ) =
            (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ) := by ring
        rw [← this]; exact hnint
      have hnint_pos : 0 < nint (α * (n : ℝ)) := lt_of_lt_of_le hpos hnint'
      calc minK X (α * (n : ℝ))
          ≤ 1 / (2 * nint (α * (n : ℝ))) := minK_le_inv _ _ hnint_pos
        _ ≤ 1 / (2 * ((((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (q : ℝ))) := by
            apply one_div_le_one_div_of_le (by positivity) (by linarith)
        _ = (q : ℝ) / (2 * (((min (rval n) (q - rval n) : ℕ) : ℝ) - 1)) := by field_simp
  have hsum_img : ∑ n ∈ S, minK X (α * (n : ℝ)) ≤ ∑ v ∈ Finset.range q, g v := by
    calc ∑ n ∈ S, minK X (α * (n : ℝ))
        ≤ ∑ n ∈ S, g (rval n) := Finset.sum_le_sum hterm
      _ = ∑ v ∈ S.image rval, g v := (Finset.sum_image (fun x hx y hy h => hrval_inj hx hy h)).symm
      _ ≤ ∑ v ∈ Finset.range q, g v := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => hg_nonneg v)
          intro v hv
          rcases Finset.mem_image.mp hv with ⟨n, _, rfl⟩
          exact hrval_mem n
  set A := (Finset.range q).filter (fun v => min v (q - v) ≤ 1)
  set B := (Finset.range q).filter (fun v => ¬ min v (q - v) ≤ 1)
  have hsplit : ∑ v ∈ Finset.range q, g v = ∑ v ∈ A, g v + ∑ v ∈ B, g v :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun v => min v (q - v) ≤ 1) g).symm
  have hA_bound : ∑ v ∈ A, g v ≤ 3 * X := by
    have hA_sub : A ⊆ ({0, 1, q - 1} : Finset ℕ) := by
      intro v hv
      simp only [A, mem_filter, mem_range, mem_insert, mem_singleton] at hv ⊢
      omega
    have hcard : A.card ≤ 3 := by
      calc A.card ≤ ({0, 1, q - 1} : Finset ℕ).card := Finset.card_le_card hA_sub
        _ ≤ 3 := by
          calc ({0, 1, q - 1} : Finset ℕ).card
              ≤ ({1, q - 1} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
            _ ≤ ({q - 1} : Finset ℕ).card + 1 + 1 := by
                have := Finset.card_insert_le (1 : ℕ) ({q - 1} : Finset ℕ); omega
            _ = 3 := by simp
    have hA_eq : ∑ v ∈ A, g v = (A.card : ℝ) * X := by
      calc ∑ v ∈ A, g v = ∑ _v ∈ A, X := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp only [A, mem_filter] at hv
            dsimp [g]; rw [if_pos hv.2]
        _ = (A.card : ℝ) * X := by simp
    rw [hA_eq]
    have : (A.card : ℝ) ≤ 3 := by exact_mod_cast hcard
    nlinarith
  have hB_bound : ∑ v ∈ B, g v ≤ (q : ℝ) * Real.log (q : ℝ) := by
    set B₁ := B.filter (fun v => v ≤ q / 2)
    set B₂ := B.filter (fun v => ¬ v ≤ q / 2)
    have hB_split : ∑ v ∈ B, g v = ∑ v ∈ B₁, g v + ∑ v ∈ B₂, g v :=
      (Finset.sum_filter_add_sum_filter_not B (fun v => v ≤ q / 2) g).symm
    have hB₁_le : ∑ v ∈ B₁, g v ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
      calc ∑ v ∈ B₁, g v
          = ∑ r ∈ B₁, (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp only [B₁, B, mem_filter, mem_range] at hv
            have hmin : min v (q - v) = v := Nat.min_eq_left (by omega)
            dsimp [g]; rw [if_neg hv.1.2, hmin]
        _ ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro v hv
              simp only [B₁, B, mem_filter, mem_range, mem_Icc] at hv ⊢
              omega
            · intro r hr _
              simp only [mem_Icc] at hr
              have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
              apply div_nonneg (le_of_lt hqpos) (by linarith)
    have hB₂_le : ∑ v ∈ B₂, g v ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
      have hinj : Set.InjOn (fun v => q - v) B₂ := by
        intro v₁ hv₁ v₂ hv₂ heq
        simp only [Finset.mem_coe, B₂, B, mem_filter, mem_range] at hv₁ hv₂
        dsimp at heq
        omega
      calc ∑ v ∈ B₂, g v
          = ∑ v ∈ B₂, (q : ℝ) / (2 * (((q - v : ℕ) : ℝ) - 1)) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp only [B₂, B, mem_filter, mem_range] at hv
            have hmin : min v (q - v) = q - v := Nat.min_eq_right (by omega)
            dsimp [g]; rw [if_neg hv.1.2, hmin]
        _ = ∑ r ∈ B₂.image (fun v => q - v), (q : ℝ) / (2 * ((r : ℝ) - 1)) :=
            (Finset.sum_image (f := fun r : ℕ => (q : ℝ) / (2 * ((r : ℝ) - 1)))
              (fun x hx y hy h => hinj hx hy h)).symm
        _ ≤ ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro r hr
              rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
              simp only [B₂, B, mem_filter, mem_range, mem_Icc] at hv ⊢
              omega
            · intro r hr _
              simp only [mem_Icc] at hr
              have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
              apply div_nonneg (le_of_lt hqpos) (by linarith)
    have hshift : 2 * ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) =
        (q : ℝ) * ∑ j ∈ Icc 1 (q / 2 - 1), (1 : ℝ) / (j : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_bij (fun r _ => r - 1) ?_ ?_ ?_ ?_
      · intro r hr; simp only [mem_Icc] at hr ⊢; omega
      · intro r₁ hr₁ r₂ hr₂ h; simp only [mem_Icc] at hr₁ hr₂; omega
      · intro j hj; refine ⟨j + 1, ?_, by omega⟩
        simp only [mem_Icc] at hj ⊢; omega
      · intro r hr
        simp only [mem_Icc] at hr
        have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hr1]; field_simp
    have hharm := harmonic_half_le_log q hq1
    calc ∑ v ∈ B, g v
        = ∑ v ∈ B₁, g v + ∑ v ∈ B₂, g v := hB_split
      _ ≤ 2 * ∑ r ∈ Icc 2 (q / 2), (q : ℝ) / (2 * ((r : ℝ) - 1)) := by linarith
      _ = (q : ℝ) * ∑ j ∈ Icc 1 (q / 2 - 1), (1 : ℝ) / (j : ℝ) := hshift
      _ ≤ (q : ℝ) * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_left hharm (le_of_lt hqpos)
  linarith

private lemma first_half_bound (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (hq15 : 15 ≤ q)
    (Y : ℝ) (_hY : 0 < Y) (M : ℕ) (hM : M ≤ q / 2) :
    ∑ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤ 2 * (q : ℝ) + (q : ℝ) * Real.log (q : ℝ) := by
  rcases hD with ⟨hq1, hgcd, happrox⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqz : (0 : ℤ) < (q : ℤ) := by omega
  let rval : ℕ → ℕ := fun n => ((a * (n : ℤ)) % (q : ℤ)).toNat
  have hrval_mem : ∀ n ∈ Icc 1 M, rval n ∈ Icc 1 (q - 1) := by
    intro n hn
    simp only [mem_Icc] at hn ⊢
    have hnn := Int.emod_nonneg (a * (n : ℤ)) (ne_of_gt hqz)
    have hlt := Int.emod_lt_of_pos (a * (n : ℤ)) hqz
    have hcast : ((rval n : ℕ) : ℤ) = (a * (n : ℤ)) % (q : ℤ) := Int.toNat_of_nonneg hnn
    have hne0 : (a * (n : ℤ)) % (q : ℤ) ≠ 0 := by
      intro hz
      have hdvd : (q : ℤ) ∣ a * (n : ℤ) := Int.dvd_of_emod_eq_zero hz
      have hcop : IsCoprime (q : ℤ) a := by
        have : IsCoprime a (q : ℤ) := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          simpa [Int.natAbs_natCast] using hgcd
        exact this.symm
      have hdvdn : (q : ℤ) ∣ (n : ℤ) := hcop.dvd_of_dvd_mul_left hdvd
      rcases hdvdn with ⟨k, hk⟩
      have h1 : (1 : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < (q : ℤ) := by omega
      by_cases hk0 : k ≤ 0 <;> nlinarith
    omega
  have hrval_inj : Set.InjOn rval (Icc 1 M) := by
    intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_coe, mem_Icc] at hn₁ hn₂
    have hnn₁ := Int.emod_nonneg (a * (n₁ : ℤ)) (ne_of_gt hqz)
    have hnn₂ := Int.emod_nonneg (a * (n₂ : ℤ)) (ne_of_gt hqz)
    have hmod : (a * (n₁ : ℤ)) % (q : ℤ) = (a * (n₂ : ℤ)) % (q : ℤ) := by
      have : ((rval n₁ : ℕ) : ℤ) = ((rval n₂ : ℕ) : ℤ) := by exact_mod_cast heq
      dsimp [rval] at this
      rwa [Int.toNat_of_nonneg hnn₁, Int.toNat_of_nonneg hnn₂] at this
    have hdvd : (q : ℤ) ∣ a * ((n₁ : ℤ) - (n₂ : ℤ)) := by
      have hsub : a * ((n₁ : ℤ) - (n₂ : ℤ)) = a * (n₁ : ℤ) - a * (n₂ : ℤ) := by ring
      rw [hsub, Int.dvd_iff_emod_eq_zero, Int.sub_emod, hmod, sub_self, Int.zero_emod]
    have hcop : IsCoprime (q : ℤ) a := by
      have : IsCoprime a (q : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.natAbs_natCast] using hgcd
      exact this.symm
    have hdvd' : (q : ℤ) ∣ ((n₁ : ℤ) - (n₂ : ℤ)) := hcop.dvd_of_dvd_mul_left hdvd
    rcases hdvd' with ⟨k, hk⟩
    have hlt1 : (n₁ : ℤ) < (q : ℤ) := by omega
    have hlt2 : (n₂ : ℤ) < (q : ℤ) := by omega
    have hk0 : k = 0 := by nlinarith
    rw [hk0, mul_zero] at hk
    omega
  let g : ℕ → ℝ := fun v => (q : ℝ) / (2 * ((min v (q - v) : ℕ) : ℝ) - 1)
  have hterm : ∀ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤ g (rval n) := by
    intro n hn
    have hrm := hrval_mem n hn
    simp only [mem_Icc] at hn hrm
    have hmin1 : 1 ≤ min (rval n) (q - rval n) := by omega
    have hmin1r : (1 : ℝ) ≤ ((min (rval n) (q - rval n) : ℕ) : ℝ) := by
      simpa using (Nat.cast_le (α := ℝ).mpr hmin1)
    have hn_le : (n : ℝ) ≤ (q : ℝ) / 2 := by
      have : 2 * n ≤ q := by omega
      have : (2 : ℝ) * (n : ℝ) ≤ (q : ℝ) := by exact_mod_cast this
      linarith
    have herr : |α * (n : ℝ) - ((a * (n : ℤ) : ℤ) : ℝ) / (q : ℝ)| ≤ 1 / (2 * (q : ℝ)) := by
      have hsplit : α * (n : ℝ) - ((a * (n : ℤ) : ℤ) : ℝ) / (q : ℝ) =
          (α - (a : ℝ) / (q : ℝ)) * (n : ℝ) := by push_cast; ring
      rw [hsplit, abs_mul, abs_of_nonneg (a := (n : ℝ)) (Nat.cast_nonneg n)]
      calc |α - (a : ℝ) / (q : ℝ)| * (n : ℝ)
          ≤ (1 / (q : ℝ) ^ 2) * ((q : ℝ) / 2) :=
            mul_le_mul happrox hn_le (Nat.cast_nonneg n) (by positivity)
        _ = 1 / (2 * (q : ℝ)) := by field_simp
    have hnint := nint_ge_of_approx q hq1 (a * (n : ℤ)) (α * (n : ℝ)) (1 / (2 * (q : ℝ))) herr
    have hrew : ((min (rval n) (q - rval n) : ℕ) : ℝ) / (q : ℝ) - 1 / (2 * (q : ℝ)) =
        (2 * ((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (2 * (q : ℝ)) := by
      field_simp
    have hpos : 0 < (2 * ((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (2 * (q : ℝ)) := by
      apply div_pos (by linarith) (by positivity)
    have hnint' : (2 * ((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (2 * (q : ℝ)) ≤
        nint (α * (n : ℝ)) := by
      rw [← hrew]; exact hnint
    have hnint_pos : 0 < nint (α * (n : ℝ)) := lt_of_lt_of_le hpos hnint'
    calc minK (Y / (n : ℝ)) (α * (n : ℝ))
        ≤ 1 / (2 * nint (α * (n : ℝ))) := minK_le_inv _ _ hnint_pos
      _ ≤ 1 / (2 * ((2 * ((min (rval n) (q - rval n) : ℕ) : ℝ) - 1) / (2 * (q : ℝ)))) := by
          apply one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = g (rval n) := by dsimp [g]; field_simp
  have hsum_img : ∑ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
      ∑ v ∈ Icc 1 (q - 1), g v := by
    calc ∑ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ))
        ≤ ∑ n ∈ Icc 1 M, g (rval n) := Finset.sum_le_sum hterm
      _ = ∑ v ∈ (Icc 1 M).image rval, g v :=
          (Finset.sum_image (fun x hx y hy h => hrval_inj hx hy h)).symm
      _ ≤ ∑ v ∈ Icc 1 (q - 1), g v := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro v hv
            rcases Finset.mem_image.mp hv with ⟨n, hn, rfl⟩
            exact hrval_mem n hn
          · intro v hv _
            simp only [mem_Icc] at hv
            have : (1 : ℝ) ≤ ((min v (q - v) : ℕ) : ℝ) := by
              simpa using (Nat.cast_le (α := ℝ).mpr (show 1 ≤ min v (q - v) by omega))
            dsimp [g]; apply div_nonneg (le_of_lt hqpos) (by linarith)
  set C₁ := (Icc 1 (q - 1)).filter (fun v => v ≤ q / 2)
  set C₂ := (Icc 1 (q - 1)).filter (fun v => ¬ v ≤ q / 2)
  have hC_split : ∑ v ∈ Icc 1 (q - 1), g v = ∑ v ∈ C₁, g v + ∑ v ∈ C₂, g v :=
    (Finset.sum_filter_add_sum_filter_not (Icc 1 (q - 1)) (fun v => v ≤ q / 2) g).symm
  have hC₁_le : ∑ v ∈ C₁, g v ≤ ∑ r ∈ Icc 1 (q / 2), (q : ℝ) / (2 * (r : ℝ) - 1) := by
    calc ∑ v ∈ C₁, g v
        = ∑ r ∈ C₁, (q : ℝ) / (2 * (r : ℝ) - 1) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          simp only [C₁, mem_filter, mem_Icc] at hv
          have hmin : min v (q - v) = v := Nat.min_eq_left (by omega)
          dsimp [g]; rw [hmin]
      _ ≤ ∑ r ∈ Icc 1 (q / 2), (q : ℝ) / (2 * (r : ℝ) - 1) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro v hv; simp only [C₁, mem_filter, mem_Icc] at hv ⊢; omega
          · intro r hr _; simp only [mem_Icc] at hr
            have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
            apply div_nonneg (le_of_lt hqpos) (by linarith)
  have hC₂_le : ∑ v ∈ C₂, g v ≤ ∑ r ∈ Icc 1 (q / 2), (q : ℝ) / (2 * (r : ℝ) - 1) := by
    have hinj : Set.InjOn (fun v => q - v) C₂ := by
      intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, C₂, mem_filter, mem_Icc] at hv₁ hv₂
      dsimp at heq
      omega
    calc ∑ v ∈ C₂, g v
        = ∑ v ∈ C₂, (q : ℝ) / (2 * ((q - v : ℕ) : ℝ) - 1) := by
          refine Finset.sum_congr rfl fun v hv => ?_
          simp only [C₂, mem_filter, mem_Icc] at hv
          have hmin : min v (q - v) = q - v := Nat.min_eq_right (by omega)
          dsimp [g]; rw [hmin]
      _ = ∑ r ∈ C₂.image (fun v => q - v), (q : ℝ) / (2 * (r : ℝ) - 1) :=
          (Finset.sum_image (f := fun r : ℕ => (q : ℝ) / (2 * (r : ℝ) - 1))
            (fun x hx y hy h => hinj hx hy h)).symm
      _ ≤ ∑ r ∈ Icc 1 (q / 2), (q : ℝ) / (2 * (r : ℝ) - 1) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro r hr
            rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
            simp only [C₂, mem_filter, mem_Icc] at hv ⊢; omega
          · intro r hr _; simp only [mem_Icc] at hr
            have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
            apply div_nonneg (le_of_lt hqpos) (by linarith)
  have hodd := odd_harmonic_bound (q / 2) (by omega)
  have hlog_le : Real.log (2 * ((q / 2 : ℕ) : ℝ) - 1) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · have : (7 : ℝ) ≤ ((q / 2 : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ q / 2 by omega)
      linarith
    · have : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
      have : (2 : ℝ) * ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast this
      linarith
  have hfactor : 2 * ∑ r ∈ Icc 1 (q / 2), (q : ℝ) / (2 * (r : ℝ) - 1) =
      (q : ℝ) * (2 * ∑ r ∈ Icc 1 (q / 2), (1 : ℝ) / (2 * (r : ℝ) - 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => by ring
  calc ∑ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ))
      ≤ ∑ v ∈ Icc 1 (q - 1), g v := hsum_img
    _ = ∑ v ∈ C₁, g v + ∑ v ∈ C₂, g v := hC_split
    _ ≤ 2 * ∑ r ∈ Icc 1 (q / 2), (q : ℝ) / (2 * (r : ℝ) - 1) := by linarith
    _ = (q : ℝ) * (2 * ∑ r ∈ Icc 1 (q / 2), (1 : ℝ) / (2 * (r : ℝ) - 1)) := hfactor
    _ ≤ (q : ℝ) * (2 + Real.log (q : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hqpos)
    _ = 2 * (q : ℝ) + (q : ℝ) * Real.log (q : ℝ) := by ring

theorem solution : WCLemma3 := by
  intro α a q hD hq15 X Y hX hY
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq1)
  have hlogX_nn : 0 ≤ Real.log X := Real.log_nonneg hX
  set M := ⌊X⌋₊
  set m₀ := q / 2
  by_cases hM : M ≤ m₀
  · have h1 := first_half_bound α a q hD hq15 Y hY M hM
    have hX_term : 0 ≤ X * Real.log (q : ℝ) := by positivity
    have hY_term : 0 ≤ 5 * Y / (q : ℝ) * Real.log X := by positivity
    nlinarith
  · push Not at hM
    have hsplit : ∑ n ∈ Icc 1 M, minK (Y / (n : ℝ)) (α * (n : ℝ)) =
        ∑ n ∈ Icc 1 m₀, minK (Y / (n : ℝ)) (α * (n : ℝ)) +
          ∑ n ∈ Icc (m₀ + 1) M, minK (Y / (n : ℝ)) (α * (n : ℝ)) := by
      have hdisj : Disjoint (Icc 1 m₀) (Icc (m₀ + 1) M) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [mem_Icc] at hx1 hx2; omega
      have hunion : Icc 1 m₀ ∪ Icc (m₀ + 1) M = Icc 1 M := by
        ext x; simp only [mem_union, mem_Icc]; omega
      rw [← Finset.sum_union hdisj, hunion]
    have hfirst := first_half_bound α a q hD hq15 Y hY m₀ le_rfl
    set K : ℕ := (M - m₀ - 1) / q
    let B : ℕ → Finset ℕ := fun k => Icc (m₀ + 1 + k * q) (min M (m₀ + (k + 1) * q))
    have htail_eq : ∑ n ∈ Icc (m₀ + 1) M, minK (Y / (n : ℝ)) (α * (n : ℝ)) =
        ∑ k ∈ range (K + 1), ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) := by
      have hdisj : Set.PairwiseDisjoint (↑(range (K + 1)) : Set ℕ) B := by
        intro k₁ _ k₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro n hn₁ hn₂
        simp only [B, mem_Icc] at hn₁ hn₂
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : (k₁ + 1) * q ≤ k₂ * q := Nat.mul_le_mul_right q (by omega)
          omega
        · have : (k₂ + 1) * q ≤ k₁ * q := Nat.mul_le_mul_right q (by omega)
          omega
      have hbi : (range (K + 1)).biUnion B = Icc (m₀ + 1) M := by
        ext n
        simp only [mem_biUnion, mem_range, B, mem_Icc]
        constructor
        · rintro ⟨k, _, h1, h2⟩; omega
        · intro ⟨h1, h2⟩
          refine ⟨(n - m₀ - 1) / q, ?_, ?_, ?_⟩
          · have : (n - m₀ - 1) / q ≤ (M - m₀ - 1) / q := Nat.div_le_div_right (by omega)
            omega
          · have : (n - m₀ - 1) / q * q ≤ n - m₀ - 1 := Nat.div_mul_le_self _ _
            omega
          · have : n - m₀ - 1 < ((n - m₀ - 1) / q + 1) * q := by
              have := Nat.lt_div_mul_add (a := n - m₀ - 1) (b := q) (by omega)
              linarith
            omega
      rw [← hbi, Finset.sum_biUnion hdisj]
    have hblock : ∀ k ∈ range (K + 1),
        ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
          3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) + (q : ℝ) * Real.log (q : ℝ) := by
      intro k _
      set Xk : ℝ := Y / (((k : ℝ) + 1 / 2) * (q : ℝ))
      have hXk_pos : 0 < Xk := by dsimp [Xk]; positivity
      have hmono : ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
          ∑ n ∈ B k, minK Xk (α * (n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        simp only [B, mem_Icc] at hn
        apply minK_mono_left
        apply div_le_div_of_nonneg_left (le_of_lt hY) (by positivity)
        have hm0_ge : (q : ℝ) / 2 < (m₀ : ℝ) + 1 := by
          have : q < 2 * (m₀ + 1) := by omega
          have : (q : ℝ) < 2 * ((m₀ : ℝ) + 1) := by exact_mod_cast this
          linarith
        have hn_ge : ((m₀ + 1 + k * q : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
        push_cast at hn_ge
        linarith
      set S : Finset ℤ := (B k).image (fun n : ℕ => (n : ℤ))
      have hsum_Z : ∑ n ∈ B k, minK Xk (α * (n : ℝ)) =
          ∑ z ∈ S, minK Xk (α * (z : ℝ)) := by
        symm
        dsimp [S]
        rw [Finset.sum_image (f := fun z : ℤ => minK Xk (α * (z : ℝ)))
          (g := fun n : ℕ => (n : ℤ)) (fun x _ y _ h => Int.ofNat.inj h)]
        refine Finset.sum_congr rfl fun n _ => by push_cast; rfl
      have hS_range : ∀ z ∈ S,
          ((m₀ + 1 + k * q : ℕ) : ℤ) ≤ z ∧ z < ((m₀ + 1 + k * q : ℕ) : ℤ) + (q : ℤ) := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
        simp only [B, mem_Icc] at hn
        have hmul : (k + 1) * q = k * q + q := by ring
        have hle2 : n ≤ m₀ + k * q + q := by
          have := le_trans hn.2 (Nat.min_le_right _ _)
          omega
        constructor <;> omega
      have hblk := block_minK_bound α a q hD Xk hXk_pos ((m₀ + 1 + k * q : ℕ) : ℤ) S hS_range
      linarith
    have htail_le : ∑ k ∈ range (K + 1), ∑ n ∈ B k, minK (Y / (n : ℝ)) (α * (n : ℝ)) ≤
        ∑ k ∈ range (K + 1), (3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) + (q : ℝ) * Real.log (q : ℝ)) :=
      Finset.sum_le_sum hblock
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htail_le
    have hKnat : K * q + m₀ + 1 ≤ M := by
      have hKmul : K * q ≤ M - m₀ - 1 := Nat.div_mul_le_self _ _
      omega
    have hKreal : (K : ℝ) * (q : ℝ) + (m₀ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hKnat
    have hMX : (M : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hKq : ((K + 1 : ℕ) : ℝ) * (q : ℝ) ≤ X + 0.5 * (q : ℝ) := by
      have hm0_ge : (q : ℝ) - 1 ≤ 2 * (m₀ : ℝ) := by
        have : q - 1 ≤ 2 * m₀ := by omega
        have hq1' : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1]; simp
        rw [← hq1']; exact_mod_cast this
      push_cast; linarith
    have hlogq_sum : ((K + 1 : ℕ) : ℝ) * ((q : ℝ) * Real.log (q : ℝ)) ≤
        X * Real.log (q : ℝ) + 0.5 * (q : ℝ) * Real.log (q : ℝ) := by
      calc ((K + 1 : ℕ) : ℝ) * ((q : ℝ) * Real.log (q : ℝ))
          = (((K + 1 : ℕ) : ℝ) * (q : ℝ)) * Real.log (q : ℝ) := by ring
        _ ≤ (X + 0.5 * (q : ℝ)) * Real.log (q : ℝ) :=
            mul_le_mul_of_nonneg_right hKq hlogq_nn
        _ = X * Real.log (q : ℝ) + 0.5 * (q : ℝ) * Real.log (q : ℝ) := by ring
    have hY_eq : ∑ k ∈ range (K + 1), 3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) =
        (Y / (q : ℝ)) * (3 * (2 * ∑ r ∈ Icc 1 (K + 1), (1 : ℝ) / (2 * (r : ℝ) - 1))) := by
      have hshift : ∑ k ∈ range (K + 1), 3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) =
          ∑ r ∈ Icc 1 (K + 1), (Y / (q : ℝ)) * (6 / (2 * (r : ℝ) - 1)) := by
        refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [mem_range, mem_Icc] at hk ⊢; omega
        · intro k₁ _ k₂ _ h; omega
        · intro r hr
          simp only [mem_Icc] at hr
          refine ⟨r - 1, ?_, by omega⟩
          simp only [mem_range]; omega
        · intro k _
          push_cast
          have hne : (2 * ((k : ℝ) + 1) - 1) ≠ 0 := by linarith
          have hne' : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
          field_simp; ring
      rw [hshift, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hoddK := odd_harmonic_bound (K + 1) (Nat.succ_pos K)
    have hX_lb : (2 * ((K + 1 : ℕ) : ℝ) - 1) * 7.5 ≤ X := by
      have hm0_ge : (q : ℝ) / 2 < (m₀ : ℝ) + 1 := by
        have : q < 2 * (m₀ + 1) := by omega
        have : (q : ℝ) < 2 * ((m₀ : ℝ) + 1) := by exact_mod_cast this
        linarith
      have hq15r : (15 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq15
      push_cast
      nlinarith
    have hlog75 : (2 : ℝ) ≤ Real.log 7.5 := by
      have hexp2 : Real.exp 2 ≤ (7.5 : ℝ) := by
        have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [h2]
        calc (Real.exp 1) ^ 2 ≤ (2.72 : ℝ) ^ 2 := by gcongr; exact le_of_lt exp_one_lt_272
          _ ≤ (7.5 : ℝ) := by norm_num
      have := Real.log_le_log (Real.exp_pos _) hexp2
      rwa [Real.log_exp] at this
    have h2K_pos : (0 : ℝ) < 2 * ((K + 1 : ℕ) : ℝ) - 1 := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
    have hlogX_lb : Real.log (2 * ((K + 1 : ℕ) : ℝ) - 1) + 2 ≤ Real.log X := by
      have h1 := Real.log_le_log (by positivity) hX_lb
      rw [Real.log_mul (ne_of_gt h2K_pos) (by norm_num)] at h1
      linarith
    have hlog2K_nn : 0 ≤ Real.log (2 * ((K + 1 : ℕ) : ℝ) - 1) := by
      apply Real.log_nonneg; push_cast; linarith
    have hY_bound : ∑ k ∈ range (K + 1), 3 * (Y / (((k : ℝ) + 1 / 2) * (q : ℝ))) ≤
        5 * Y / (q : ℝ) * Real.log X := by
      rw [hY_eq]
      have hcoef : 3 * (2 * ∑ r ∈ Icc 1 (K + 1), (1 : ℝ) / (2 * (r : ℝ) - 1)) ≤ 5 * Real.log X := by
        linarith
      calc (Y / (q : ℝ)) * (3 * (2 * ∑ r ∈ Icc 1 (K + 1), (1 : ℝ) / (2 * (r : ℝ) - 1)))
          ≤ (Y / (q : ℝ)) * (5 * Real.log X) :=
            mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = 5 * Y / (q : ℝ) * Real.log X := by ring
    linarith
