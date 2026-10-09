-- Prove2me | solution 1 for IntMul.HvdH.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T00:12:01.980344+00:00
-- url     : https://prove2.me/submissions/282e587c-ec4a-44bf-a200-cadfc66a618e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_IntMul_HvdH_corollary_5_5

open Real IntMul

namespace IntMulThm11

/-- Larger time budgets are still budgets. -/
lemma multipliesAt_mono {M : MultitapeTM} {n : ℕ} {τ τ' : ℝ} (h : MultipliesAt M n τ)
    (hle : τ ≤ τ') : MultipliesAt M n τ' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hle, hh⟩

/-- The worst-case time `sInf {τ | MultipliesAt M n τ}` is itself a valid budget. -/
lemma multipliesAt_sInf {M : MultitapeTM} {n : ℕ} (h : ∃ τ, MultipliesAt M n τ) :
    MultipliesAt M n (sInf {τ : ℝ | MultipliesAt M n τ}) := by
  set S : Set ℝ := {τ : ℝ | MultipliesAt M n τ}
  have hS : S = ⋂ (x : List Bool) (y : List Bool) (_ : x.length = n) (_ : y.length = n),
      {τ : ℝ | ∃ t : ℕ, (t : ℝ) ≤ τ ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))} := by
    ext τ; simp [S, MultipliesAt]
  have hclosed : IsClosed S := by
    rw [hS]
    refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    classical
    by_cases hex : ∃ t : ℕ, M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))
    · have : {τ : ℝ | ∃ t : ℕ, (t : ℝ) ≤ τ ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))} =
          Set.Ici ((Nat.find hex : ℕ) : ℝ) := by
        ext τ; simp only [Set.mem_ofPred_eq, Set.mem_Ici]; constructor
        · rintro ⟨t, ht, hh⟩; exact le_trans (by exact_mod_cast Nat.find_min' hex hh) ht
        · intro hτ; exact ⟨_, hτ, Nat.find_spec hex⟩
      rw [this]; exact isClosed_Ici
    · have : {τ : ℝ | ∃ t : ℕ, (t : ℝ) ≤ τ ∧ M.HaltsWithOutput x y t (bin (2 * n) (val x * val y))} = ∅ := by
        ext τ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨t, -, hh⟩; exact hex ⟨t, hh⟩
      rw [this]; exact isClosed_empty
  have hbdd : BddBelow S := by
    refine ⟨0, fun τ hτ => ?_⟩
    obtain ⟨t, ht, -⟩ := hτ (List.replicate n false) (List.replicate n false) (by simp) (by simp)
    exact le_trans (Nat.cast_nonneg t) ht
  exact hclosed.csInf_mem h hbdd

/-- `1296 b² < 2^(b-1)` once `b ≥ 30`. -/
lemma sq_lt_two_pow (b : ℕ) (hb : 30 ≤ b) : 1296 * b ^ 2 < 2 ^ (b - 1) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 - 1 = (k - 1) + 1 by omega,
      show (2 : ℕ) ^ (k - 1 + 1) = 2 ^ (k - 1) * 2 from pow_succ 2 (k - 1)]
    nlinarith

/-- The parameters `T` and `r` of §5.1 exist. -/
lemma exists_T_r (n b d : ℕ) (hb : 1 ≤ b) (hbn : b ≤ n) (hd : 1 ≤ d) :
    ∃ T r : ℕ, (∃ k : ℕ, T = 2 ^ k) ∧ 4 * (n : ℝ) / b ≤ T ∧ (T : ℝ) < 8 * (n : ℝ) / b ∧
      (∃ j : ℕ, r = 2 ^ j) ∧ (T : ℝ) ^ ((1 : ℝ) / d) ≤ r ∧ (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hn1 : (1 : ℝ) ≤ n / b := by
    rw [le_div_iff₀ hbR]; simpa using (show ((b : ℕ) : ℝ) ≤ n by exact_mod_cast hbn)
  have hexT : ∃ k : ℕ, 4 * (n : ℝ) / b ≤ (2 : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * (n : ℝ) / b) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  classical
  set k := Nat.find hexT
  have hk := Nat.find_spec hexT
  have hTlt : (2 : ℝ) ^ k < 8 * (n : ℝ) / b := by
    rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
    · rw [h0]; have : (8 : ℝ) * n / b = 8 * (n / b) := by ring
      rw [this]; norm_num; linarith
    · have hmin := Nat.find_min hexT (show k.pred < k by omega)
      rw [not_le] at hmin
      rw [hs, pow_succ]
      have : (8 : ℝ) * n / b = 2 * (4 * n / b) := by ring
      rw [this]; linarith
  set T : ℕ := 2 ^ k
  have hT1 : (1 : ℝ) ≤ T := by simp only [T]; push_cast; exact one_le_pow₀ (by norm_num)
  have hdR : (0 : ℝ) < 1 / d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hTd1 : (1 : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / d) := Real.one_le_rpow hT1 hdR.le
  have hexr : ∃ j : ℕ, (T : ℝ) ^ ((1 : ℝ) / d) ≤ (2 : ℝ) ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((T : ℝ) ^ ((1 : ℝ) / d)) (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  set j := Nat.find hexr
  have hj := Nat.find_spec hexr
  have hrlt : (2 : ℝ) ^ j < 2 * (T : ℝ) ^ ((1 : ℝ) / d) := by
    rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hs
    · rw [h0, pow_zero]; linarith
    · have hmin := Nat.find_min hexr (show j.pred < j by omega)
      rw [not_le] at hmin
      rw [hs, pow_succ]; linarith
  refine ⟨T, 2 ^ j, ⟨k, rfl⟩, ?_, ?_, ⟨j, rfl⟩, ?_, ?_⟩
  · simpa [T] using hk
  · simpa [T] using hTlt
  · push_cast; exact hj
  · push_cast; exact hrlt

end IntMulThm11

open IntMulThm11 in
theorem solution : MulTimeBound fun n => (n : ℝ) * Real.log n := by
  obtain ⟨M, hcorr, A, hrec⟩ := IntMul.HvdH.corollary_5_5 1729 (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 1729 ^ 12 := ⟨_, rfl⟩
  have hK30 : 30 ≤ K := by rw [hK]; norm_num
  rw [← hK] at hrec
  set N0 : ℕ := 2 ^ K with hN0
  set W : ℕ → ℝ := fun m => sInf {τ : ℝ | MultipliesAt M m τ} with hW
  set Tn : ℕ → ℝ := fun m => W m / ((m : ℝ) * Real.log m) with hTn
  have hN0big : 2 < N0 := by
    rw [hN0]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : (Finset.Ico 2 N0).Nonempty := ⟨2, by simp; omega⟩
  set B : ℝ := (Finset.Ico 2 N0).sup' hne Tn with hB
  set C : ℝ := max (max B (5000 * A)) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCB : B ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCA : 5000 * A ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  -- the induction of the paper: Tn n ≤ C for all n ≥ 2
  have hmain : ∀ n : ℕ, 2 ≤ n → Tn n ≤ C := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn2
    by_cases hsmall : n < N0
    · exact le_trans (Finset.le_sup' Tn (by simp; omega)) hCB
    · rw [not_lt] at hsmall
      set b := Nat.clog 2 n with hb_def
      have hb_big : K ≤ b := by
        have := Nat.clog_mono_right 2 hsmall
        rw [hN0, Nat.clog_pow 2 K (by norm_num)] at this
        exact this
      have hb30 : 30 ≤ b := le_trans hK30 hb_big
      have hbn : b ≤ n := by
        rw [hb_def]; exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
      obtain ⟨T, r, hTpow, hT1, hT2, hrpow, hr1, hr2⟩ :=
        exists_T_r n b 1729 (by omega) hbn (by norm_num)
      set p := 6 * b with hp_def
      set m := 3 * r * p with hm_def
      have hr1' : 1 ≤ r := by obtain ⟨j, rfl⟩ := hrpow; exact Nat.one_le_two_pow
      have hm2 : 2 ≤ m := by
        rw [hm_def, hp_def]; nlinarith
      -- 3rp < n
      have hmn : m < n := by
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hbR : (8 : ℝ) ≤ b := by exact_mod_cast (show 8 ≤ b by omega)
        have hbpos : (0 : ℝ) < b := by linarith
        have hTn : (T : ℝ) ≤ n := by
          have : 8 * (n : ℝ) / b ≤ n := by
            rw [div_le_iff₀ hbpos]; nlinarith
          linarith
        have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
        have hroot : (T : ℝ) ^ ((1 : ℝ) / 1729) ≤ Real.sqrt n := by
          rw [Real.sqrt_eq_rpow]
          calc (T : ℝ) ^ ((1 : ℝ) / 1729) ≤ (n : ℝ) ^ ((1 : ℝ) / 1729) :=
                Real.rpow_le_rpow hT0 hTn (by norm_num)
            _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
        have hsq : ((36 * b : ℕ) : ℝ) ≤ Real.sqrt n := by
          apply Real.le_sqrt_of_sq_le
          have h1 := sq_lt_two_pow b hb30
          have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
          rw [← hb_def] at h2
          have : (36 * b) ^ 2 < n := by
            calc (36 * b) ^ 2 = 1296 * b ^ 2 := by ring
              _ < 2 ^ (b - 1) := h1
              _ = 2 ^ b.pred := rfl
              _ < n := h2
          exact_mod_cast this.le
        have hmR : (m : ℝ) < n := by
          have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
          have hmexp : (m : ℝ) = 18 * b * r := by rw [hm_def, hp_def]; push_cast; ring
          calc (m : ℝ) = 18 * b * r := hmexp
            _ < 18 * b * (2 * (T : ℝ) ^ ((1 : ℝ) / 1729)) := by
                have : (0 : ℝ) < 18 * b := by positivity
                exact mul_lt_mul_of_pos_left (by simpa using hr2) this
            _ = (36 * b : ℝ) * (T : ℝ) ^ ((1 : ℝ) / 1729) := by ring
            _ ≤ (36 * b : ℝ) * Real.sqrt n := by gcongr
            _ ≤ Real.sqrt n * Real.sqrt n := by
                gcongr; push_cast at hsq; exact hsq
            _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
        exact_mod_cast hmR
      have hIH := ih m hmn hm2
      have hstep := hrec n hsmall b p T r hb_def rfl hTpow hT1 hT2 hrpow (by simpa using hr1)
        (by simpa using hr2)
      have hk : (1728 : ℝ) / ((1729 : ℕ) - 1 / 2) ≤ 1 - 1 / 5000 := by norm_num
      have hk0 : (0 : ℝ) ≤ (1728 : ℝ) / ((1729 : ℕ) - 1 / 2) := by norm_num
      have : Tn n < (1728 : ℝ) / ((1729 : ℕ) - 1 / 2) * Tn m + A := by
        simpa [hTn, hW, hm_def] using hstep
      have hC0 : 0 ≤ C := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hIH hk0]
  -- conclude
  refine ⟨M, hcorr, C, by linarith, 2, fun n hn _ => ?_⟩
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) * Real.log n := mul_pos hnpos hlog
  have hTle := hmain n hn
  have hWle : W n ≤ C * ((n : ℝ) * Real.log n) := by
    have := (div_le_iff₀ hden).1 (by simpa [hTn] using hTle)
    simpa [hW] using this
  exact multipliesAt_mono (multipliesAt_sInf (hcorr n (by omega))) hWle
