-- Prove2me | solution 1 for HTInsensBW.PhaseType.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T23:08:09.022834+00:00
-- url     : https://prove2.me/submissions/f3b02b12-04e8-4380-abb0-74d71a174822

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBWL10

open Finset HTInsensBW.PhaseType

lemma pow_le_sum_choose (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ (k+1) ≤ ((k+1).factorial : ℝ) * ∑ j ∈ range ⌈y⌉₊, ((j + k).choose k : ℝ) := by
  have h1 : y ^ (k+1) ≤ (⌈y⌉₊ : ℝ) ^ (k+1) := pow_le_pow_left₀ hy (Nat.le_ceil y) _
  rcases Nat.eq_zero_or_eq_succ_pred ⌈y⌉₊ with h0 | hK
  · rw [h0] at h1 ⊢
    simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow] at h1
    simpa using h1
  · set K' := ⌈y⌉₊.pred
    rw [hK] at h1 ⊢
    have hs : ∑ j ∈ range (K' + 1), ((j + k).choose k : ℝ) = ((K' + k + 1).choose (k+1) : ℝ) := by
      exact_mod_cast Nat.sum_range_add_choose K' k
    rw [hs]
    have h2 : ((K'+1) : ℕ) ^ (k+1) ≤ (K'+1).ascFactorial (k+1) := Nat.pow_succ_le_ascFactorial _ _
    rw [Nat.ascFactorial_eq_factorial_mul_choose] at h2
    have h3 : (((K'+1 : ℕ) : ℝ)) ^ (k+1) ≤ ((k+1).factorial : ℝ) * ((K' + (k + 1)).choose (k+1) : ℝ) := by
      exact_mod_cast h2
    have : K' + k + 1 = K' + (k+1) := by omega
    rw [this]
    exact h1.trans (by simpa using h3)

lemma moment_of_tail {S : Type*} (π : S → ℝ) (hπ0 : ∀ n, 0 ≤ π n) (hπ : HasSum π 1)
    (W : S → ℝ) (hW : ∀ n, 0 ≤ W n) (a b β : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (htail : ∀ j : ℕ, ∑' n, (if a + b * j < W n then π n else 0) ≤ β ^ (j+1)) (k : ℕ) :
    Summable (fun n => π n * W n ^ (k+1)) ∧
    ∑' n, π n * W n ^ (k+1) ≤
      2 ^ k * (a ^ (k+1) + b ^ (k+1) * (k+1).factorial / (1 - β) ^ (k+1)) := by
  set Y : S → ℝ := fun n => max 0 ((W n - a) / b) with hYdef
  have hY0 : ∀ n, 0 ≤ Y n := fun n => le_max_left _ _
  have hWY : ∀ n, W n ≤ a + b * Y n := by
    intro n
    have : (W n - a) / b ≤ Y n := le_max_right _ _
    have := (div_le_iff₀ hb).1 this
    linarith
  have hind : ∀ n (j : ℕ), j < ⌈Y n⌉₊ → a + b * j < W n := by
    intro n j hj
    have hj' : (j : ℝ) < Y n := Nat.lt_ceil.1 hj
    have hjpos : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hYeq : Y n = (W n - a) / b := by
      rcases le_total 0 ((W n - a) / b) with h | h
      · exact max_eq_right h
      · have : Y n = 0 := max_eq_left h
        linarith
    rw [hYeq, lt_div_iff₀ hb] at hj'
    linarith
  have hπs : Summable π := hπ.summable
  have hite_s : ∀ j : ℕ, Summable (fun n => if a + b * j < W n then π n else 0) := by
    intro j
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hπs
    · split_ifs <;> simp [hπ0 n]
    · split_ifs <;> simp [hπ0 n]
  have hgeo : Summable (fun j : ℕ => ((j + k).choose k : ℝ) * β ^ j) :=
    summable_choose_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  have hgeo_t : ∑' j : ℕ, ((j + k).choose k : ℝ) * β ^ j = 1 / (1 - β) ^ (k+1) :=
    tsum_choose_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  set c : ℝ := 2 ^ k * (a ^ (k+1) + b ^ (k+1) * (k+1).factorial / (1 - β) ^ (k+1)) with hc
  have hbound : ∀ s : Finset S, ∑ n ∈ s, π n * W n ^ (k+1) ≤ c := by
    intro s
    set M := s.sup (fun n => ⌈Y n⌉₊)
    have hpt : ∀ n ∈ s, π n * W n ^ (k+1) ≤
        2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0)) := by
      intro n hn
      have e1 : W n ^ (k+1) ≤ (a + b * Y n) ^ (k+1) := pow_le_pow_left₀ (hW n) (hWY n) _
      have e2 : (a + b * Y n) ^ (k+1) ≤ 2 ^ k * (a ^ (k+1) + (b * Y n) ^ (k+1)) := by
        simpa using add_pow_le ha (mul_nonneg hb.le (hY0 n)) (k+1)
      have e3 : Y n ^ (k+1) ≤ ((k+1).factorial : ℝ) * ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) :=
        pow_le_sum_choose _ (hY0 n) k
      have e4 : (∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n ≤
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
        rw [Finset.sum_mul]
        have hsub : range ⌈Y n⌉₊ ⊆ range M := by
          apply Finset.range_subset_range.2
          exact Finset.le_sup (f := fun n => ⌈Y n⌉₊) hn
        calc ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) * π n
            = ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [if_pos (hind n j (Finset.mem_range.1 hj))]
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro j _ _
              apply mul_nonneg (Nat.cast_nonneg _)
              split_ifs <;> simp [hπ0 n]
      have hp := hπ0 n
      calc π n * W n ^ (k+1) ≤ π n * (2 ^ k * (a ^ (k+1) + (b * Y n) ^ (k+1))) :=
            mul_le_mul_of_nonneg_left (e1.trans e2) hp
        _ = 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (Y n ^ (k+1) * π n)) := by ring
        _ ≤ 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (((k+1).factorial : ℝ) *
              ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0))) := by
            have e5 : Y n ^ (k+1) * π n ≤ ((k+1).factorial : ℝ) *
                ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
              calc Y n ^ (k+1) * π n ≤ (((k+1).factorial : ℝ) * ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n :=
                    mul_le_mul_of_nonneg_right e3 hp
                _ = ((k+1).factorial : ℝ) * ((∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
            have hb' : 0 ≤ b ^ (k+1) := by positivity
            have h2k : (0:ℝ) ≤ 2 ^ k := by positivity
            exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left e5 hb') _) h2k
        _ = _ := by ring
    have hsum1 : ∑ n ∈ s, π n ≤ 1 := sum_le_hasSum s (fun n _ => hπ0 n) hπ
    have hsum2 : ∀ j : ℕ, ∑ n ∈ s, (if a + b * j < W n then π n else 0) ≤ β ^ (j+1) := by
      intro j
      refine le_trans ?_ (htail j)
      apply Summable.sum_le_tsum s _ (hite_s j)
      intro n _
      split_ifs <;> simp [hπ0 n]
    have hsum3 : ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1) ≤ 1 / (1 - β) ^ (k+1) := by
      calc ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1)
          = β * ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ 1 * ∑' j : ℕ, ((j + k).choose k : ℝ) * β ^ j := by
            apply mul_le_mul hβ1.le _ (Finset.sum_nonneg (fun j _ => by positivity)) zero_le_one
            apply Summable.sum_le_tsum _ (fun j _ => by positivity) hgeo
        _ = _ := by rw [hgeo_t, one_mul]
    calc ∑ n ∈ s, π n * W n ^ (k+1)
        ≤ ∑ n ∈ s, 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0)) :=
          Finset.sum_le_sum hpt
      _ = 2 ^ k * (a ^ (k+1) * ∑ n ∈ s, π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) *
            ∑ n ∈ s, (if a + b * j < W n then π n else 0)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_comm]
          congr 3
          apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
      _ ≤ 2 ^ k * (a ^ (k+1) * 1 + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1)) := by
          gcongr with j hj
          exact hsum2 j
      _ ≤ 2 ^ k * (a ^ (k+1) * 1 + b ^ (k+1) * (k+1).factorial * (1 / (1 - β) ^ (k+1))) := by
          gcongr
      _ = c := by rw [hc]; ring
  have hnn : 0 ≤ fun n => π n * W n ^ (k+1) := fun n => mul_nonneg (hπ0 n) (pow_nonneg (hW n) _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩


/-- Steady-state drift is zero (generic, nonnegative rates and nonnegative `V`). -/
lemma stationary_drift_zero {S : Type*} (q : S → S → ℝ) (π : S → ℝ) (hπ : IsStationary q π)
    (hq0 : ∀ i j, 0 ≤ q i j) (V : S → ℝ) (hV0 : ∀ i, 0 ≤ V i)
    (hqs : ∀ i, Summable (q i)) (hqVs : ∀ i, Summable (fun j => q i j * V j))
    (hA : Summable (fun i => π i * ∑' j, q i j * V j))
    (hB : Summable (fun i => π i * V i * ∑' j, q i j)) :
    Summable (fun i => π i * drift q V i) ∧ ∑' i, π i * drift q V i = 0 := by
  have hπ0 := hπ.1
  have hdr : ∀ i, π i * drift q V i = π i * ∑' j, q i j * V j - π i * V i * ∑' j, q i j := by
    intro i
    unfold drift
    have : ∑' j, q i j * (V j - V i) = ∑' j, q i j * V j - V i * ∑' j, q i j := by
      have e : (fun j => q i j * (V j - V i)) = fun j => q i j * V j - q i j * V i := by
        funext j; ring
      rw [e, Summable.tsum_sub (hqVs i) ((hqs i).mul_right _), tsum_mul_right]; ring
    rw [this]; ring
  simp_rw [hdr]
  refine ⟨hA.sub hB, ?_⟩
  rw [Summable.tsum_sub hA hB, sub_eq_zero]
  set F : S → S → ℝ := fun i j => π i * q i j * V j with hF
  have hF0 : ∀ i j, 0 ≤ F i j := fun i j => mul_nonneg (mul_nonneg (hπ0 i) (hq0 i j)) (hV0 j)
  have hFrow : ∀ i, Summable (F i) := fun i => by
    have := (hqVs i).mul_left (π i)
    refine this.congr (fun j => ?_); simp only [hF]; ring
  have hFrowsum : ∀ i, ∑' j, F i j = π i * ∑' j, q i j * V j := fun i => by
    rw [← tsum_mul_left]; apply tsum_congr; intro j; simp only [hF]; ring
  have hFu : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg (f := Function.uncurry F) (fun p => hF0 p.1 p.2)]
    refine ⟨fun i => hFrow i, ?_⟩
    refine hA.congr (fun i => ?_)
    simp only [Function.uncurry]
    rw [hFrowsum]
  have hFcol : ∀ j, Summable (fun i => F i j) := by
    intro j
    have := hFu.prod_symm.prod_factor j
    simpa [Function.uncurry] using this
  have h1 : ∑' i, π i * ∑' j, q i j * V j = ∑' i, ∑' j, F i j := by
    apply tsum_congr; intro i; rw [hFrowsum]
  rw [h1, ← Summable.tsum_comm' hFu hFrow hFcol]
  apply tsum_congr
  intro j
  have : ∑' i, F i j = V j * ∑' i, π i * q i j := by
    rw [← tsum_mul_left]; apply tsum_congr; intro i; simp only [hF]; ring
  rw [this, ← hπ.2.2 j]; ring



lemma clip_mono (M c x y : ℝ) (h : x ≤ y) : min M (max c x) ≤ min M (max c y) :=
  min_le_min_left _ (max_le_max_left _ h)

lemma clip_lip (M c x y : ℝ) (h : x ≤ y) : min M (max c y) - min M (max c x) ≤ y - x := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma bgt_step {X : Type*} (q : X → X → ℝ) (hq0 : ∀ i j, 0 ≤ q i j) (hqs : ∀ i, Summable (q i))
    (qbar : ℝ) (hqbar : ∀ i, ∑' j, q i j ≤ qbar)
    (π : X → ℝ) (hπ : IsStationary q π) (V : X → ℝ) (hV : ∀ i, 0 ≤ V i)
    (γ B : ℝ) (hγ : 0 < γ) (hdrift : ∀ i, B < V i → drift q V i ≤ -γ)
    (ν : ℝ) (hν0 : 0 ≤ ν) (hν : ∀ i j, 0 < q i j → |V j - V i| ≤ ν)
    (qmax : ℝ) (hqm0 : 0 ≤ qmax) (hqmax : ∀ i, ∑' j, (if V i < V j then q i j else 0) ≤ qmax)
    (c : ℝ) (hc : B ≤ c + ν) :
    γ * ∑' i, (if c + ν < V i then π i else 0) ≤
      ν * qmax * ((∑' i, (if c - ν < V i then π i else 0)) -
        ∑' i, (if c + ν < V i then π i else 0)) := by
  classical
  have hπ0 := hπ.1
  have hπs : Summable π := hπ.2.1.summable
  have hind : ∀ (P : X → Prop) [DecidablePred P], Summable (fun i => if P i then π i else 0) := by
    intro P _
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hπs
    · split_ifs <;> simp [hπ0 i]
    · split_ifs <;> simp [hπ0 i]
  have hqb : ∀ i, 0 ≤ ∑' j, q i j := fun i => tsum_nonneg (fun j => hq0 i j)
  set R := ν * qmax * ((∑' i, (if c - ν < V i then π i else 0)) -
      ∑' i, (if c + ν < V i then π i else 0)) with hR
  -- the truncated bound for each level M
  have hM : ∀ M : ℝ, 0 ≤ M →
      γ * ∑' i, (if c + ν < V i ∧ V i < M then π i else 0) ≤ R := by
    intro M hM0
    set W : X → ℝ := fun i => min M (max c (V i)) with hW
    have hW0 : ∀ i, 0 ≤ W i := fun i => le_min hM0 ((hV i).trans (le_max_right _ _))
    have hWM : ∀ i, W i ≤ M := fun i => min_le_left _ _
    have hqWs : ∀ i, Summable (fun j => q i j * W j) := fun i =>
      Summable.of_nonneg_of_le (fun j => mul_nonneg (hq0 i j) (hW0 j))
        (fun j => mul_le_mul_of_nonneg_left (hWM j) (hq0 i j)) ((hqs i).mul_right M)
    have hA : Summable (fun i => π i * ∑' j, q i j * W j) := by
      refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hπ0 i)
        (tsum_nonneg (fun j => mul_nonneg (hq0 i j) (hW0 j)))) (fun i => ?_) (hπs.mul_right (qbar * M))
      have h1 : ∑' j, q i j * W j ≤ qbar * M := by
        calc ∑' j, q i j * W j ≤ ∑' j, q i j * M :=
              Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hWM j) (hq0 i j))
                (hqWs i) ((hqs i).mul_right M)
          _ = (∑' j, q i j) * M := tsum_mul_right
          _ ≤ qbar * M := mul_le_mul_of_nonneg_right (hqbar i) hM0
      exact mul_le_mul_of_nonneg_left h1 (hπ0 i)
    have hB : Summable (fun i => π i * W i * ∑' j, q i j) := by
      refine Summable.of_nonneg_of_le (fun i => mul_nonneg (mul_nonneg (hπ0 i) (hW0 i)) (hqb i))
        (fun i => ?_) (hπs.mul_right (M * qbar))
      have := mul_le_mul (hWM i) (hqbar i) (hqb i) hM0
      have := mul_le_mul_of_nonneg_left this (hπ0 i)
      linarith
    obtain ⟨hs, hzero⟩ := stationary_drift_zero q π hπ hq0 W hW0 hqs hqWs hA hB
    -- pointwise drift bound
    have hpt : ∀ i, drift q W i ≤
        ν * qmax * ((if c - ν < V i then 1 else 0) - (if c + ν < V i then 1 else 0)) -
          γ * (if c + ν < V i ∧ V i < M then 1 else 0) := by
      intro i
      unfold drift
      by_cases h1 : V i ≤ c - ν
      · have : ∀ j, q i j * (W j - W i) = 0 := by
          intro j
          rcases eq_or_lt_of_le (hq0 i j) with hq | hq
          · rw [← hq]; ring
          · have hj := hν i j hq
            have hj' : V j ≤ c := by have := (abs_le.1 hj).2; linarith
            have hWj : W j = min M c := by simp only [hW, max_eq_left hj']
            have hWi : W i = min M c := by simp only [hW]; rw [max_eq_left (by linarith)]
            rw [hWj, hWi]; ring
        rw [tsum_congr this, tsum_zero, if_neg (by intro h; linarith),
          if_neg (by intro h; linarith), if_neg (by intro h; linarith [h.1])]
        norm_num
      · push_neg at h1
        by_cases h2 : V i ≤ c + ν
        · rw [if_pos h1, if_neg (by intro h; linarith), if_neg (by intro h; linarith [h.1])]
          have hterm : ∀ j, q i j * (W j - W i) ≤ ν * (if V i < V j then q i j else 0) := by
            intro j
            rcases eq_or_lt_of_le (hq0 i j) with hq | hq
            · rw [← hq]; simp
            · by_cases hv : V i < V j
              · rw [if_pos hv]
                have := clip_lip M c (V i) (V j) hv.le
                have hj := (abs_le.1 (hν i j hq)).2
                have : W j - W i ≤ ν := by simp only [hW]; linarith
                nlinarith
              · rw [if_neg hv]
                push_neg at hv
                have := clip_mono M c (V j) (V i) hv
                have : W j - W i ≤ 0 := by simp only [hW]; linarith
                nlinarith
          have hs2 : Summable (fun j => ν * (if V i < V j then q i j else 0)) := by
            refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hqs i))
            · split_ifs <;> simp [hq0 i j]
            · split_ifs <;> simp [hq0 i j]
          have hs1 : Summable (fun j => q i j * (W j - W i)) :=
            ((hqWs i).sub ((hqs i).mul_right (W i))).congr (fun j => by ring)
          calc ∑' j, q i j * (W j - W i) ≤ ∑' j, ν * (if V i < V j then q i j else 0) :=
                Summable.tsum_le_tsum hterm hs1 hs2
            _ = ν * ∑' j, (if V i < V j then q i j else 0) := tsum_mul_left
            _ ≤ ν * qmax := mul_le_mul_of_nonneg_left (hqmax i) hν0
            _ = _ := by ring
        · push_neg at h2
          rw [if_pos h1, if_pos h2, sub_self, mul_zero, zero_sub]
          have hs1 : Summable (fun j => q i j * (W j - W i)) :=
            ((hqWs i).sub ((hqs i).mul_right (W i))).congr (fun j => by ring)
          by_cases h3 : V i < M
          · rw [if_pos ⟨h2, h3⟩]
            have hWi : W i = V i := by
              simp only [hW]; rw [max_eq_right (by linarith), min_eq_right h3.le]
            have hterm : ∀ j, q i j * (W j - W i) ≤ q i j * (V j - V i) := by
              intro j
              rcases eq_or_lt_of_le (hq0 i j) with hq | hq
              · rw [← hq]; simp
              · apply mul_le_mul_of_nonneg_left _ (hq0 i j)
                have hj := (abs_le.1 (hν i j hq)).1
                have hcj : c ≤ V j := by linarith
                have : W j ≤ V j := by simp only [hW]; rw [max_eq_right hcj]; exact min_le_right _ _
                linarith
            have hs2 : Summable (fun j => q i j * (V j - V i)) := by
              refine Summable.of_norm_bounded ((hqs i).mul_right ν) (fun j => ?_)
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 i j)]
              rcases eq_or_lt_of_le (hq0 i j) with hq | hq
              · rw [← hq]; simp
              · exact mul_le_mul_of_nonneg_left (hν i j hq) (hq0 i j)
            have hd := hdrift i (by linarith)
            unfold drift at hd
            calc ∑' j, q i j * (W j - W i) ≤ ∑' j, q i j * (V j - V i) :=
                  Summable.tsum_le_tsum hterm hs1 hs2
              _ ≤ -γ := hd
              _ = _ := by ring
          · push_neg at h3
            rw [if_neg (by intro h; linarith [h.2])]
            have hWi : W i = M := by
              simp only [hW]; exact min_eq_left (h3.trans (le_max_right _ _))
            have hterm : ∀ j, q i j * (W j - W i) ≤ 0 := by
              intro j
              rw [hWi]
              exact mul_nonpos_of_nonneg_of_nonpos (hq0 i j) (by linarith [hWM j])
            calc ∑' j, q i j * (W j - W i) ≤ ∑' j, (0 : ℝ) :=
                  Summable.tsum_le_tsum hterm hs1 summable_zero
              _ = _ := by simp
    -- sum up
    have hs3 : Summable (fun i => π i * (ν * qmax * ((if c - ν < V i then 1 else 0) -
        (if c + ν < V i then 1 else 0)) - γ * (if c + ν < V i ∧ V i < M then 1 else 0))) := by
      refine Summable.of_norm_bounded (hπs.mul_right (ν * qmax + γ)) (fun i => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hπ0 i)]
      apply mul_le_mul_of_nonneg_left _ (hπ0 i)
      have hnq : 0 ≤ ν * qmax := mul_nonneg hν0 hqm0
      have hAB : |((if c - ν < V i then (1:ℝ) else 0) - (if c + ν < V i then 1 else 0))| ≤ 1 := by
        split_ifs <;> norm_num
      have hC : |(if c + ν < V i ∧ V i < M then (1:ℝ) else 0)| ≤ 1 := by
        split_ifs <;> norm_num
      calc _ ≤ |ν * qmax * ((if c - ν < V i then (1:ℝ) else 0) - (if c + ν < V i then 1 else 0))| +
            |γ * (if c + ν < V i ∧ V i < M then (1:ℝ) else 0)| := abs_sub _ _
        _ ≤ ν * qmax * 1 + γ * 1 := by
            rw [abs_mul (ν * qmax), abs_mul γ, abs_of_nonneg hnq, abs_of_pos hγ]
            exact add_le_add (mul_le_mul_of_nonneg_left hAB hnq) (mul_le_mul_of_nonneg_left hC hγ.le)
        _ = _ := by ring
    have hle := Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (hpt i) (hπ0 i)) hs hs3
    rw [hzero] at hle
    have e1 : ∀ i, π i * (ν * qmax * ((if c - ν < V i then 1 else 0) -
        (if c + ν < V i then 1 else 0)) - γ * (if c + ν < V i ∧ V i < M then 1 else 0)) =
        ν * qmax * ((if c - ν < V i then π i else 0) - (if c + ν < V i then π i else 0)) -
        γ * (if c + ν < V i ∧ V i < M then π i else 0) := by
      intro i
      split_ifs <;> ring
    simp_rw [e1] at hle
    rw [Summable.tsum_sub ((((hind _).sub (hind _))).mul_left _) ((hind _).mul_left _),
      tsum_mul_left, tsum_mul_left, Summable.tsum_sub (hind _) (hind _)] at hle
    linarith
  -- pass to the limit M → ∞ via finite sums
  have hT : ∑' i, (if c + ν < V i then π i else 0) ≤ R / γ := by
    apply Real.tsum_le_of_sum_le (fun i => by split_ifs <;> simp [hπ0 i])
    intro s
    set M := 1 + ∑ i ∈ s, V i with hMdef
    have hM0 : 0 ≤ M := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ s) => hV i); linarith
    have h1 : ∑ i ∈ s, (if c + ν < V i then π i else 0) ≤
        ∑' i, (if c + ν < V i ∧ V i < M then π i else 0) := by
      calc ∑ i ∈ s, (if c + ν < V i then π i else 0)
          = ∑ i ∈ s, (if c + ν < V i ∧ V i < M then π i else 0) := by
            apply Finset.sum_congr rfl; intro i hi
            have : V i < M := by
              have := Finset.single_le_sum (f := V) (fun j _ => hV j) hi
              linarith
            by_cases h : c + ν < V i <;> simp [h, this]
        _ ≤ _ := Summable.sum_le_tsum s (fun i _ => by split_ifs <;> simp [hπ0 i]) (hind _)
    have h2 := hM M hM0
    rw [le_div_iff₀ hγ]
    nlinarith
  rw [le_div_iff₀ hγ] at hT
  linarith

end HTInsensBWL10

open HTInsensBW.PhaseType HTInsensBWL10

theorem solution {X : Type*} [Countable X] (q : X → X → ℝ)
    (hq0 : ∀ i j, 0 ≤ q i j) (hqd : ∀ i, q i i = 0) (hqs : ∀ i, Summable (q i))
    (qbar : ℝ) (hqbar : ∀ i, ∑' j, q i j ≤ qbar)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j)
    (π : X → ℝ) (hπ : IsStationary q π)
    (V : X → ℝ) (hV : ∀ i, 0 ≤ V i)
    (γ B : ℝ) (hγ : 0 < γ) (hB : 0 < B) (hdrift : ∀ i, B < V i → drift q V i ≤ -γ)
    (νmax : ℝ) (hν0 : 0 ≤ νmax) (hν : ∀ i j, 0 < q i j → |V j - V i| ≤ νmax)
    (qmax : ℝ) (hqm0 : 0 ≤ qmax)
    (hqmax : ∀ i, ∑' j, (if V i < V j then q i j else 0) ≤ qmax) :
    (∀ j : ℕ, ∑' i, (if B + 2 * νmax * j < V i then π i else 0) ≤
        (qmax * νmax / (qmax * νmax + γ)) ^ (j + 1)) ∧
    (∀ m : ℕ, Summable (fun i => π i * V i ^ m) ∧
      ∑' i, π i * V i ^ m ≤
        (2 * B) ^ m + (4 * νmax) ^ m * ((qmax * νmax + γ) / γ) ^ m * (m.factorial : ℝ)) := by
  classical
  have hπ0 := hπ.1
  have hπs : Summable π := hπ.2.1.summable
  set β := qmax * νmax / (qmax * νmax + γ) with hβ
  have hden : 0 < qmax * νmax + γ := by have := mul_nonneg hqm0 hν0; linarith
  have hβ0 : 0 ≤ β := div_nonneg (mul_nonneg hqm0 hν0) hden.le
  have hβ1 : β < 1 := by rw [hβ, div_lt_one hden]; linarith
  set T : ℝ → ℝ := fun a => ∑' i, (if a < V i then π i else 0) with hT
  have hTs : ∀ a, Summable (fun i => if a < V i then π i else 0) := by
    intro a
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hπs
    · split_ifs <;> simp [hπ0 i]
    · split_ifs <;> simp [hπ0 i]
  have hT1 : ∀ a, T a ≤ 1 := by
    intro a
    rw [← hπ.2.1.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => by split_ifs <;> simp [hπ0 i]) (hTs a) hπs
  -- one step of the recursion
  have hstep : ∀ a, B ≤ a → T a ≤ β * T (a - 2 * νmax) := by
    intro a ha
    have h := bgt_step q hq0 hqs qbar hqbar π hπ V hV γ B hγ hdrift νmax hν0 hν qmax hqm0 hqmax
      (a - νmax) (by linarith)
    have e1 : a - νmax + νmax = a := by ring
    have e2 : a - νmax - νmax = a - 2 * νmax := by ring
    rw [e1, e2] at h
    change γ * T a ≤ νmax * qmax * (T (a - 2 * νmax) - T a) at h
    rw [hβ, div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  have htail : ∀ j : ℕ, T (B + 2 * νmax * j) ≤ β ^ (j + 1) := by
    intro j
    induction j with
    | zero =>
      have := hstep B le_rfl
      simp only [Nat.cast_zero, mul_zero, add_zero, zero_add, pow_one]
      have h1 := hT1 (B - 2 * νmax)
      nlinarith
    | succ j ih =>
      have := hstep (B + 2 * νmax * ((j + 1 : ℕ) : ℝ)) (by
        have : 0 ≤ 2 * νmax * ((j + 1 : ℕ) : ℝ) := by positivity
        linarith)
      have e : B + 2 * νmax * ((j + 1 : ℕ) : ℝ) - 2 * νmax = B + 2 * νmax * j := by
        push_cast; ring
      rw [e] at this
      calc T (B + 2 * νmax * ((j + 1 : ℕ) : ℝ)) ≤ β * T (B + 2 * νmax * j) := this
        _ ≤ β * β ^ (j + 1) := mul_le_mul_of_nonneg_left ih hβ0
        _ = β ^ (j + 1 + 1) := by ring
  refine ⟨fun j => htail j, ?_⟩
  intro m
  rcases m with _ | k
  · refine ⟨by simpa using hπs, ?_⟩
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    rw [hπ.2.1.tsum_eq]; norm_num
  · rcases eq_or_lt_of_le hν0 with hν00 | hνpos
    · -- νmax = 0 : V ≤ B almost surely
      have hβz : β = 0 := by rw [hβ, ← hν00]; simp
      have hzero : ∀ i, B < V i → π i = 0 := by
        intro i hi
        have h1 := htail 0
        rw [hβz] at h1
        simp only [zero_add, pow_one, Nat.cast_zero, mul_zero, add_zero] at h1
        have h2 : (if B < V i then π i else 0) ≤ T B :=
          Summable.le_tsum (hTs B) i (fun j _ => by split_ifs <;> simp [hπ0 j])
        rw [if_pos hi] at h2
        exact le_antisymm (by linarith) (hπ0 i)
      have hpt : ∀ i, π i * V i ^ (k + 1) ≤ π i * B ^ (k + 1) := by
        intro i
        by_cases hi : B < V i
        · rw [hzero i hi]; simp
        · push_neg at hi
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hV i) hi _) (hπ0 i)
      have hs : Summable (fun i => π i * V i ^ (k + 1)) :=
        Summable.of_nonneg_of_le (fun i => mul_nonneg (hπ0 i) (pow_nonneg (hV i) _)) hpt
          (hπs.mul_right _)
      refine ⟨hs, ?_⟩
      calc ∑' i, π i * V i ^ (k + 1) ≤ ∑' i, π i * B ^ (k + 1) :=
            Summable.tsum_le_tsum hpt hs (hπs.mul_right _)
        _ = B ^ (k + 1) := by rw [tsum_mul_right, hπ.2.1.tsum_eq, one_mul]
        _ ≤ (2 * B) ^ (k + 1) := pow_le_pow_left₀ hB.le (by linarith) _
        _ ≤ _ := by
            rw [← hν00]
            simp
    · obtain ⟨hs, hb⟩ := moment_of_tail π hπ0 hπ.2.1 V hV B (2 * νmax) β hB.le (by positivity)
        hβ0 hβ1 htail k
      refine ⟨hs, hb.trans ?_⟩
      have h1β : 1 / (1 - β) = (qmax * νmax + γ) / γ := by
        have h1 : 1 - β = γ / (qmax * νmax + γ) := by
          rw [hβ, eq_div_iff hden.ne', sub_mul, div_mul_cancel₀ _ hden.ne']; ring
        rw [h1, one_div_div]
      have e : (2 * νmax) ^ (k + 1) * ((k + 1).factorial : ℝ) / (1 - β) ^ (k + 1) =
          (2 * νmax) ^ (k + 1) * ((k + 1).factorial : ℝ) * (1 / (1 - β)) ^ (k + 1) := by
        rw [one_div_pow]; ring
      rw [e, h1β]
      set F : ℝ := ((k + 1).factorial : ℝ)
      set Q := ((qmax * νmax + γ) / γ) ^ (k + 1)
      have hF : 0 ≤ F := by positivity
      have hQ : 0 ≤ Q := by positivity
      have h22 : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ k * B ^ (k + 1) ≤ (2 * B) ^ (k + 1) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right h22 (by positivity)
      have h3 : (2 : ℝ) ^ k * ((2 * νmax) ^ (k + 1) * F * Q) ≤ (4 * νmax) ^ (k + 1) * Q * F := by
        have : (2 : ℝ) ^ k * (2 * νmax) ^ (k + 1) ≤ (4 * νmax) ^ (k + 1) := by
          rw [show (4 : ℝ) * νmax = 2 * (2 * νmax) by ring, mul_pow (2 : ℝ) (2 * νmax)]
          exact mul_le_mul_of_nonneg_right h22 (by positivity)
        have := mul_le_mul_of_nonneg_right this (mul_nonneg hF hQ)
        nlinarith
      nlinarith
