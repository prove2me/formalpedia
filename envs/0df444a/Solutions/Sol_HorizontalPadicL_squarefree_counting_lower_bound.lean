-- Prove2me | solution 1 for HorizontalPadicL.squarefree_counting_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T00:17:06.330476+00:00
-- url     : https://prove2.me/submissions/ccf96e38-422c-4f9f-9878-17def18e1979

import Mathlib

set_option autoImplicit false

open Finset

theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    c * (N : ℝ) ≤ (((Finset.range (N + 1)).filter (fun n : ℕ => Squarefree n)).card : ℝ) := by
  -- 0 is not squarefree
  have hsf0 : ¬ Squarefree (0 : ℕ) := by
    intro h
    have h2 : (2 : ℕ) * 2 ∣ 0 := dvd_zero _
    have hu := h 2 h2
    rw [Nat.isUnit_iff] at hu
    omega
  -- every non-squarefree n ≥ 1 is divisible by a square d^2 with d ≥ 2
  have hdiv : ∀ n : ℕ, 1 ≤ n → ¬ Squarefree n → ∃ d : ℕ, 2 ≤ d ∧ d ^ 2 ∣ n := by
    intro n hn hns
    unfold Squarefree at hns
    obtain ⟨y, hy⟩ := not_forall.mp hns
    rw [Classical.not_imp] at hy
    obtain ⟨hdvd, hni⟩ := hy
    have hy2 : 2 ≤ y := by
      by_contra hlt
      have hlt2 : y < 2 := lt_of_not_ge hlt
      interval_cases y
      · exfalso
        simp only [mul_zero] at hdvd
        rw [zero_dvd_iff] at hdvd
        omega
      · exact absurd isUnit_one hni
    exact ⟨y, hy2, by rwa [pow_two]⟩
  -- telescoping bound: ∑_{d ∈ Icc 3 N} 1/(d(d-1)) ≤ 1/2
  have htele : ∀ N : ℕ, ∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) ≤ 1 / 2 := by
    intro N
    rcases lt_or_ge N 3 with hN | hN
    · rw [Finset.Icc_eq_empty (by omega : ¬ 3 ≤ N), Finset.sum_empty]
      norm_num
    · have hIcc : Finset.Icc 3 N = Finset.Ico 3 (N + 1) := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      have hN2 : N + 1 - 3 = N - 2 := by omega
      rw [hN2]
      have key : ∀ i : ℕ, (1 : ℝ) / ((((3 + i : ℕ)) : ℝ) * ((((3 + i : ℕ)) : ℝ) - 1))
          = (1 : ℝ) / ((i : ℝ) + 2) - (1 : ℝ) / ((i : ℝ) + 3) := by
        intro i
        have e1 : ((((3 + i : ℕ))) : ℝ) = (i : ℝ) + 3 := by push_cast; ring
        have hnn : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
        have h2 : ((i : ℝ) + 2) ≠ 0 := by linarith
        have h3 : ((i : ℝ) + 3) ≠ 0 := by linarith
        have h4 : ((i : ℝ) + 3) - 1 = (i : ℝ) + 2 := by ring
        rw [e1, h4]
        field_simp
        ring
      rw [Finset.sum_congr rfl (fun i _ => key i)]
      have hts : ∀ k : ℕ, ∑ i ∈ Finset.range k, ((1:ℝ)/((i:ℝ)+2) - (1:ℝ)/((i:ℝ)+3))
          = 1/2 - 1/((k:ℝ)+2) := by
        intro k
        induction k with
        | zero =>
          simp only [Finset.sum_range_zero, Nat.cast_zero]
          norm_num
        | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          have hkn : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.zero_le k
          have e : ((k + 1 : ℕ) : ℝ) + 2 = (k:ℝ) + 3 := by push_cast; ring
          rw [e]
          have h1 : ((k:ℝ)+2) ≠ 0 := by linarith
          have h3 : ((k:ℝ)+3) ≠ 0 := by linarith
          field_simp
          ring
      rw [hts (N - 2)]
      have hpos : (0:ℝ) ≤ 1/((((N-2:ℕ)):ℝ)+2) := by
        apply div_nonneg (by norm_num)
        have hnn := Nat.cast_nonneg (α := ℝ) (N - 2)
        linarith
      linarith
  -- sieve sum bound: ∑_{d ∈ Icc 2 N} 1/d^2 ≤ 3/4
  have hbasel : ∀ N : ℕ, ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 := by
    intro N
    rcases lt_or_ge N 3 with hN | hN
    · have hsub : Finset.Icc 2 N ⊆ {2} := by
        intro d hd
        simp only [Finset.mem_Icc] at hd
        simp only [Finset.mem_singleton]
        omega
      calc ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2
          ≤ ∑ d ∈ ({2} : Finset ℕ), (1 : ℝ) / (d : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
        _ = 1 / 4 := by norm_num
        _ ≤ 3 / 4 := by norm_num
    · have h2N : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [h2N, Finset.sum_insert (by simp)]
      have h1 : (1 : ℝ) / ((((2 : ℕ)) : ℝ) ^ 2) = 1 / 4 := by norm_num
      rw [h1]
      have h2 : ∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 1 / 2 := by
        calc ∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / (d : ℝ) ^ 2
            ≤ ∑ d ∈ Finset.Icc 3 N, (1 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) := by
              apply Finset.sum_le_sum
              intro d hd
              have hd3 : 3 ≤ d := (Finset.mem_Icc.mp hd).1
              have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
              have hdm1 : (0 : ℝ) < (d : ℝ) - 1 := by
                have h1d : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
                linarith
              have hpos : (0 : ℝ) < (d : ℝ) * ((d : ℝ) - 1) := mul_pos hdpos hdm1
              have hle : (d : ℝ) * ((d : ℝ) - 1) ≤ (d : ℝ) ^ 2 := by
                have hdm : (d : ℝ) - 1 ≤ (d : ℝ) := by linarith
                nlinarith [hdpos, hdm, hdm1]
              exact one_div_le_one_div_of_le hpos hle
          _ ≤ 1 / 2 := htele N
      linarith
  -- now the main proof with c = 1/4
  refine ⟨1 / 4, by norm_num, fun N hN => ?_⟩
  -- fiber card: multiples of d^2 in Icc 1 N
  have hfiber : ∀ d : ℕ, 2 ≤ d →
      ((Finset.Icc 1 N).filter (fun n : ℕ => d ^ 2 ∣ n)).card = N / d ^ 2 := by
    intro d hd
    have hdpos : 0 < d ^ 2 := by positivity
    have him : (Finset.Icc 1 N).filter (fun n : ℕ => d ^ 2 ∣ n)
        = (Finset.Icc 1 (N / d ^ 2)).image (fun m => d ^ 2 * m) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, hNn⟩, ⟨m, rfl⟩⟩
        have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · simp at h1
          · exact hpos
        refine ⟨m, ⟨hm1, ?_⟩, rfl⟩
        have hle : m * d ^ 2 ≤ N := by rw [mul_comm]; exact hNn
        exact (Nat.le_div_iff_mul_le hdpos).mpr hle
      · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
        have hmul : d ^ 2 * m ≤ N := by
          have hle : m * d ^ 2 ≤ N := (Nat.le_div_iff_mul_le hdpos).mp hmN
          rwa [mul_comm] at hle
        refine ⟨⟨?_, hmul⟩, ⟨m, rfl⟩⟩
        calc (1 : ℕ) ≤ d ^ 2 := hdpos
          _ ≤ d ^ 2 * m := by
            have h := Nat.mul_le_mul_left (d ^ 2) hm1
            rwa [mul_one] at h
    rw [him, Finset.card_image_of_injective]
    · rw [Nat.card_Icc, Nat.add_sub_cancel]
    · intro a b hab
      simp only at hab
      exact mul_left_cancel₀ (ne_of_gt hdpos) hab
  -- B : non-squarefree numbers in Icc 1 N
  set B := (Finset.Icc 1 N).filter (fun n : ℕ => ¬ Squarefree n) with hB
  have hsub : B ⊆ (Finset.Icc 2 N).biUnion (fun d => (Finset.Icc 1 N).filter (fun n : ℕ => d ^ 2 ∣ n)) := by
    intro n hn
    rw [hB] at hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, hNn⟩, hns⟩ := hn
    obtain ⟨d, hd2, hdvd⟩ := hdiv n h1 hns
    have h1d : d ^ 2 ≤ n := Nat.le_of_dvd (by omega) hdvd
    have h2d : d ≤ d ^ 2 := by nlinarith [hd2]
    have hdN : d ≤ N := by omega
    rw [Finset.mem_biUnion]
    exact ⟨d, Finset.mem_Icc.mpr ⟨hd2, hdN⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hNn⟩, hdvd⟩⟩
  have hcardB : (B.card : ℝ) ≤ ∑ d ∈ Finset.Icc 2 N, ((N / d ^ 2 : ℕ) : ℝ) := by
    have h1 : B.card ≤ ∑ d ∈ Finset.Icc 2 N, ((Finset.Icc 1 N).filter (fun n : ℕ => d ^ 2 ∣ n)).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have h2 : (∑ d ∈ Finset.Icc 2 N, ((Finset.Icc 1 N).filter (fun n : ℕ => d ^ 2 ∣ n)).card)
        = ∑ d ∈ Finset.Icc 2 N, (N / d ^ 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hfiber d (Finset.mem_Icc.mp hd).1
    have h3 : (B.card : ℝ) ≤ ((∑ d ∈ Finset.Icc 2 N, (N / d ^ 2) : ℕ) : ℝ) := by
      rw [← h2]
      exact_mod_cast h1
    rwa [Nat.cast_sum] at h3
  have hsum : ∑ d ∈ Finset.Icc 2 N, ((N / d ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) * (3 / 4) := by
    calc ∑ d ∈ Finset.Icc 2 N, ((N / d ^ 2 : ℕ) : ℝ)
        ≤ ∑ d ∈ Finset.Icc 2 N, (N : ℝ) / (d : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro d hd
          have h := Nat.cast_div_le (α := ℝ) (m := N) (n := d ^ 2)
          rwa [Nat.cast_pow] at h
      _ = (N : ℝ) * ∑ d ∈ Finset.Icc 2 N, 1 / (d : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
      _ ≤ (N : ℝ) * (3 / 4) :=
          mul_le_mul_of_nonneg_left (hbasel N) (by positivity)
  -- relate the target filter (over range (N+1)) to the filter over Icc 1 N
  have hSeq : (Finset.range (N + 1)).filter (fun n : ℕ => Squarefree n)
      = (Finset.Icc 1 N).filter (fun n : ℕ => Squarefree n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hn, hsq⟩
      rcases eq_or_ne n 0 with rfl | hne
      · exact absurd hsq hsf0
      · exact ⟨⟨Nat.pos_of_ne_zero hne, by omega⟩, hsq⟩
    · rintro ⟨⟨h1, hNn⟩, hsq⟩
      exact ⟨by omega, hsq⟩
  have hpart : ((Finset.Icc 1 N).filter (fun n : ℕ => Squarefree n)).card + B.card = N := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.Icc 1 N) (fun n : ℕ => Squarefree n)
    rw [Nat.card_Icc] at h
    have hNN : N + 1 - 1 = N := by omega
    rw [hNN, ← hB] at h
    exact h
  -- final assembly
  rw [hSeq]
  have hBbound : (B.card : ℝ) ≤ (N : ℝ) * (3 / 4) := hcardB.trans hsum
  have hcast : ((((Finset.Icc 1 N).filter (fun n : ℕ => Squarefree n)).card : ℕ) : ℝ)
      + (B.card : ℝ) = (N : ℝ) := by exact_mod_cast hpart
  have hgoal : (1 / 4 : ℝ) * (N : ℝ)
      ≤ ((((Finset.Icc 1 N).filter (fun n : ℕ => Squarefree n)).card : ℕ) : ℝ) := by
    linarith
  exact hgoal
