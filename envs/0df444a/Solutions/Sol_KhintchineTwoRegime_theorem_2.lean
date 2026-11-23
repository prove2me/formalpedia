-- Prove2me | solution 1 for KhintchineTwoRegime.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:20.615806+00:00
-- url     : https://prove2.me/submissions/a31d101a-e451-4057-93ab-127275525971
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_fourProfile
import Definitions.Def_KhintchineTwoRegime_Abound
import Definitions.Def_KhintchineTwoRegime_Phi
import Definitions.Def_KhintchineTwoRegime_pad
import Theorems.Thm_KhintchineTwoRegime_theorem_1
import Theorems.Thm_KhintchineTwoRegime_lemma_5
import Theorems.Thm_KhintchineTwoRegime_lemma_6
import Theorems.Thm_KhintchineTwoRegime_proper_unit_distance_sq
import Theorems.Thm_KhintchineTwoRegime_sixProfile_mem_Cn
import Theorems.Thm_KhintchineTwoRegime_sixProfile_K
import Theorems.Thm_KhintchineTwoRegime_theorem_2_q_bounds
import Theorems.Thm_KhintchineTwoRegime_Phi_strict
import Theorems.Thm_KhintchineTwoRegime_sixProfile_eq_of_interior_equality
import Theorems.Thm_KhintchineTwoRegime_sixProfile_endpoint

open KhintchineTwoRegime

private lemma d1_decimal :
    ((7663211842 : ℝ) / 10 ^ 10 < Real.sqrt (2 - Real.sqrt 966 / 22) ∧
      Real.sqrt (2 - Real.sqrt 966 / 22) < (7663211843 : ℝ) / 10 ^ 10) := by
  have hs : Real.sqrt 966 ^ 2 = 966 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 966 := Real.sqrt_nonneg _
  have hd : Real.sqrt (2 - Real.sqrt 966 / 22) ^ 2 =
      2 - Real.sqrt 966 / 22 := by
    apply Real.sq_sqrt
    nlinarith
  have hd0 : 0 ≤ Real.sqrt (2 - Real.sqrt 966 / 22) := Real.sqrt_nonneg _
  constructor
  · by_contra! h
    have hsq := mul_self_le_mul_self hd0 h
    have hsc : Real.sqrt 966 < 22 * (2 - ((7663211842 : ℝ) / 10 ^ 10) ^ 2) := by
      nlinarith
    have hsc2 := mul_self_lt_mul_self hs0 hsc
    nlinarith
  · by_contra! h
    have hpos : (0 : ℝ) ≤ (7663211843 : ℝ) / 10 ^ 10 := by norm_num
    have hsq := mul_self_le_mul_self hpos h
    have hsc : 22 * (2 - ((7663211843 : ℝ) / 10 ^ 10) ^ 2) < Real.sqrt 966 := by
      nlinarith
    have hnonneg : 0 ≤ 22 * (2 - ((7663211843 : ℝ) / 10 ^ 10) ^ 2) := by norm_num
    have hsc2 := mul_self_lt_mul_self hnonneg hsc
    nlinarith

theorem solution :
    (∀ n : ℕ, 6 ≤ n →
      ∀ τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22)),
        sixProfile n τ ∈ Cn n τ ∧
        (∀ ω ∈ Cn n τ, K n (sixProfile n τ) ≤ K n ω) ∧
        (∀ ω ∈ Cn n τ, K n ω = K n (sixProfile n τ) → ω = sixProfile n τ) ∧
        K n (sixProfile n τ) = Abound ((2 - τ ^ 2) / Real.sqrt 2)) ∧
    ((7663211842 : ℝ) / 10 ^ 10 < Real.sqrt (2 - Real.sqrt 966 / 22) ∧
      Real.sqrt (2 - Real.sqrt 966 / 22) < (7663211843 : ℝ) / 10 ^ 10) := by
  refine ⟨?_, d1_decimal⟩
  intro n hn τ hτ
  let q : ℝ := (2 - τ ^ 2) / Real.sqrt 2
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hq := theorem_2_q_bounds τ hτ
  have hmem := sixProfile_mem_Cn n hn τ hτ
  have hval := sixProfile_K n hn τ hτ
  change K n (sixProfile n τ) = Abound q at hval
  have key : ∀ ω ∈ Cn n τ, K n ω ≤ Abound q → ω = sixProfile n τ := by
    intro ω hω hcomp
    by_cases hend : τ = Real.sqrt (2 - Real.sqrt 2)
    · have ht1 := (theorem_1).2 n (by omega) τ hq.1 (le_of_eq hend)
      have hep := sixProfile_endpoint n (by omega)
      have hBA : (1 / Real.sqrt 2 +
          (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2))) = Abound q := by
        subst τ
        exact hep.2.symm
      have hlo := (theorem_1).1 n (by omega) τ ω hω
      rw [hBA] at hlo
      have hKeq : K n ω = Abound q := le_antisymm hcomp hlo
      have heq := ht1.2.2 ω hω (by rw [hKeq, ← hBA])
      rw [heq]
      subst τ
      exact hep.1.symm
    · have hgt : Real.sqrt (2 - Real.sqrt 2) < τ := lt_of_le_of_ne hτ.1 (Ne.symm hend)
      have h5 := (lemma_5).1 n (by omega) τ ω hω hgt
      have hdist := proper_unit_distance_sq n (by omega) τ ω hω
      have hqω : pad ω 0 + pad ω 1 = q := by
        apply (eq_div_iff (ne_of_gt hs2)).2
        nlinarith
      rw [hqω] at h5
      have hp0 : pad ω 0 = ω ⟨0, by omega⟩ := by rw [pad, dif_pos (by omega)]
      have hp1 : pad ω 1 = ω ⟨1, by omega⟩ := by rw [pad, dif_pos (by omega)]
      have hp2 : pad ω 2 = ω ⟨2, by omega⟩ := by rw [pad, dif_pos (by omega)]
      have hp3 : pad ω 3 = ω ⟨3, by omega⟩ := by rw [pad, dif_pos (by omega)]
      have hqd : ω ⟨0, by omega⟩ + ω ⟨1, by omega⟩ = q := by
        simpa only [hp0, hp1] using hqω
      have h6d := lemma_6 n hn ω hω.1 (by simpa [hqd] using hq.2.1)
        (by simpa [hqd] using h5.1) (by simpa [hqd] using hcomp)
      have h6 : 0 ≤ q - pad ω 2 - pad ω 3 ∧ q - pad ω 2 - pad ω 3 < 1 / 12 := by
        simpa only [hqd, hp2, hp3] using h6d
      let x : ℝ := q - pad ω 2 - pad ω 3
      have hPhi0 : Phi q 0 = Abound q := by
        simp [Phi, Aq, Bq, Abound] <;> ring
      by_cases hx : x = 0
      · have hKeq : K n ω = Abound q := by
          apply le_antisymm hcomp
          have hh := h5.2
          change Phi q x ≤ K n ω at hh
          rw [hx, hPhi0] at hh
          exact hh
        apply sixProfile_eq_of_interior_equality n hn τ hτ hgt ω hω hKeq
        rw [hqω]
        exact hx
      · have hxpos : 0 < x := lt_of_le_of_ne h6.1 (Ne.symm hx)
        have hstrict := Phi_strict q x hq.2.1 h5.1 hxpos (le_of_lt h6.2)
        have hle : Phi q x ≤ K n ω := h5.2
        linarith
  refine ⟨hmem, ?_, ?_, hval⟩
  · intro ω hω
    rw [hval]
    by_cases hcomp : K n ω ≤ Abound q
    · rw [key ω hω hcomp, hval]
    · exact le_of_lt (lt_of_not_ge hcomp)
  · intro ω hω hKeq
    apply key ω hω
    rw [hKeq, hval]
