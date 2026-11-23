-- Prove2me | solution 1 for IntegerRootsFN.Main.elementary_candidate_runtime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:53:40.019198+00:00
-- url     : https://prove2.me/submissions/2bf8cc4f-62be-4ddb-b6c3-8ce5e6bb76ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline
import Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_composed_run

set_option autoImplicit false

open IntegerRootsFN.Main

private lemma logTwo_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logTwo x := by
  exact div_nonneg (Real.log_nonneg hx) (Real.log_pos (by norm_num)).le

theorem solution
    (hsearch : ElementarySearchContract) :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        Runs M (polynomialWord f n b)
          (integersWord ([-1, 0, 1] ++ searchCandidates f n b))
          (softBound C k l n b
            ((n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)) := by
  obtain ⟨M, C, hC, k, l, hrun⟩ := elementary_candidate_composed_run hsearch
  refine ⟨M, C, hC, k, l, ?_⟩
  intro n b f hf
  obtain ⟨t, ht, halt⟩ := hrun n b f hf
  refine ⟨t, ?_, halt⟩
  have hd : min n b ≤ n := min_le_left _ _
  have hcast : (((min n b : ℕ) : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hd 1
  have hlog : logTwo (((min n b : ℕ) : ℝ) + 1) ≤ logTwo ((n : ℝ) + 1) := by
    unfold logTwo
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by positivity) hcast) (Real.log_pos (by norm_num)).le
  have hLd : 0 ≤ 1 + logTwo (((min n b : ℕ) : ℝ) + 1) := by
    have hnonneg : 0 ≤ logTwo (((min n b : ℕ) : ℝ) + 1) := by
      apply logTwo_nonneg_of_one_le
      have : (0 : ℝ) ≤ ((min n b : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  have hpow : (1 + logTwo (((min n b : ℕ) : ℝ) + 1)) ^ k ≤
      (1 + logTwo ((n : ℝ) + 1)) ^ k := by
    exact pow_le_pow_left₀ hLd (add_le_add_right hlog 1) k
  have hsecond :
      softBound C k l (min n b) b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) ≤
      softBound C k l n b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) := by
    unfold softBound
    have hfactor : C * ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) *
        (1 + logTwo (((min n b : ℕ) : ℝ) + 1)) ^ k ≤
        C * ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) *
        (1 + logTwo ((n : ℝ) + 1)) ^ k := by
      gcongr
    have hLb : 0 ≤ (1 + logTwo ((b : ℝ) + 1)) ^ l := by
      apply pow_nonneg
      have hnonneg : 0 ≤ logTwo ((b : ℝ) + 1) := by
        apply logTwo_nonneg_of_one_le
        have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    exact mul_le_mul_of_nonneg_right hfactor hLb
  calc
    (t : ℝ) ≤ softBound C k l n b ((n : ℝ) * b) +
        softBound C k l (min n b) b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) := ht
    _ ≤ softBound C k l n b ((n : ℝ) * b) +
        softBound C k l n b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) :=
      add_le_add le_rfl hsecond
    _ = softBound C k l n b
        ((n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) := by
      unfold softBound
      ring
