-- Prove2me | solution 1 for IntegerRootsFN.Main.candidate_filtering_machine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:25.955788+00:00
-- url     : https://prove2.me/submissions/6e58cce7-ba96-43ee-8ddd-f333a8843465
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline
import Theorems.Thm_IntegerRootsFN_Main_candidate_filtering_composed_run

set_option autoImplicit false

open IntegerRootsFN.Main

theorem solution
    (F : ℕ → ℕ → ℝ)
    (hscale : ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → (n : ℝ) * b ≤ F n b)
    (heval : MultipointEvaluationContract)
    (hgen : CandidateAlgorithm F) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        RootRuns A f n b (softBound C k l n b (F n b)) := by
  obtain ⟨A, C, hC, k, l, Kcard, Ksize, hA⟩ :=
    candidate_filtering_composed_run F heval hgen
  refine ⟨A, C * ((Ksize : ℝ) + 2), by positivity, k, l, ?_⟩
  intro n b f hf
  obtain ⟨cs, hcov, hlen, hsize, t, ht, halt⟩ := hA n b f hf
  refine ⟨((cs.filter fun c => f.eval c = 0).dedup), ?_, t, ht.trans ?_, halt⟩
  · constructor
    · exact List.nodup_dedup _
    · intro r
      simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro hr
        exact ⟨hcov r hr, hr⟩
  · have hn : 0 ≤ (n : ℝ) := by positivity
    have hb : 0 ≤ (b : ℝ) := by positivity
    have hK : 0 ≤ (Ksize : ℝ) := by positivity
    have hnb : (n : ℝ) * b ≤ F n b := hscale n b hf.1 hf.2.1
    have hF : 0 ≤ F n b := le_trans (mul_nonneg hn hb) hnb
    have hsizeR : (pointSize cs : ℝ) ≤ ((Ksize * b : ℕ) : ℝ) := by
      exact_mod_cast hsize
    have hnS : (n : ℝ) * (pointSize cs : ℝ) ≤ (Ksize : ℝ) * F n b := by
      calc
        (n : ℝ) * (pointSize cs : ℝ) ≤ (n : ℝ) * ((Ksize * b : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsizeR hn
        _ = (Ksize : ℝ) * ((n : ℝ) * b) := by push_cast; ring
        _ ≤ (Ksize : ℝ) * F n b := mul_le_mul_of_nonneg_left hnb hK
    have hlogn : 0 ≤ logTwo ((n : ℝ) + 1) := by
      unfold logTwo
      exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
    have hlogb : 0 ≤ logTwo ((b : ℝ) + 1) := by
      unfold logTwo
      exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
    have hPn : 0 ≤ (1 + logTwo ((n : ℝ) + 1)) ^ k := by positivity
    have hPl : 0 ≤ (1 + logTwo ((b : ℝ) + 1)) ^ l := by positivity
    have henvelope : F n b + (n : ℝ) * b + n * (pointSize cs : ℝ) ≤
        ((Ksize : ℝ) + 2) * F n b := by
      nlinarith
    unfold softBound at ht ⊢
    calc
      C * (F n b + (n : ℝ) * b + n * (pointSize cs : ℝ)) *
          (1 + logTwo ((n : ℝ) + 1)) ^ k * (1 + logTwo ((b : ℝ) + 1)) ^ l
        ≤ C * (((Ksize : ℝ) + 2) * F n b) *
          (1 + logTwo ((n : ℝ) + 1)) ^ k * (1 + logTwo ((b : ℝ) + 1)) ^ l := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left henvelope (le_of_lt hC)) hPn) hPl
      _ = C * ((Ksize : ℝ) + 2) * F n b *
          (1 + logTwo ((n : ℝ) + 1)) ^ k * (1 + logTwo ((b : ℝ) + 1)) ^ l := by ring
