-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.lemma_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:34.686954+00:00
-- url     : https://prove2.me/submissions/af6cc64b-4233-406c-8ef8-94d287d73c3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Model
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency
import Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2_operational_core
import Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2_privacy_transfer
import Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2_correctness_transfer
import Theorems.Thm_ITPIRPreproc_MatchVec_private_of_stepPrivate
import Theorems.Thm_ITPIRPreproc_MatchVec_error_of_perRoundCorrect

open scoped ENNReal
open ITPIRPreproc.MatchVec
open ITPIRPreproc.MatchVec.WordRAM

theorem solution :
    ∃ C : ℝ, ∀ (P : ∀ m : ℕ, OCHP (m * m)) (I : OCHPImpl P),
      ∃ S : Scheme, S.WellFormed ∧
        ∀ (m : ℕ) (tB tS tQ tD tA : ℝ) (qLen aLen : ℕ), 8 ≤ m →
          (P m).IsOneCompatibleHint m → I.Efficient m tB tS tQ tD tA qLen aLen →
          ∀ lam : ℕ, 1 ≤ lam →
            PerfectlyPrivate S (m * m) lam ∧
            Correct S (m * m) lam (fun T => (T : ℝ≥0∞) * (7 / 8 : ℝ≥0∞) ^ (8 * (lam + 1))) ∧
            MeetsBudget S (m * m) lam
              { preWork := C * (lam * m * tB + lam * (m * m) * tS)
                preSpace := C * (tB + lam * m * tS)
                online := C * (lam * (qLen + aLen) + Real.log (m * m))
                offline := C * m
                clientWork := C * (lam * m * (tB + tS) + lam * (tQ + tD) + m * Real.log (m * m))
                clientSpace := C * (lam * m * (tB + tS) + lam * (tQ + tD) + m * Real.log (m * m))
                serverWork := C * (lam * tA + m) } := by
  obtain ⟨C, hC⟩ := lemma_4_2_operational_core
  refine ⟨C, ?_⟩
  intro P I
  obtain ⟨S, hWF, hS⟩ := hC P I
  refine ⟨S, hWF, ?_⟩
  intro m tB tS tQ tD tA qLen aLen hm hP hEff lam hlam
  obtain ⟨huniform, hmodel, hbudget⟩ := hS m tB tS tQ tD tA qLen aLen hm hP hEff lam hlam
  refine ⟨private_of_stepPrivate S (m * m) lam (lemma_4_2_privacy_transfer S (m * m) lam huniform),
    error_of_perRoundCorrect S (m * m) lam ((7 / 8 : ℝ≥0∞) ^ (8 * (lam + 1)))
      (lemma_4_2_correctness_transfer S (m * m) lam (8 * (lam + 1)) hmodel), hbudget⟩
