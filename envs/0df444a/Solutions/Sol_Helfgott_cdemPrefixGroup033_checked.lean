-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup033_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:58.823996+00:00
-- url     : https://prove2.me/submissions/a0fbed5c-e672-4a47-9f50-499ba1814450

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace Helfgott
private theorem cdemPrefixStats_135168_135232 :
    (∑ n ∈ Ico 135168 135232, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 135168 135232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 135168 135232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (184881 : ℤ) ∧
    (∑ n ∈ Ico 135168 135232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3697688863402801106031427598 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135232_135296 :
    (∑ n ∈ Ico 135232 135296, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 135232 135296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 135232 135296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147869 : ℤ) ∧
    (∑ n ∈ Ico 135232 135296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2957409530306331228188788229 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135168_135296 :
    (∑ n ∈ Ico 135168 135296, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 135168 135296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 135168 135296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (37012 : ℤ) ∧
    (∑ n ∈ Ico 135168 135296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (740279333096469877842639369 : ℤ) := by
  rcases cdemPrefixStats_135168_135232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135232_135296 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135168 ≤ 135232) (by norm_num : 135232 ≤ 135296), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135168 ≤ 135232) (by norm_num : 135232 ≤ 135296), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135232) (by norm_num : 135232 ≤ 135296), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135232) (by norm_num : 135232 ≤ 135296), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135296_135360 :
    (∑ n ∈ Ico 135296 135360, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 135296 135360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135296 135360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36968 : ℤ) ∧
    (∑ n ∈ Ico 135296 135360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (739333204919047380974793742 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135360_135424 :
    (∑ n ∈ Ico 135360 135424, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 135360 135424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135360 135424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (184620 : ℤ) ∧
    (∑ n ∈ Ico 135360 135424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3692385871323011885381134237 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135296_135424 :
    (∑ n ∈ Ico 135296 135424, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 135296 135424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 135296 135424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (221588 : ℤ) ∧
    (∑ n ∈ Ico 135296 135424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4431719076242059266355927979 : ℤ) := by
  rcases cdemPrefixStats_135296_135360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135360_135424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135296 ≤ 135360) (by norm_num : 135360 ≤ 135424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135296 ≤ 135360) (by norm_num : 135360 ≤ 135424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135296 ≤ 135360) (by norm_num : 135360 ≤ 135424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135296 ≤ 135360) (by norm_num : 135360 ≤ 135424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135168_135424 :
    (∑ n ∈ Ico 135168 135424, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 135168 135424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 135168 135424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (258600 : ℤ) ∧
    (∑ n ∈ Ico 135168 135424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5171998409338529144198567348 : ℤ) := by
  rcases cdemPrefixStats_135168_135296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135296_135424 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135168 ≤ 135296) (by norm_num : 135296 ≤ 135424), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135168 ≤ 135296) (by norm_num : 135296 ≤ 135424), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135296) (by norm_num : 135296 ≤ 135424), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135296) (by norm_num : 135296 ≤ 135424), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135424_135488 :
    (∑ n ∈ Ico 135424 135488, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 135424 135488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 135424 135488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-442985 : ℤ) ∧
    (∑ n ∈ Ico 135424 135488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8859772084656811345157007197 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135488_135552 :
    (∑ n ∈ Ico 135488 135552, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 135488 135552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 135488 135552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (184428 : ℤ) ∧
    (∑ n ∈ Ico 135488 135552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3688659309933101648504741930 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135424_135552 :
    (∑ n ∈ Ico 135424 135552, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 135424 135552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 135424 135552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258557 : ℤ) ∧
    (∑ n ∈ Ico 135424 135552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5171112774723709696652265267 : ℤ) := by
  rcases cdemPrefixStats_135424_135488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135488_135552 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135424 ≤ 135488) (by norm_num : 135488 ≤ 135552), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135424 ≤ 135488) (by norm_num : 135488 ≤ 135552), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135424 ≤ 135488) (by norm_num : 135488 ≤ 135552), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135424 ≤ 135488) (by norm_num : 135488 ≤ 135552), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135552_135616 :
    (∑ n ∈ Ico 135552 135616, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 135552 135616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 135552 135616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36831 : ℤ) ∧
    (∑ n ∈ Ico 135552 135616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-736641625791789408679108160 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135616_135680 :
    (∑ n ∈ Ico 135616 135680, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 135616 135680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135616 135680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-405425 : ℤ) ∧
    (∑ n ∈ Ico 135616 135680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8108615308312119139955767823 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135552_135680 :
    (∑ n ∈ Ico 135552 135680, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 135552 135680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 135552 135680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-442256 : ℤ) ∧
    (∑ n ∈ Ico 135552 135680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8845256934103908548634875983 : ℤ) := by
  rcases cdemPrefixStats_135552_135616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135616_135680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135552 ≤ 135616) (by norm_num : 135616 ≤ 135680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135552 ≤ 135616) (by norm_num : 135616 ≤ 135680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135552 ≤ 135616) (by norm_num : 135616 ≤ 135680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135552 ≤ 135616) (by norm_num : 135616 ≤ 135680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135424_135680 :
    (∑ n ∈ Ico 135424 135680, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 135424 135680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 135424 135680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-700813 : ℤ) ∧
    (∑ n ∈ Ico 135424 135680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14016369708827618245287141250 : ℤ) := by
  rcases cdemPrefixStats_135424_135552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135552_135680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135424 ≤ 135552) (by norm_num : 135552 ≤ 135680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135424 ≤ 135552) (by norm_num : 135552 ≤ 135680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135424 ≤ 135552) (by norm_num : 135552 ≤ 135680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135424 ≤ 135552) (by norm_num : 135552 ≤ 135680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135168_135680 :
    (∑ n ∈ Ico 135168 135680, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 135168 135680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 135168 135680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-442213 : ℤ) ∧
    (∑ n ∈ Ico 135168 135680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8844371299489089101088573902 : ℤ) := by
  rcases cdemPrefixStats_135168_135424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135424_135680 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135168 ≤ 135424) (by norm_num : 135424 ≤ 135680), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135168 ≤ 135424) (by norm_num : 135424 ≤ 135680), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135424) (by norm_num : 135424 ≤ 135680), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135424) (by norm_num : 135424 ≤ 135680), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135680_135744 :
    (∑ n ∈ Ico 135680 135744, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 135680 135744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135680 135744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36868 : ℤ) ∧
    (∑ n ∈ Ico 135680 135744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (737408310398167993445479331 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135744_135808 :
    (∑ n ∈ Ico 135744 135808, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 135744 135808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 135744 135808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 135744 135808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-547893934683355351717977 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135680_135808 :
    (∑ n ∈ Ico 135680 135808, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 135680 135808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 135680 135808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36842 : ℤ) ∧
    (∑ n ∈ Ico 135680 135808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (736860416463484638093761354 : ℤ) := by
  rcases cdemPrefixStats_135680_135744 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135744_135808 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135680 ≤ 135744) (by norm_num : 135744 ≤ 135808), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135680 ≤ 135744) (by norm_num : 135744 ≤ 135808), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135680 ≤ 135744) (by norm_num : 135744 ≤ 135808), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135680 ≤ 135744) (by norm_num : 135744 ≤ 135808), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135808_135872 :
    (∑ n ∈ Ico 135808 135872, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 135808 135872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 135808 135872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147251 : ℤ) ∧
    (∑ n ∈ Ico 135808 135872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2945128438627969340194439641 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135872_135936 :
    (∑ n ∈ Ico 135872 135936, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 135872 135936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 135872 135936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-110350 : ℤ) ∧
    (∑ n ∈ Ico 135872 135936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2207039901333181372436042925 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135808_135936 :
    (∑ n ∈ Ico 135808 135936, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 135808 135936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 135808 135936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-257601 : ℤ) ∧
    (∑ n ∈ Ico 135808 135936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5152168339961150712630482566 : ℤ) := by
  rcases cdemPrefixStats_135808_135872 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135872_135936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135808 ≤ 135872) (by norm_num : 135872 ≤ 135936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135808 ≤ 135872) (by norm_num : 135872 ≤ 135936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135808 ≤ 135872) (by norm_num : 135872 ≤ 135936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135808 ≤ 135872) (by norm_num : 135872 ≤ 135936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135680_135936 :
    (∑ n ∈ Ico 135680 135936, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 135680 135936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 135680 135936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220759 : ℤ) ∧
    (∑ n ∈ Ico 135680 135936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4415307923497666074536721212 : ℤ) := by
  rcases cdemPrefixStats_135680_135808 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135808_135936 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135680 ≤ 135808) (by norm_num : 135808 ≤ 135936), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135680 ≤ 135808) (by norm_num : 135808 ≤ 135936), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135680 ≤ 135808) (by norm_num : 135808 ≤ 135936), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135680 ≤ 135808) (by norm_num : 135808 ≤ 135936), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135936_136000 :
    (∑ n ∈ Ico 135936 136000, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 135936 136000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 135936 136000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183886 : ℤ) ∧
    (∑ n ∈ Ico 135936 136000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3677768606092051903296360846 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136000_136064 :
    (∑ n ∈ Ico 136000 136064, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 136000 136064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 136000 136064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146997 : ℤ) ∧
    (∑ n ∈ Ico 136000 136064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2939960365280341123427374917 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_135936_136064 :
    (∑ n ∈ Ico 135936 136064, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 135936 136064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 135936 136064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36889 : ℤ) ∧
    (∑ n ∈ Ico 135936 136064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (737808240811710779868985929 : ℤ) := by
  rcases cdemPrefixStats_135936_136000 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136000_136064 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135936 ≤ 136000) (by norm_num : 136000 ≤ 136064), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135936 ≤ 136000) (by norm_num : 136000 ≤ 136064), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135936 ≤ 136000) (by norm_num : 136000 ≤ 136064), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135936 ≤ 136000) (by norm_num : 136000 ≤ 136064), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136064_136128 :
    (∑ n ∈ Ico 136064 136128, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 136064 136128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 136064 136128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-146965 : ℤ) ∧
    (∑ n ∈ Ico 136064 136128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2939404199762103699900955780 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136128_136192 :
    (∑ n ∈ Ico 136128 136192, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 136128 136192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 136128 136192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-220320 : ℤ) ∧
    (∑ n ∈ Ico 136128 136192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4406456591142547424441826077 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136064_136192 :
    (∑ n ∈ Ico 136064 136192, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 136064 136192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 136064 136192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-367285 : ℤ) ∧
    (∑ n ∈ Ico 136064 136192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7345860790904651124342781857 : ℤ) := by
  rcases cdemPrefixStats_136064_136128 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136128_136192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136064 ≤ 136128) (by norm_num : 136128 ≤ 136192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136064 ≤ 136128) (by norm_num : 136128 ≤ 136192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136064 ≤ 136128) (by norm_num : 136128 ≤ 136192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136064 ≤ 136128) (by norm_num : 136128 ≤ 136192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135936_136192 :
    (∑ n ∈ Ico 135936 136192, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 135936 136192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 135936 136192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-330396 : ℤ) ∧
    (∑ n ∈ Ico 135936 136192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6608052550092940344473795928 : ℤ) := by
  rcases cdemPrefixStats_135936_136064 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136064_136192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135936 ≤ 136064) (by norm_num : 136064 ≤ 136192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135936 ≤ 136064) (by norm_num : 136064 ≤ 136192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135936 ≤ 136064) (by norm_num : 136064 ≤ 136192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135936 ≤ 136064) (by norm_num : 136064 ≤ 136192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135680_136192 :
    (∑ n ∈ Ico 135680 136192, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 135680 136192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 135680 136192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-551155 : ℤ) ∧
    (∑ n ∈ Ico 135680 136192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11023360473590606419010517140 : ℤ) := by
  rcases cdemPrefixStats_135680_135936 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135936_136192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135680 ≤ 135936) (by norm_num : 135936 ≤ 136192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135680 ≤ 135936) (by norm_num : 135936 ≤ 136192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135680 ≤ 135936) (by norm_num : 135936 ≤ 136192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135680 ≤ 135936) (by norm_num : 135936 ≤ 136192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135168_136192 :
    (∑ n ∈ Ico 135168 136192, mobiusTreeValue 16 mobiusTable1200001 n) = (-27 : ℤ) ∧
    (∑ n ∈ Ico 135168 136192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 135168 136192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-993368 : ℤ) ∧
    (∑ n ∈ Ico 135168 136192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19867731773079695520099091042 : ℤ) := by
  rcases cdemPrefixStats_135168_135680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_135680_136192 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135168 ≤ 135680) (by norm_num : 135680 ≤ 136192), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135168 ≤ 135680) (by norm_num : 135680 ≤ 136192), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135680) (by norm_num : 135680 ≤ 136192), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 135680) (by norm_num : 135680 ≤ 136192), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136192_136256 :
    (∑ n ∈ Ico 136192 136256, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 136192 136256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 136192 136256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (220248 : ℤ) ∧
    (∑ n ∈ Ico 136192 136256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4405022169162318845383831830 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136256_136320 :
    (∑ n ∈ Ico 136256 136320, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 136256 136320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 136256 136320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36721 : ℤ) ∧
    (∑ n ∈ Ico 136256 136320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-734461848973517181339281353 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136192_136320 :
    (∑ n ∈ Ico 136192 136320, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 136192 136320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 136192 136320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (183527 : ℤ) ∧
    (∑ n ∈ Ico 136192 136320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3670560320188801664044550477 : ℤ) := by
  rcases cdemPrefixStats_136192_136256 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136256_136320 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136192 ≤ 136256) (by norm_num : 136256 ≤ 136320), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136192 ≤ 136256) (by norm_num : 136256 ≤ 136320), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136256) (by norm_num : 136256 ≤ 136320), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136256) (by norm_num : 136256 ≤ 136320), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136320_136384 :
    (∑ n ∈ Ico 136320 136384, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 136320 136384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 136320 136384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-330006 : ℤ) ∧
    (∑ n ∈ Ico 136320 136384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6600154532193087787865298899 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136384_136448 :
    (∑ n ∈ Ico 136384 136448, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 136384 136448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 136384 136448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-219915 : ℤ) ∧
    (∑ n ∈ Ico 136384 136448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4398289679360263922425955872 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136320_136448 :
    (∑ n ∈ Ico 136320 136448, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 136320 136448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 136320 136448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-549921 : ℤ) ∧
    (∑ n ∈ Ico 136320 136448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10998444211553351710291254771 : ℤ) := by
  rcases cdemPrefixStats_136320_136384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136384_136448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136320 ≤ 136384) (by norm_num : 136384 ≤ 136448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136320 ≤ 136384) (by norm_num : 136384 ≤ 136448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136320 ≤ 136384) (by norm_num : 136384 ≤ 136448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136320 ≤ 136384) (by norm_num : 136384 ≤ 136448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136192_136448 :
    (∑ n ∈ Ico 136192 136448, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 136192 136448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (160 : ℕ) ∧
    (∑ n ∈ Ico 136192 136448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-366394 : ℤ) ∧
    (∑ n ∈ Ico 136192 136448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7327883891364550046246704294 : ℤ) := by
  rcases cdemPrefixStats_136192_136320 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136320_136448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136192 ≤ 136320) (by norm_num : 136320 ≤ 136448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136192 ≤ 136320) (by norm_num : 136320 ≤ 136448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136320) (by norm_num : 136320 ≤ 136448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136320) (by norm_num : 136320 ≤ 136448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136448_136512 :
    (∑ n ∈ Ico 136448 136512, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 136448 136512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 136448 136512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109890 : ℤ) ∧
    (∑ n ∈ Ico 136448 136512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2197845220483139258875436377 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136512_136576 :
    (∑ n ∈ Ico 136512 136576, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 136512 136576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 136512 136576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (73238 : ℤ) ∧
    (∑ n ∈ Ico 136512 136576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1464750920603610476589252116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136448_136576 :
    (∑ n ∈ Ico 136448 136576, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 136448 136576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 136448 136576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36652 : ℤ) ∧
    (∑ n ∈ Ico 136448 136576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-733094299879528782286184261 : ℤ) := by
  rcases cdemPrefixStats_136448_136512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136512_136576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136448 ≤ 136512) (by norm_num : 136512 ≤ 136576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136448 ≤ 136512) (by norm_num : 136512 ≤ 136576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136448 ≤ 136512) (by norm_num : 136512 ≤ 136576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136448 ≤ 136512) (by norm_num : 136512 ≤ 136576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136576_136640 :
    (∑ n ∈ Ico 136576 136640, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 136576 136640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 136576 136640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109851 : ℤ) ∧
    (∑ n ∈ Ico 136576 136640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2197023893825508513560008473 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136640_136704 :
    (∑ n ∈ Ico 136640 136704, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 136640 136704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 136640 136704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36561 : ℤ) ∧
    (∑ n ∈ Ico 136640 136704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (731212867603327088197573203 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136576_136704 :
    (∑ n ∈ Ico 136576 136704, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 136576 136704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 136576 136704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-73290 : ℤ) ∧
    (∑ n ∈ Ico 136576 136704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1465811026222181425362435270 : ℤ) := by
  rcases cdemPrefixStats_136576_136640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136640_136704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136576 ≤ 136640) (by norm_num : 136640 ≤ 136704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136576 ≤ 136640) (by norm_num : 136640 ≤ 136704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136576 ≤ 136640) (by norm_num : 136640 ≤ 136704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136576 ≤ 136640) (by norm_num : 136640 ≤ 136704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136448_136704 :
    (∑ n ∈ Ico 136448 136704, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 136448 136704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 136448 136704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109942 : ℤ) ∧
    (∑ n ∈ Ico 136448 136704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2198905326101710207648619531 : ℤ) := by
  rcases cdemPrefixStats_136448_136576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136576_136704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136448 ≤ 136576) (by norm_num : 136576 ≤ 136704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136448 ≤ 136576) (by norm_num : 136576 ≤ 136704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136448 ≤ 136576) (by norm_num : 136576 ≤ 136704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136448 ≤ 136576) (by norm_num : 136576 ≤ 136704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136192_136704 :
    (∑ n ∈ Ico 136192 136704, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 136192 136704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 136192 136704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-476336 : ℤ) ∧
    (∑ n ∈ Ico 136192 136704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9526789217466260253895323825 : ℤ) := by
  rcases cdemPrefixStats_136192_136448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136448_136704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136192 ≤ 136448) (by norm_num : 136448 ≤ 136704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136192 ≤ 136448) (by norm_num : 136448 ≤ 136704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136448) (by norm_num : 136448 ≤ 136704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136448) (by norm_num : 136448 ≤ 136704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136704_136768 :
    (∑ n ∈ Ico 136704 136768, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 136704 136768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 136704 136768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-365705 : ℤ) ∧
    (∑ n ∈ Ico 136704 136768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7314197465101427500574154578 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136768_136832 :
    (∑ n ∈ Ico 136768 136832, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 136768 136832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 136768 136832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109669 : ℤ) ∧
    (∑ n ∈ Ico 136768 136832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2193426009989237770499411843 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136704_136832 :
    (∑ n ∈ Ico 136704 136832, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 136704 136832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 136704 136832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-475374 : ℤ) ∧
    (∑ n ∈ Ico 136704 136832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9507623475090665271073566421 : ℤ) := by
  rcases cdemPrefixStats_136704_136768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136768_136832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136704 ≤ 136768) (by norm_num : 136768 ≤ 136832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136704 ≤ 136768) (by norm_num : 136768 ≤ 136832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136704 ≤ 136768) (by norm_num : 136768 ≤ 136832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136704 ≤ 136768) (by norm_num : 136768 ≤ 136832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136832_136896 :
    (∑ n ∈ Ico 136832 136896, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 136832 136896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 136832 136896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-328814 : ℤ) ∧
    (∑ n ∈ Ico 136832 136896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6576330010846359301508344177 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136896_136960 :
    (∑ n ∈ Ico 136896 136960, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 136896 136960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 136896 136960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-73014 : ℤ) ∧
    (∑ n ∈ Ico 136896 136960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1460237638923499506528754932 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136832_136960 :
    (∑ n ∈ Ico 136832 136960, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 136832 136960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 136832 136960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-401828 : ℤ) ∧
    (∑ n ∈ Ico 136832 136960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8036567649769858808037099109 : ℤ) := by
  rcases cdemPrefixStats_136832_136896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136896_136960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136832 ≤ 136896) (by norm_num : 136896 ≤ 136960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136832 ≤ 136896) (by norm_num : 136896 ≤ 136960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136832 ≤ 136896) (by norm_num : 136896 ≤ 136960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136832 ≤ 136896) (by norm_num : 136896 ≤ 136960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136704_136960 :
    (∑ n ∈ Ico 136704 136960, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 136704 136960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 136704 136960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-877202 : ℤ) ∧
    (∑ n ∈ Ico 136704 136960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17544191124860524079110665530 : ℤ) := by
  rcases cdemPrefixStats_136704_136832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136832_136960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136704 ≤ 136832) (by norm_num : 136832 ≤ 136960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136704 ≤ 136832) (by norm_num : 136832 ≤ 136960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136704 ≤ 136832) (by norm_num : 136832 ≤ 136960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136704 ≤ 136832) (by norm_num : 136832 ≤ 136960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136960_137024 :
    (∑ n ∈ Ico 136960 137024, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 136960 137024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 136960 137024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (291959 : ℤ) ∧
    (∑ n ∈ Ico 136960 137024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5839240397695231642991787381 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137024_137088 :
    (∑ n ∈ Ico 137024 137088, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 137024 137088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 137024 137088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (109458 : ℤ) ∧
    (∑ n ∈ Ico 137024 137088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2189237633864194725304174774 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_136960_137088 :
    (∑ n ∈ Ico 136960 137088, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 136960 137088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 136960 137088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (401417 : ℤ) ∧
    (∑ n ∈ Ico 136960 137088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8028478031559426368295962155 : ℤ) := by
  rcases cdemPrefixStats_136960_137024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137024_137088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136960 ≤ 137024) (by norm_num : 137024 ≤ 137088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136960 ≤ 137024) (by norm_num : 137024 ≤ 137088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136960 ≤ 137024) (by norm_num : 137024 ≤ 137088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136960 ≤ 137024) (by norm_num : 137024 ≤ 137088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137088_137152 :
    (∑ n ∈ Ico 137088 137152, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 137088 137152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 137088 137152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-291714 : ℤ) ∧
    (∑ n ∈ Ico 137088 137152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5834327113860812925224151474 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137152_137216 :
    (∑ n ∈ Ico 137152 137216, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 137152 137216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 137152 137216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-291573 : ℤ) ∧
    (∑ n ∈ Ico 137152 137216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5831541467490859490693772852 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137088_137216 :
    (∑ n ∈ Ico 137088 137216, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 137088 137216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 137088 137216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-583287 : ℤ) ∧
    (∑ n ∈ Ico 137088 137216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11665868581351672415917924326 : ℤ) := by
  rcases cdemPrefixStats_137088_137152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137152_137216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137088 ≤ 137152) (by norm_num : 137152 ≤ 137216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137088 ≤ 137152) (by norm_num : 137152 ≤ 137216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137088 ≤ 137152) (by norm_num : 137152 ≤ 137216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137088 ≤ 137152) (by norm_num : 137152 ≤ 137216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136960_137216 :
    (∑ n ∈ Ico 136960 137216, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 136960 137216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 136960 137216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-181870 : ℤ) ∧
    (∑ n ∈ Ico 136960 137216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3637390549792246047621962171 : ℤ) := by
  rcases cdemPrefixStats_136960_137088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137088_137216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136960 ≤ 137088) (by norm_num : 137088 ≤ 137216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136960 ≤ 137088) (by norm_num : 137088 ≤ 137216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136960 ≤ 137088) (by norm_num : 137088 ≤ 137216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136960 ≤ 137088) (by norm_num : 137088 ≤ 137216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136704_137216 :
    (∑ n ∈ Ico 136704 137216, mobiusTreeValue 16 mobiusTable1200001 n) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 136704 137216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 136704 137216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1059072 : ℤ) ∧
    (∑ n ∈ Ico 136704 137216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21181581674652770126732627701 : ℤ) := by
  rcases cdemPrefixStats_136704_136960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136960_137216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136704 ≤ 136960) (by norm_num : 136960 ≤ 137216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136704 ≤ 136960) (by norm_num : 136960 ≤ 137216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136704 ≤ 136960) (by norm_num : 136960 ≤ 137216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136704 ≤ 136960) (by norm_num : 136960 ≤ 137216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_136192_137216 :
    (∑ n ∈ Ico 136192 137216, mobiusTreeValue 16 mobiusTable1200001 n) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 136192 137216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (624 : ℕ) ∧
    (∑ n ∈ Ico 136192 137216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1535408 : ℤ) ∧
    (∑ n ∈ Ico 136192 137216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30708370892119030380627951526 : ℤ) := by
  rcases cdemPrefixStats_136192_136704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136704_137216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 136192 ≤ 136704) (by norm_num : 136704 ≤ 137216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 136192 ≤ 136704) (by norm_num : 136704 ≤ 137216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136704) (by norm_num : 136704 ≤ 137216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 136192 ≤ 136704) (by norm_num : 136704 ≤ 137216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135168_137216 :
    (∑ n ∈ Ico 135168 137216, mobiusTreeValue 16 mobiusTable1200001 n) = (-69 : ℤ) ∧
    (∑ n ∈ Ico 135168 137216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 135168 137216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2528776 : ℤ) ∧
    (∑ n ∈ Ico 135168 137216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-50576102665198725900727042568 : ℤ) := by
  rcases cdemPrefixStats_135168_136192 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_136192_137216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135168 ≤ 136192) (by norm_num : 136192 ≤ 137216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135168 ≤ 136192) (by norm_num : 136192 ≤ 137216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 136192) (by norm_num : 136192 ≤ 137216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 136192) (by norm_num : 136192 ≤ 137216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137216_137280 :
    (∑ n ∈ Ico 137216 137280, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 137216 137280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 137216 137280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (72845 : ℤ) ∧
    (∑ n ∈ Ico 137216 137280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1456902972796734463369745979 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137280_137344 :
    (∑ n ∈ Ico 137280 137344, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 137280 137344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 137280 137344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-182097 : ℤ) ∧
    (∑ n ∈ Ico 137280 137344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3641952379896211856637747057 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137216_137344 :
    (∑ n ∈ Ico 137216 137344, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 137216 137344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 137216 137344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-109252 : ℤ) ∧
    (∑ n ∈ Ico 137216 137344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2185049407099477393268001078 : ℤ) := by
  rcases cdemPrefixStats_137216_137280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137280_137344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137216 ≤ 137280) (by norm_num : 137280 ≤ 137344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137216 ≤ 137280) (by norm_num : 137280 ≤ 137344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137280) (by norm_num : 137280 ≤ 137344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137280) (by norm_num : 137280 ≤ 137344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137344_137408 :
    (∑ n ∈ Ico 137344 137408, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 137344 137408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 137344 137408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-145613 : ℤ) ∧
    (∑ n ∈ Ico 137344 137408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2912273094812124753139602120 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137408_137472 :
    (∑ n ∈ Ico 137408 137472, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 137408 137472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 137408 137472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-254708 : ℤ) ∧
    (∑ n ∈ Ico 137408 137472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5094222162629348683705465511 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137344_137472 :
    (∑ n ∈ Ico 137344 137472, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 137344 137472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 137344 137472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-400321 : ℤ) ∧
    (∑ n ∈ Ico 137344 137472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8006495257441473436845067631 : ℤ) := by
  rcases cdemPrefixStats_137344_137408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137408_137472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137344 ≤ 137408) (by norm_num : 137408 ≤ 137472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137344 ≤ 137408) (by norm_num : 137408 ≤ 137472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137344 ≤ 137408) (by norm_num : 137408 ≤ 137472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137344 ≤ 137408) (by norm_num : 137408 ≤ 137472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137216_137472 :
    (∑ n ∈ Ico 137216 137472, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 137216 137472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 137216 137472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-509573 : ℤ) ∧
    (∑ n ∈ Ico 137216 137472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10191544664540950830113068709 : ℤ) := by
  rcases cdemPrefixStats_137216_137344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137344_137472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137216 ≤ 137344) (by norm_num : 137344 ≤ 137472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137216 ≤ 137344) (by norm_num : 137344 ≤ 137472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137344) (by norm_num : 137344 ≤ 137472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137344) (by norm_num : 137344 ≤ 137472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137472_137536 :
    (∑ n ∈ Ico 137472 137536, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 137472 137536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 137472 137536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36381 : ℤ) ∧
    (∑ n ∈ Ico 137472 137536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-727669310160644677024153057 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137536_137600 :
    (∑ n ∈ Ico 137536 137600, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 137536 137600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 137536 137600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36284 : ℤ) ∧
    (∑ n ∈ Ico 137536 137600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-725724440758679668055147105 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137472_137600 :
    (∑ n ∈ Ico 137472 137600, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 137472 137600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 137472 137600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-72665 : ℤ) ∧
    (∑ n ∈ Ico 137472 137600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1453393750919324345079300162 : ℤ) := by
  rcases cdemPrefixStats_137472_137536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137536_137600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137472 ≤ 137536) (by norm_num : 137536 ≤ 137600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137472 ≤ 137536) (by norm_num : 137536 ≤ 137600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137472 ≤ 137536) (by norm_num : 137536 ≤ 137600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137472 ≤ 137536) (by norm_num : 137536 ≤ 137600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137600_137664 :
    (∑ n ∈ Ico 137600 137664, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 137600 137664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 137600 137664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36313 : ℤ) ∧
    (∑ n ∈ Ico 137600 137664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-726290221983201509623899574 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137664_137728 :
    (∑ n ∈ Ico 137664 137728, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 137664 137728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 137664 137728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36313 : ℤ) ∧
    (∑ n ∈ Ico 137664 137728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (726274276286357427814775297 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137600_137728 :
    (∑ n ∈ Ico 137600 137728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 137600 137728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 137600 137728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (0 : ℤ) ∧
    (∑ n ∈ Ico 137600 137728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15945696844081809124277 : ℤ) := by
  rcases cdemPrefixStats_137600_137664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137664_137728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137600 ≤ 137664) (by norm_num : 137664 ≤ 137728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137600 ≤ 137664) (by norm_num : 137664 ≤ 137728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137600 ≤ 137664) (by norm_num : 137664 ≤ 137728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137600 ≤ 137664) (by norm_num : 137664 ≤ 137728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137472_137728 :
    (∑ n ∈ Ico 137472 137728, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 137472 137728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 137472 137728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-72665 : ℤ) ∧
    (∑ n ∈ Ico 137472 137728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1453409696616168426888424439 : ℤ) := by
  rcases cdemPrefixStats_137472_137600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137600_137728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137472 ≤ 137600) (by norm_num : 137600 ≤ 137728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137472 ≤ 137600) (by norm_num : 137600 ≤ 137728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137472 ≤ 137600) (by norm_num : 137600 ≤ 137728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137472 ≤ 137600) (by norm_num : 137600 ≤ 137728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137216_137728 :
    (∑ n ∈ Ico 137216 137728, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 137216 137728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 137216 137728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-582238 : ℤ) ∧
    (∑ n ∈ Ico 137216 137728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11644954361157119257001493148 : ℤ) := by
  rcases cdemPrefixStats_137216_137472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137472_137728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137216 ≤ 137472) (by norm_num : 137472 ≤ 137728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137216 ≤ 137472) (by norm_num : 137472 ≤ 137728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137472) (by norm_num : 137472 ≤ 137728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137472) (by norm_num : 137472 ≤ 137728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137728_137792 :
    (∑ n ∈ Ico 137728 137792, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 137728 137792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 137728 137792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36298 : ℤ) ∧
    (∑ n ∈ Ico 137728 137792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-726005591305614709887220174 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137792_137856 :
    (∑ n ∈ Ico 137792 137856, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 137792 137856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 137792 137856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-72509 : ℤ) ∧
    (∑ n ∈ Ico 137792 137856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1450204799533032260831112510 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137728_137856 :
    (∑ n ∈ Ico 137728 137856, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 137728 137856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 137728 137856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108807 : ℤ) ∧
    (∑ n ∈ Ico 137728 137856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2176210390838646970718332684 : ℤ) := by
  rcases cdemPrefixStats_137728_137792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137792_137856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137728 ≤ 137792) (by norm_num : 137792 ≤ 137856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137728 ≤ 137792) (by norm_num : 137792 ≤ 137856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137728 ≤ 137792) (by norm_num : 137792 ≤ 137856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137728 ≤ 137792) (by norm_num : 137792 ≤ 137856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137856_137920 :
    (∑ n ∈ Ico 137856 137920, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 137856 137920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 137856 137920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (253842 : ℤ) ∧
    (∑ n ∈ Ico 137856 137920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5076904729625193664203790372 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137920_137984 :
    (∑ n ∈ Ico 137920 137984, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 137920 137984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 137920 137984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108685 : ℤ) ∧
    (∑ n ∈ Ico 137920 137984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2173734078031189328522383438 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137856_137984 :
    (∑ n ∈ Ico 137856 137984, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 137856 137984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 137856 137984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145157 : ℤ) ∧
    (∑ n ∈ Ico 137856 137984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2903170651594004335681406934 : ℤ) := by
  rcases cdemPrefixStats_137856_137920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137920_137984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137856 ≤ 137920) (by norm_num : 137920 ≤ 137984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137856 ≤ 137920) (by norm_num : 137920 ≤ 137984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137856 ≤ 137920) (by norm_num : 137920 ≤ 137984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137856 ≤ 137920) (by norm_num : 137920 ≤ 137984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137728_137984 :
    (∑ n ∈ Ico 137728 137984, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 137728 137984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 137728 137984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (36350 : ℤ) ∧
    (∑ n ∈ Ico 137728 137984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (726960260755357364963074250 : ℤ) := by
  rcases cdemPrefixStats_137728_137856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137856_137984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137728 ≤ 137856) (by norm_num : 137856 ≤ 137984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137728 ≤ 137856) (by norm_num : 137856 ≤ 137984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137728 ≤ 137856) (by norm_num : 137856 ≤ 137984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137728 ≤ 137856) (by norm_num : 137856 ≤ 137984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137984_138048 :
    (∑ n ∈ Ico 137984 138048, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 137984 138048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 137984 138048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144897 : ℤ) ∧
    (∑ n ∈ Ico 137984 138048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2897941762965326839900515188 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138048_138112 :
    (∑ n ∈ Ico 138048 138112, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 138048 138112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 138048 138112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144814 : ℤ) ∧
    (∑ n ∈ Ico 138048 138112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2896394197655649897357335862 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_137984_138112 :
    (∑ n ∈ Ico 137984 138112, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 137984 138112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 137984 138112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289711 : ℤ) ∧
    (∑ n ∈ Ico 137984 138112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5794335960620976737257851050 : ℤ) := by
  rcases cdemPrefixStats_137984_138048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138048_138112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137984 ≤ 138048) (by norm_num : 138048 ≤ 138112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137984 ≤ 138048) (by norm_num : 138048 ≤ 138112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137984 ≤ 138048) (by norm_num : 138048 ≤ 138112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137984 ≤ 138048) (by norm_num : 138048 ≤ 138112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138112_138176 :
    (∑ n ∈ Ico 138112 138176, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 138112 138176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 138112 138176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (108535 : ℤ) ∧
    (∑ n ∈ Ico 138112 138176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2170745717328079501768966396 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138176_138240 :
    (∑ n ∈ Ico 138176 138240, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 138176 138240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 138176 138240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108609 : ℤ) ∧
    (∑ n ∈ Ico 138176 138240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2172170068152071747465086014 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138112_138240 :
    (∑ n ∈ Ico 138112 138240, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 138112 138240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 138112 138240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-74 : ℤ) ∧
    (∑ n ∈ Ico 138112 138240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1424350823992245696119618 : ℤ) := by
  rcases cdemPrefixStats_138112_138176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138176_138240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138112 ≤ 138176) (by norm_num : 138176 ≤ 138240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138112 ≤ 138176) (by norm_num : 138176 ≤ 138240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138112 ≤ 138176) (by norm_num : 138176 ≤ 138240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138112 ≤ 138176) (by norm_num : 138176 ≤ 138240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137984_138240 :
    (∑ n ∈ Ico 137984 138240, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 137984 138240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 137984 138240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289785 : ℤ) ∧
    (∑ n ∈ Ico 137984 138240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5795760311444968982953970668 : ℤ) := by
  rcases cdemPrefixStats_137984_138112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138112_138240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137984 ≤ 138112) (by norm_num : 138112 ≤ 138240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137984 ≤ 138112) (by norm_num : 138112 ≤ 138240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137984 ≤ 138112) (by norm_num : 138112 ≤ 138240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137984 ≤ 138112) (by norm_num : 138112 ≤ 138240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137728_138240 :
    (∑ n ∈ Ico 137728 138240, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 137728 138240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 137728 138240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-253435 : ℤ) ∧
    (∑ n ∈ Ico 137728 138240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5068800050689611617990896418 : ℤ) := by
  rcases cdemPrefixStats_137728_137984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137984_138240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137728 ≤ 137984) (by norm_num : 137984 ≤ 138240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137728 ≤ 137984) (by norm_num : 137984 ≤ 138240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137728 ≤ 137984) (by norm_num : 137984 ≤ 138240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137728 ≤ 137984) (by norm_num : 137984 ≤ 138240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137216_138240 :
    (∑ n ∈ Ico 137216 138240, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 137216 138240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 137216 138240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-835673 : ℤ) ∧
    (∑ n ∈ Ico 137216 138240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-16713754411846730874992389566 : ℤ) := by
  rcases cdemPrefixStats_137216_137728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137728_138240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137216 ≤ 137728) (by norm_num : 137728 ≤ 138240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137216 ≤ 137728) (by norm_num : 137728 ≤ 138240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137728) (by norm_num : 137728 ≤ 138240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 137728) (by norm_num : 137728 ≤ 138240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138240_138304 :
    (∑ n ∈ Ico 138240 138304, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 138240 138304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 138240 138304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 138240 138304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-204039813856547034681914 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138304_138368 :
    (∑ n ∈ Ico 138304 138368, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 138304 138368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 138304 138368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36179 : ℤ) ∧
    (∑ n ∈ Ico 138304 138368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-723614463525663884545172614 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138240_138368 :
    (∑ n ∈ Ico 138240 138368, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 138240 138368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 138240 138368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36191 : ℤ) ∧
    (∑ n ∈ Ico 138240 138368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-723818503339520431579854528 : ℤ) := by
  rcases cdemPrefixStats_138240_138304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138304_138368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138240 ≤ 138304) (by norm_num : 138304 ≤ 138368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138240 ≤ 138304) (by norm_num : 138304 ≤ 138368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138304) (by norm_num : 138304 ≤ 138368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138304) (by norm_num : 138304 ≤ 138368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138368_138432 :
    (∑ n ∈ Ico 138368 138432, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 138368 138432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 138368 138432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252908 : ℤ) ∧
    (∑ n ∈ Ico 138368 138432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5058242016948894835644923597 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138432_138496 :
    (∑ n ∈ Ico 138432 138496, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 138432 138496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 138432 138496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (108311 : ℤ) ∧
    (∑ n ∈ Ico 138432 138496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2166346558689099149268993737 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138368_138496 :
    (∑ n ∈ Ico 138368 138496, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 138368 138496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (82 : ℕ) ∧
    (∑ n ∈ Ico 138368 138496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144597 : ℤ) ∧
    (∑ n ∈ Ico 138368 138496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2891895458259795686375929860 : ℤ) := by
  rcases cdemPrefixStats_138368_138432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138432_138496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138368 ≤ 138432) (by norm_num : 138432 ≤ 138496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138368 ≤ 138432) (by norm_num : 138432 ≤ 138496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138368 ≤ 138432) (by norm_num : 138432 ≤ 138496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138368 ≤ 138432) (by norm_num : 138432 ≤ 138496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138240_138496 :
    (∑ n ∈ Ico 138240 138496, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 138240 138496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 138240 138496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-180788 : ℤ) ∧
    (∑ n ∈ Ico 138240 138496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3615713961599316117955784388 : ℤ) := by
  rcases cdemPrefixStats_138240_138368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138368_138496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138240 ≤ 138368) (by norm_num : 138368 ≤ 138496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138240 ≤ 138368) (by norm_num : 138368 ≤ 138496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138368) (by norm_num : 138368 ≤ 138496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138368) (by norm_num : 138368 ≤ 138496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138496_138560 :
    (∑ n ∈ Ico 138496 138560, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 138496 138560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 138496 138560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (108275 : ℤ) ∧
    (∑ n ∈ Ico 138496 138560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2165517855207902617440192882 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138560_138624 :
    (∑ n ∈ Ico 138560 138624, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 138560 138624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 138560 138624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-577270 : ℤ) ∧
    (∑ n ∈ Ico 138560 138624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11545641192805999789790558948 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138496_138624 :
    (∑ n ∈ Ico 138496 138624, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 138496 138624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 138496 138624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-468995 : ℤ) ∧
    (∑ n ∈ Ico 138496 138624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9380123337598097172350366066 : ℤ) := by
  rcases cdemPrefixStats_138496_138560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138560_138624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138496 ≤ 138560) (by norm_num : 138560 ≤ 138624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138496 ≤ 138560) (by norm_num : 138560 ≤ 138624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138496 ≤ 138560) (by norm_num : 138560 ≤ 138624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138496 ≤ 138560) (by norm_num : 138560 ≤ 138624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138624_138688 :
    (∑ n ∈ Ico 138624 138688, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 138624 138688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 138624 138688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (72102 : ℤ) ∧
    (∑ n ∈ Ico 138624 138688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1442085832591825287963250739 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138688_138752 :
    (∑ n ∈ Ico 138688 138752, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 138688 138752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 138688 138752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-108131 : ℤ) ∧
    (∑ n ∈ Ico 138688 138752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2162650518837082306992936089 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138624_138752 :
    (∑ n ∈ Ico 138624 138752, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 138624 138752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 138624 138752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-36029 : ℤ) ∧
    (∑ n ∈ Ico 138624 138752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-720564686245257019029685350 : ℤ) := by
  rcases cdemPrefixStats_138624_138688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138688_138752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138624 ≤ 138688) (by norm_num : 138688 ≤ 138752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138624 ≤ 138688) (by norm_num : 138688 ≤ 138752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138624 ≤ 138688) (by norm_num : 138688 ≤ 138752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138624 ≤ 138688) (by norm_num : 138688 ≤ 138752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138496_138752 :
    (∑ n ∈ Ico 138496 138752, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 138496 138752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 138496 138752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-505024 : ℤ) ∧
    (∑ n ∈ Ico 138496 138752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10100688023843354191380051416 : ℤ) := by
  rcases cdemPrefixStats_138496_138624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138624_138752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138496 ≤ 138624) (by norm_num : 138624 ≤ 138752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138496 ≤ 138624) (by norm_num : 138624 ≤ 138752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138496 ≤ 138624) (by norm_num : 138624 ≤ 138752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138496 ≤ 138624) (by norm_num : 138624 ≤ 138752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138240_138752 :
    (∑ n ∈ Ico 138240 138752, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 138240 138752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 138240 138752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-685812 : ℤ) ∧
    (∑ n ∈ Ico 138240 138752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13716401985442670309335835804 : ℤ) := by
  rcases cdemPrefixStats_138240_138496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138496_138752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138240 ≤ 138496) (by norm_num : 138496 ≤ 138752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138240 ≤ 138496) (by norm_num : 138496 ≤ 138752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138496) (by norm_num : 138496 ≤ 138752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138496) (by norm_num : 138496 ≤ 138752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138752_138816 :
    (∑ n ∈ Ico 138752 138816, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 138752 138816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 138752 138816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (180106 : ℤ) ∧
    (∑ n ∈ Ico 138752 138816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3602165349508670003747470319 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138816_138880 :
    (∑ n ∈ Ico 138816 138880, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 138816 138880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 138816 138880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (72011 : ℤ) ∧
    (∑ n ∈ Ico 138816 138880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1440237375684780575282690698 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138752_138880 :
    (∑ n ∈ Ico 138752 138880, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 138752 138880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 138752 138880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (252117 : ℤ) ∧
    (∑ n ∈ Ico 138752 138880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5042402725193450579030161017 : ℤ) := by
  rcases cdemPrefixStats_138752_138816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138816_138880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138752 ≤ 138816) (by norm_num : 138816 ≤ 138880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138752 ≤ 138816) (by norm_num : 138816 ≤ 138880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138752 ≤ 138816) (by norm_num : 138816 ≤ 138880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138752 ≤ 138816) (by norm_num : 138816 ≤ 138880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138880_138944 :
    (∑ n ∈ Ico 138880 138944, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 138880 138944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 138880 138944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107930 : ℤ) ∧
    (∑ n ∈ Ico 138880 138944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2158666456060712000289021112 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138944_139008 :
    (∑ n ∈ Ico 138944 139008, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 138944 139008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 138944 139008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (503680 : ℤ) ∧
    (∑ n ∈ Ico 138944 139008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10073733741988990685160503173 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_138880_139008 :
    (∑ n ∈ Ico 138880 139008, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 138880 139008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 138880 139008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (395750 : ℤ) ∧
    (∑ n ∈ Ico 138880 139008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7915067285928278684871482061 : ℤ) := by
  rcases cdemPrefixStats_138880_138944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138944_139008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138880 ≤ 138944) (by norm_num : 138944 ≤ 139008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138880 ≤ 138944) (by norm_num : 138944 ≤ 139008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138880 ≤ 138944) (by norm_num : 138944 ≤ 139008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138880 ≤ 138944) (by norm_num : 138944 ≤ 139008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138752_139008 :
    (∑ n ∈ Ico 138752 139008, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 138752 139008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 138752 139008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (647867 : ℤ) ∧
    (∑ n ∈ Ico 138752 139008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12957470011121729263901643078 : ℤ) := by
  rcases cdemPrefixStats_138752_138880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138880_139008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138752 ≤ 138880) (by norm_num : 138880 ≤ 139008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138752 ≤ 138880) (by norm_num : 138880 ≤ 139008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138752 ≤ 138880) (by norm_num : 138880 ≤ 139008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138752 ≤ 138880) (by norm_num : 138880 ≤ 139008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139008_139072 :
    (∑ n ∈ Ico 139008 139072, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 139008 139072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 139008 139072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-71929 : ℤ) ∧
    (∑ n ∈ Ico 139008 139072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1438616105160857546481008192 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139072_139136 :
    (∑ n ∈ Ico 139072 139136, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 139072 139136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 139072 139136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-143747 : ℤ) ∧
    (∑ n ∈ Ico 139072 139136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2874967598512520158546217442 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139008_139136 :
    (∑ n ∈ Ico 139008 139136, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 139008 139136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 139008 139136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-215676 : ℤ) ∧
    (∑ n ∈ Ico 139008 139136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4313583703673377705027225634 : ℤ) := by
  rcases cdemPrefixStats_139008_139072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139072_139136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139008 ≤ 139072) (by norm_num : 139072 ≤ 139136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139008 ≤ 139072) (by norm_num : 139072 ≤ 139136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139008 ≤ 139072) (by norm_num : 139072 ≤ 139136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139008 ≤ 139072) (by norm_num : 139072 ≤ 139136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139136_139200 :
    (∑ n ∈ Ico 139136 139200, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 139136 139200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 139136 139200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-71870 : ℤ) ∧
    (∑ n ∈ Ico 139136 139200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1437468195662614543861269011 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139200_139264 :
    (∑ n ∈ Ico 139200 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 139200 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 139200 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (35872 : ℤ) ∧
    (∑ n ∈ Ico 139200 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (717390002700800752746372461 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_139136_139264 :
    (∑ n ∈ Ico 139136 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 139136 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 139136 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-35998 : ℤ) ∧
    (∑ n ∈ Ico 139136 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-720078192961813791114896550 : ℤ) := by
  rcases cdemPrefixStats_139136_139200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139200_139264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139136 ≤ 139200) (by norm_num : 139200 ≤ 139264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139136 ≤ 139200) (by norm_num : 139200 ≤ 139264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139136 ≤ 139200) (by norm_num : 139200 ≤ 139264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139136 ≤ 139200) (by norm_num : 139200 ≤ 139264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_139008_139264 :
    (∑ n ∈ Ico 139008 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 139008 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 139008 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-251674 : ℤ) ∧
    (∑ n ∈ Ico 139008 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5033661896635191496142122184 : ℤ) := by
  rcases cdemPrefixStats_139008_139136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139136_139264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 139008 ≤ 139136) (by norm_num : 139136 ≤ 139264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 139008 ≤ 139136) (by norm_num : 139136 ≤ 139264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 139008 ≤ 139136) (by norm_num : 139136 ≤ 139264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 139008 ≤ 139136) (by norm_num : 139136 ≤ 139264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138752_139264 :
    (∑ n ∈ Ico 138752 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 138752 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 138752 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (396193 : ℤ) ∧
    (∑ n ∈ Ico 138752 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7923808114486537767759520894 : ℤ) := by
  rcases cdemPrefixStats_138752_139008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_139008_139264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138752 ≤ 139008) (by norm_num : 139008 ≤ 139264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138752 ≤ 139008) (by norm_num : 139008 ≤ 139264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138752 ≤ 139008) (by norm_num : 139008 ≤ 139264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138752 ≤ 139008) (by norm_num : 139008 ≤ 139264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_138240_139264 :
    (∑ n ∈ Ico 138240 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 138240 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 138240 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-289619 : ℤ) ∧
    (∑ n ∈ Ico 138240 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5792593870956132541576314910 : ℤ) := by
  rcases cdemPrefixStats_138240_138752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138752_139264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 138240 ≤ 138752) (by norm_num : 138752 ≤ 139264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 138240 ≤ 138752) (by norm_num : 138752 ≤ 139264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138752) (by norm_num : 138752 ≤ 139264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 138240 ≤ 138752) (by norm_num : 138752 ≤ 139264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_137216_139264 :
    (∑ n ∈ Ico 137216 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-31 : ℤ) ∧
    (∑ n ∈ Ico 137216 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1245 : ℕ) ∧
    (∑ n ∈ Ico 137216 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1125292 : ℤ) ∧
    (∑ n ∈ Ico 137216 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22506348282802863416568704476 : ℤ) := by
  rcases cdemPrefixStats_137216_138240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_138240_139264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 137216 ≤ 138240) (by norm_num : 138240 ≤ 139264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 137216 ≤ 138240) (by norm_num : 138240 ≤ 139264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 138240) (by norm_num : 138240 ≤ 139264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 137216 ≤ 138240) (by norm_num : 138240 ≤ 139264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_135168_139264 :
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-100 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3654068 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-73082450948001589317295747044 : ℤ) := by
  rcases cdemPrefixStats_135168_137216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_137216_139264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 135168 ≤ 137216) (by norm_num : 137216 ≤ 139264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 135168 ≤ 137216) (by norm_num : 137216 ≤ 139264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 137216) (by norm_num : 137216 ≤ 139264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 135168 ≤ 137216) (by norm_num : 137216 ≤ 139264), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup033_checked_complete :
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-100 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3654068 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-73082450948001589317295747044 : ℤ) := cdemPrefixStats_135168_139264
end Helfgott
#print axioms Helfgott.cdemPrefixGroup033_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-100 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3654068 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-73082450948001589317295747044 : ℤ) := Helfgott.cdemPrefixGroup033_checked_complete
#print axioms solution
