-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup045_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:53:25.262618+00:00
-- url     : https://prove2.me/submissions/402678c6-13b5-441a-9800-db72709cab65

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
private theorem cdemPrefixStats_184320_184384 :
    (∑ n ∈ Ico 184320 184384, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 184320 184384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 184320 184384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135576 : ℤ) ∧
    (∑ n ∈ Ico 184320 184384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2711611315138872842621868987 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184384_184448 :
    (∑ n ∈ Ico 184384 184448, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 184384 184448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 184384 184448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (406706 : ℤ) ∧
    (∑ n ∈ Ico 184384 184448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8134287339838313584353055310 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184320_184448 :
    (∑ n ∈ Ico 184320 184448, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 184320 184448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 184320 184448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (542282 : ℤ) ∧
    (∑ n ∈ Ico 184320 184448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10845898654977186426974924297 : ℤ) := by
  rcases cdemPrefixStats_184320_184384 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184384_184448 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184320 ≤ 184384) (by norm_num : 184384 ≤ 184448), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184320 ≤ 184384) (by norm_num : 184384 ≤ 184448), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184384) (by norm_num : 184384 ≤ 184448), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184384) (by norm_num : 184384 ≤ 184448), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184448_184512 :
    (∑ n ∈ Ico 184448 184512, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 184448 184512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 184448 184512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54222 : ℤ) ∧
    (∑ n ∈ Ico 184448 184512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1084392841192124484925860568 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184512_184576 :
    (∑ n ∈ Ico 184512 184576, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 184512 184576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 184512 184576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135469 : ℤ) ∧
    (∑ n ∈ Ico 184512 184576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2709401555892920258253358657 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184448_184576 :
    (∑ n ∈ Ico 184448 184576, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 184448 184576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 184448 184576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-81247 : ℤ) ∧
    (∑ n ∈ Ico 184448 184576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1625008714700795773327498089 : ℤ) := by
  rcases cdemPrefixStats_184448_184512 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184512_184576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184448 ≤ 184512) (by norm_num : 184512 ≤ 184576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184448 ≤ 184512) (by norm_num : 184512 ≤ 184576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184448 ≤ 184512) (by norm_num : 184512 ≤ 184576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184448 ≤ 184512) (by norm_num : 184512 ≤ 184576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184320_184576 :
    (∑ n ∈ Ico 184320 184576, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 184320 184576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 184320 184576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (461035 : ℤ) ∧
    (∑ n ∈ Ico 184320 184576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9220889940276390653647426208 : ℤ) := by
  rcases cdemPrefixStats_184320_184448 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184448_184576 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184320 ≤ 184448) (by norm_num : 184448 ≤ 184576), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184320 ≤ 184448) (by norm_num : 184448 ≤ 184576), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184448) (by norm_num : 184448 ≤ 184576), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184448) (by norm_num : 184448 ≤ 184576), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184576_184640 :
    (∑ n ∈ Ico 184576 184640, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 184576 184640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 184576 184640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (81253 : ℤ) ∧
    (∑ n ∈ Ico 184576 184640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1625038575083741045743369893 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184640_184704 :
    (∑ n ∈ Ico 184640 184704, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 184640 184704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 184640 184704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (243675 : ℤ) ∧
    (∑ n ∈ Ico 184640 184704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4873619885520554960791191737 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184576_184704 :
    (∑ n ∈ Ico 184576 184704, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 184576 184704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 184576 184704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (324928 : ℤ) ∧
    (∑ n ∈ Ico 184576 184704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6498658460604296006534561630 : ℤ) := by
  rcases cdemPrefixStats_184576_184640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184640_184704 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184576 ≤ 184640) (by norm_num : 184640 ≤ 184704), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184576 ≤ 184640) (by norm_num : 184640 ≤ 184704), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184576 ≤ 184640) (by norm_num : 184640 ≤ 184704), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184576 ≤ 184640) (by norm_num : 184640 ≤ 184704), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184704_184768 :
    (∑ n ∈ Ico 184704 184768, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 184704 184768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 184704 184768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135310 : ℤ) ∧
    (∑ n ∈ Ico 184704 184768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2706272066208289986334127145 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184768_184832 :
    (∑ n ∈ Ico 184768 184832, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 184768 184832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 184768 184832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (135294 : ℤ) ∧
    (∑ n ∈ Ico 184768 184832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2705859029279587274303532935 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184704_184832 :
    (∑ n ∈ Ico 184704 184832, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 184704 184832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 184704 184832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (270604 : ℤ) ∧
    (∑ n ∈ Ico 184704 184832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5412131095487877260637660080 : ℤ) := by
  rcases cdemPrefixStats_184704_184768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184768_184832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184704 ≤ 184768) (by norm_num : 184768 ≤ 184832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184704 ≤ 184768) (by norm_num : 184768 ≤ 184832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184704 ≤ 184768) (by norm_num : 184768 ≤ 184832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184704 ≤ 184768) (by norm_num : 184768 ≤ 184832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184576_184832 :
    (∑ n ∈ Ico 184576 184832, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 184576 184832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 184576 184832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (595532 : ℤ) ∧
    (∑ n ∈ Ico 184576 184832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11910789556092173267172221710 : ℤ) := by
  rcases cdemPrefixStats_184576_184704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184704_184832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184576 ≤ 184704) (by norm_num : 184704 ≤ 184832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184576 ≤ 184704) (by norm_num : 184704 ≤ 184832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184576 ≤ 184704) (by norm_num : 184704 ≤ 184832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184576 ≤ 184704) (by norm_num : 184704 ≤ 184832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184320_184832 :
    (∑ n ∈ Ico 184320 184832, mobiusTreeValue 16 mobiusTable1200001 n) = (39 : ℤ) ∧
    (∑ n ∈ Ico 184320 184832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 184320 184832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1056567 : ℤ) ∧
    (∑ n ∈ Ico 184320 184832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21131679496368563920819647918 : ℤ) := by
  rcases cdemPrefixStats_184320_184576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184576_184832 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184320 ≤ 184576) (by norm_num : 184576 ≤ 184832), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184320 ≤ 184576) (by norm_num : 184576 ≤ 184832), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184576) (by norm_num : 184576 ≤ 184832), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184576) (by norm_num : 184576 ≤ 184832), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184832_184896 :
    (∑ n ∈ Ico 184832 184896, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 184832 184896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 184832 184896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-216393 : ℤ) ∧
    (∑ n ∈ Ico 184832 184896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4327956305293278220872590467 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184896_184960 :
    (∑ n ∈ Ico 184896 184960, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 184896 184960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 184896 184960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (81112 : ℤ) ∧
    (∑ n ∈ Ico 184896 184960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1622290997559617675478007714 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184832_184960 :
    (∑ n ∈ Ico 184832 184960, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 184832 184960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 184832 184960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135281 : ℤ) ∧
    (∑ n ∈ Ico 184832 184960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2705665307733660545394582753 : ℤ) := by
  rcases cdemPrefixStats_184832_184896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184896_184960 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184832 ≤ 184896) (by norm_num : 184896 ≤ 184960), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184832 ≤ 184896) (by norm_num : 184896 ≤ 184960), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184832 ≤ 184896) (by norm_num : 184896 ≤ 184960), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184832 ≤ 184896) (by norm_num : 184896 ≤ 184960), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184960_185024 :
    (∑ n ∈ Ico 184960 185024, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 184960 185024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 184960 185024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (189197 : ℤ) ∧
    (∑ n ∈ Ico 184960 185024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3784002986744616773469890991 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185024_185088 :
    (∑ n ∈ Ico 185024 185088, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 185024 185088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 185024 185088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-216161 : ℤ) ∧
    (∑ n ∈ Ico 185024 185088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4323348684947546254562060629 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_184960_185088 :
    (∑ n ∈ Ico 184960 185088, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 184960 185088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 184960 185088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26964 : ℤ) ∧
    (∑ n ∈ Ico 184960 185088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-539345698202929481092169638 : ℤ) := by
  rcases cdemPrefixStats_184960_185024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185024_185088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184960 ≤ 185024) (by norm_num : 185024 ≤ 185088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184960 ≤ 185024) (by norm_num : 185024 ≤ 185088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184960 ≤ 185024) (by norm_num : 185024 ≤ 185088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184960 ≤ 185024) (by norm_num : 185024 ≤ 185088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184832_185088 :
    (∑ n ∈ Ico 184832 185088, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 184832 185088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 184832 185088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-162245 : ℤ) ∧
    (∑ n ∈ Ico 184832 185088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3245011005936590026486752391 : ℤ) := by
  rcases cdemPrefixStats_184832_184960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184960_185088 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184832 ≤ 184960) (by norm_num : 184960 ≤ 185088), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184832 ≤ 184960) (by norm_num : 184960 ≤ 185088), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184832 ≤ 184960) (by norm_num : 184960 ≤ 185088), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184832 ≤ 184960) (by norm_num : 184960 ≤ 185088), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185088_185152 :
    (∑ n ∈ Ico 185088 185152, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 185088 185152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 185088 185152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (54017 : ℤ) ∧
    (∑ n ∈ Ico 185088 185152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1080403656073821378094547683 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185152_185216 :
    (∑ n ∈ Ico 185152 185216, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 185152 185216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 185152 185216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-135005 : ℤ) ∧
    (∑ n ∈ Ico 185152 185216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2700183573304598379809785950 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185088_185216 :
    (∑ n ∈ Ico 185088 185216, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 185088 185216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 185088 185216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-80988 : ℤ) ∧
    (∑ n ∈ Ico 185088 185216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1619779917230777001715238267 : ℤ) := by
  rcases cdemPrefixStats_185088_185152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185152_185216 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185088 ≤ 185152) (by norm_num : 185152 ≤ 185216), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185088 ≤ 185152) (by norm_num : 185152 ≤ 185216), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185088 ≤ 185152) (by norm_num : 185152 ≤ 185216), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185088 ≤ 185152) (by norm_num : 185152 ≤ 185216), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185216_185280 :
    (∑ n ∈ Ico 185216 185280, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 185216 185280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 185216 185280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26958 : ℤ) ∧
    (∑ n ∈ Ico 185216 185280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (539175783535345219386195906 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185280_185344 :
    (∑ n ∈ Ico 185280 185344, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 185280 185344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 185280 185344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-80944 : ℤ) ∧
    (∑ n ∈ Ico 185280 185344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1618952486857933603819941468 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185216_185344 :
    (∑ n ∈ Ico 185216 185344, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 185216 185344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 185216 185344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53986 : ℤ) ∧
    (∑ n ∈ Ico 185216 185344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1079776703322588384433745562 : ℤ) := by
  rcases cdemPrefixStats_185216_185280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185280_185344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185216 ≤ 185280) (by norm_num : 185280 ≤ 185344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185216 ≤ 185280) (by norm_num : 185280 ≤ 185344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185216 ≤ 185280) (by norm_num : 185280 ≤ 185344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185216 ≤ 185280) (by norm_num : 185280 ≤ 185344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185088_185344 :
    (∑ n ∈ Ico 185088 185344, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 185088 185344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 185088 185344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-134974 : ℤ) ∧
    (∑ n ∈ Ico 185088 185344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2699556620553365386148983829 : ℤ) := by
  rcases cdemPrefixStats_185088_185216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185216_185344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185088 ≤ 185216) (by norm_num : 185216 ≤ 185344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185088 ≤ 185216) (by norm_num : 185216 ≤ 185344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185088 ≤ 185216) (by norm_num : 185216 ≤ 185344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185088 ≤ 185216) (by norm_num : 185216 ≤ 185344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184832_185344 :
    (∑ n ∈ Ico 184832 185344, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 184832 185344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 184832 185344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-297219 : ℤ) ∧
    (∑ n ∈ Ico 184832 185344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5944567626489955412635736220 : ℤ) := by
  rcases cdemPrefixStats_184832_185088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185088_185344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184832 ≤ 185088) (by norm_num : 185088 ≤ 185344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184832 ≤ 185088) (by norm_num : 185088 ≤ 185344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184832 ≤ 185088) (by norm_num : 185088 ≤ 185344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184832 ≤ 185088) (by norm_num : 185088 ≤ 185344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184320_185344 :
    (∑ n ∈ Ico 184320 185344, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 184320 185344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (628 : ℕ) ∧
    (∑ n ∈ Ico 184320 185344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (759348 : ℤ) ∧
    (∑ n ∈ Ico 184320 185344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15187111869878608508183911698 : ℤ) := by
  rcases cdemPrefixStats_184320_184832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_184832_185344 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184320 ≤ 184832) (by norm_num : 184832 ≤ 185344), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184320 ≤ 184832) (by norm_num : 184832 ≤ 185344), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184832) (by norm_num : 184832 ≤ 185344), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 184832) (by norm_num : 184832 ≤ 185344), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185344_185408 :
    (∑ n ∈ Ico 185344 185408, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 185344 185408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 185344 185408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-161831 : ℤ) ∧
    (∑ n ∈ Ico 185344 185408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3236653314949984636752543435 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185408_185472 :
    (∑ n ∈ Ico 185408 185472, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 185408 185472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 185408 185472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26983 : ℤ) ∧
    (∑ n ∈ Ico 185408 185472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (539647643447384364193068230 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185344_185472 :
    (∑ n ∈ Ico 185344 185472, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 185344 185472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 185344 185472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-134848 : ℤ) ∧
    (∑ n ∈ Ico 185344 185472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2697005671502600272559475205 : ℤ) := by
  rcases cdemPrefixStats_185344_185408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185408_185472 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185344 ≤ 185408) (by norm_num : 185408 ≤ 185472), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185344 ≤ 185408) (by norm_num : 185408 ≤ 185472), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185408) (by norm_num : 185408 ≤ 185472), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185408) (by norm_num : 185408 ≤ 185472), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185472_185536 :
    (∑ n ∈ Ico 185472 185536, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 185472 185536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 185472 185536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80855 : ℤ) ∧
    (∑ n ∈ Ico 185472 185536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1617157670604164415139365480 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185536_185600 :
    (∑ n ∈ Ico 185536 185600, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 185536 185600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 185536 185600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53918 : ℤ) ∧
    (∑ n ∈ Ico 185536 185600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1078408071712120431095704113 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185472_185600 :
    (∑ n ∈ Ico 185472 185600, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 185472 185600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 185472 185600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26937 : ℤ) ∧
    (∑ n ∈ Ico 185472 185600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (538749598892043984043661367 : ℤ) := by
  rcases cdemPrefixStats_185472_185536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185536_185600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185472 ≤ 185536) (by norm_num : 185536 ≤ 185600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185472 ≤ 185536) (by norm_num : 185536 ≤ 185600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185472 ≤ 185536) (by norm_num : 185536 ≤ 185600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185472 ≤ 185536) (by norm_num : 185536 ≤ 185600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185344_185600 :
    (∑ n ∈ Ico 185344 185600, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 185344 185600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 185344 185600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-107911 : ℤ) ∧
    (∑ n ∈ Ico 185344 185600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2158256072610556288515813838 : ℤ) := by
  rcases cdemPrefixStats_185344_185472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185472_185600 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185344 ≤ 185472) (by norm_num : 185472 ≤ 185600), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185344 ≤ 185472) (by norm_num : 185472 ≤ 185600), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185472) (by norm_num : 185472 ≤ 185600), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185472) (by norm_num : 185472 ≤ 185600), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185600_185664 :
    (∑ n ∈ Ico 185600 185664, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 185600 185664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 185600 185664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-242400 : ℤ) ∧
    (∑ n ∈ Ico 185600 185664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4848093088483793096657450895 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185664_185728 :
    (∑ n ∈ Ico 185664 185728, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 185664 185728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 185664 185728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53870 : ℤ) ∧
    (∑ n ∈ Ico 185664 185728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1077385803167796241094153669 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185600_185728 :
    (∑ n ∈ Ico 185600 185728, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 185600 185728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 185600 185728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-296270 : ℤ) ∧
    (∑ n ∈ Ico 185600 185728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5925478891651589337751604564 : ℤ) := by
  rcases cdemPrefixStats_185600_185664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185664_185728 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185600 ≤ 185664) (by norm_num : 185664 ≤ 185728), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185600 ≤ 185664) (by norm_num : 185664 ≤ 185728), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185600 ≤ 185664) (by norm_num : 185664 ≤ 185728), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185600 ≤ 185664) (by norm_num : 185664 ≤ 185728), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185728_185792 :
    (∑ n ∈ Ico 185728 185792, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 185728 185792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 185728 185792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-269157 : ℤ) ∧
    (∑ n ∈ Ico 185728 185792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5383206279881386108090211332 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185792_185856 :
    (∑ n ∈ Ico 185792 185856, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 185792 185856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 185792 185856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26908 : ℤ) ∧
    (∑ n ∈ Ico 185792 185856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-538192792100124359674259462 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185728_185856 :
    (∑ n ∈ Ico 185728 185856, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 185728 185856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 185728 185856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-296065 : ℤ) ∧
    (∑ n ∈ Ico 185728 185856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5921399071981510467764470794 : ℤ) := by
  rcases cdemPrefixStats_185728_185792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185792_185856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185728 ≤ 185792) (by norm_num : 185792 ≤ 185856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185728 ≤ 185792) (by norm_num : 185792 ≤ 185856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185728 ≤ 185792) (by norm_num : 185792 ≤ 185856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185728 ≤ 185792) (by norm_num : 185792 ≤ 185856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185600_185856 :
    (∑ n ∈ Ico 185600 185856, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 185600 185856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 185600 185856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-592335 : ℤ) ∧
    (∑ n ∈ Ico 185600 185856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11846877963633099805516075358 : ℤ) := by
  rcases cdemPrefixStats_185600_185728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185728_185856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185600 ≤ 185728) (by norm_num : 185728 ≤ 185856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185600 ≤ 185728) (by norm_num : 185728 ≤ 185856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185600 ≤ 185728) (by norm_num : 185728 ≤ 185856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185600 ≤ 185728) (by norm_num : 185728 ≤ 185856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185344_185856 :
    (∑ n ∈ Ico 185344 185856, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 185344 185856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 185344 185856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-700246 : ℤ) ∧
    (∑ n ∈ Ico 185344 185856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14005134036243656094031889196 : ℤ) := by
  rcases cdemPrefixStats_185344_185600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185600_185856 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185344 ≤ 185600) (by norm_num : 185600 ≤ 185856), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185344 ≤ 185600) (by norm_num : 185600 ≤ 185856), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185600) (by norm_num : 185600 ≤ 185856), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185600) (by norm_num : 185600 ≤ 185856), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185856_185920 :
    (∑ n ∈ Ico 185856 185920, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 185856 185920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 185856 185920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53785 : ℤ) ∧
    (∑ n ∈ Ico 185856 185920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1075754607757373613982834946 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185920_185984 :
    (∑ n ∈ Ico 185920 185984, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 185920 185984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 185920 185984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80650 : ℤ) ∧
    (∑ n ∈ Ico 185920 185984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1613013053492599190887961025 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185856_185984 :
    (∑ n ∈ Ico 185856 185984, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 185856 185984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 185856 185984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (134435 : ℤ) ∧
    (∑ n ∈ Ico 185856 185984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2688767661249972804870795971 : ℤ) := by
  rcases cdemPrefixStats_185856_185920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185920_185984 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185856 ≤ 185920) (by norm_num : 185920 ≤ 185984), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185856 ≤ 185920) (by norm_num : 185920 ≤ 185984), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185856 ≤ 185920) (by norm_num : 185920 ≤ 185984), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185856 ≤ 185920) (by norm_num : 185920 ≤ 185984), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185984_186048 :
    (∑ n ∈ Ico 185984 186048, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 185984 186048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 185984 186048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-134372 : ℤ) ∧
    (∑ n ∈ Ico 185984 186048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2687527509471101730040628398 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186048_186112 :
    (∑ n ∈ Ico 186048 186112, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 186048 186112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 186048 186112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (161199 : ℤ) ∧
    (∑ n ∈ Ico 186048 186112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3224078833214963151205686433 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_185984_186112 :
    (∑ n ∈ Ico 185984 186112, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 185984 186112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 185984 186112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26827 : ℤ) ∧
    (∑ n ∈ Ico 185984 186112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (536551323743861421165058035 : ℤ) := by
  rcases cdemPrefixStats_185984_186048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186048_186112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185984 ≤ 186048) (by norm_num : 186048 ≤ 186112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185984 ≤ 186048) (by norm_num : 186048 ≤ 186112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185984 ≤ 186048) (by norm_num : 186048 ≤ 186112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185984 ≤ 186048) (by norm_num : 186048 ≤ 186112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185856_186112 :
    (∑ n ∈ Ico 185856 186112, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 185856 186112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 185856 186112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (161262 : ℤ) ∧
    (∑ n ∈ Ico 185856 186112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3225318984993834226035854006 : ℤ) := by
  rcases cdemPrefixStats_185856_185984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185984_186112 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185856 ≤ 185984) (by norm_num : 185984 ≤ 186112), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185856 ≤ 185984) (by norm_num : 185984 ≤ 186112), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185856 ≤ 185984) (by norm_num : 185984 ≤ 186112), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185856 ≤ 185984) (by norm_num : 185984 ≤ 186112), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186112_186176 :
    (∑ n ∈ Ico 186112 186176, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 186112 186176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 186112 186176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-134302 : ℤ) ∧
    (∑ n ∈ Ico 186112 186176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2686017457861847565155772523 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186176_186240 :
    (∑ n ∈ Ico 186176 186240, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 186176 186240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 186176 186240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-80560 : ℤ) ∧
    (∑ n ∈ Ico 186176 186240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1611173715843833842050701337 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186112_186240 :
    (∑ n ∈ Ico 186112 186240, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 186112 186240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 186112 186240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-214862 : ℤ) ∧
    (∑ n ∈ Ico 186112 186240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4297191173705681407206473860 : ℤ) := by
  rcases cdemPrefixStats_186112_186176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186176_186240 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186112 ≤ 186176) (by norm_num : 186176 ≤ 186240), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186112 ≤ 186176) (by norm_num : 186176 ≤ 186240), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186112 ≤ 186176) (by norm_num : 186176 ≤ 186240), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186112 ≤ 186176) (by norm_num : 186176 ≤ 186240), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186240_186304 :
    (∑ n ∈ Ico 186240 186304, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 186240 186304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 186240 186304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268408 : ℤ) ∧
    (∑ n ∈ Ico 186240 186304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5368309016300742649902363071 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186304_186368 :
    (∑ n ∈ Ico 186304 186368, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 186304 186368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 186304 186368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26790 : ℤ) ∧
    (∑ n ∈ Ico 186304 186368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (535823998677200475332838869 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186240_186368 :
    (∑ n ∈ Ico 186240 186368, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 186240 186368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 186240 186368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (295198 : ℤ) ∧
    (∑ n ∈ Ico 186240 186368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5904133014977943125235201940 : ℤ) := by
  rcases cdemPrefixStats_186240_186304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186304_186368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186240 ≤ 186304) (by norm_num : 186304 ≤ 186368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186240 ≤ 186304) (by norm_num : 186304 ≤ 186368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186240 ≤ 186304) (by norm_num : 186304 ≤ 186368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186240 ≤ 186304) (by norm_num : 186304 ≤ 186368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186112_186368 :
    (∑ n ∈ Ico 186112 186368, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 186112 186368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 186112 186368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80336 : ℤ) ∧
    (∑ n ∈ Ico 186112 186368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1606941841272261718028728080 : ℤ) := by
  rcases cdemPrefixStats_186112_186240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186240_186368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186112 ≤ 186240) (by norm_num : 186240 ≤ 186368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186112 ≤ 186240) (by norm_num : 186240 ≤ 186368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186112 ≤ 186240) (by norm_num : 186240 ≤ 186368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186112 ≤ 186240) (by norm_num : 186240 ≤ 186368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185856_186368 :
    (∑ n ∈ Ico 185856 186368, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 185856 186368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 185856 186368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (241598 : ℤ) ∧
    (∑ n ∈ Ico 185856 186368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4832260826266095944064582086 : ℤ) := by
  rcases cdemPrefixStats_185856_186112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186112_186368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185856 ≤ 186112) (by norm_num : 186112 ≤ 186368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185856 ≤ 186112) (by norm_num : 186112 ≤ 186368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185856 ≤ 186112) (by norm_num : 186112 ≤ 186368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185856 ≤ 186112) (by norm_num : 186112 ≤ 186368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_185344_186368 :
    (∑ n ∈ Ico 185344 186368, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 185344 186368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 185344 186368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-458648 : ℤ) ∧
    (∑ n ∈ Ico 185344 186368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9172873209977560149967307110 : ℤ) := by
  rcases cdemPrefixStats_185344_185856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185856_186368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 185344 ≤ 185856) (by norm_num : 185856 ≤ 186368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 185344 ≤ 185856) (by norm_num : 185856 ≤ 186368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185856) (by norm_num : 185856 ≤ 186368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 185344 ≤ 185856) (by norm_num : 185856 ≤ 186368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184320_186368 :
    (∑ n ∈ Ico 184320 186368, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 184320 186368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 184320 186368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (300700 : ℤ) ∧
    (∑ n ∈ Ico 184320 186368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6014238659901048358216604588 : ℤ) := by
  rcases cdemPrefixStats_184320_185344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_185344_186368 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184320 ≤ 185344) (by norm_num : 185344 ≤ 186368), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184320 ≤ 185344) (by norm_num : 185344 ≤ 186368), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 185344) (by norm_num : 185344 ≤ 186368), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 185344) (by norm_num : 185344 ≤ 186368), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186368_186432 :
    (∑ n ∈ Ico 186368 186432, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 186368 186432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 186368 186432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (187742 : ℤ) ∧
    (∑ n ∈ Ico 186368 186432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3754959034957727902480431661 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186432_186496 :
    (∑ n ∈ Ico 186432 186496, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 186432 186496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 186432 186496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26797 : ℤ) ∧
    (∑ n ∈ Ico 186432 186496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (536017556804921230872761735 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186368_186496 :
    (∑ n ∈ Ico 186368 186496, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 186368 186496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 186368 186496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (214539 : ℤ) ∧
    (∑ n ∈ Ico 186368 186496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4290976591762649133353193396 : ℤ) := by
  rcases cdemPrefixStats_186368_186432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186432_186496 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186368 ≤ 186432) (by norm_num : 186432 ≤ 186496), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186368 ≤ 186432) (by norm_num : 186432 ≤ 186496), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186432) (by norm_num : 186432 ≤ 186496), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186432) (by norm_num : 186432 ≤ 186496), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186496_186560 :
    (∑ n ∈ Ico 186496 186560, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 186496 186560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 186496 186560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (268085 : ℤ) ∧
    (∑ n ∈ Ico 186496 186560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5361760620009111073394509430 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186560_186624 :
    (∑ n ∈ Ico 186560 186624, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 186560 186624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 186560 186624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80387 : ℤ) ∧
    (∑ n ∈ Ico 186560 186624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1607751554784531802086193397 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186496_186624 :
    (∑ n ∈ Ico 186496 186624, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 186496 186624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 186496 186624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (348472 : ℤ) ∧
    (∑ n ∈ Ico 186496 186624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6969512174793642875480702827 : ℤ) := by
  rcases cdemPrefixStats_186496_186560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186560_186624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186496 ≤ 186560) (by norm_num : 186560 ≤ 186624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186496 ≤ 186560) (by norm_num : 186560 ≤ 186624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186496 ≤ 186560) (by norm_num : 186560 ≤ 186624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186496 ≤ 186560) (by norm_num : 186560 ≤ 186624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186368_186624 :
    (∑ n ∈ Ico 186368 186624, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 186368 186624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 186368 186624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (563011 : ℤ) ∧
    (∑ n ∈ Ico 186368 186624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11260488766556292008833896223 : ℤ) := by
  rcases cdemPrefixStats_186368_186496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186496_186624 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186368 ≤ 186496) (by norm_num : 186496 ≤ 186624), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186368 ≤ 186496) (by norm_num : 186496 ≤ 186624), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186496) (by norm_num : 186496 ≤ 186624), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186496) (by norm_num : 186496 ≤ 186624), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186624_186688 :
    (∑ n ∈ Ico 186624 186688, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 186624 186688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 186624 186688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26772 : ℤ) ∧
    (∑ n ∈ Ico 186624 186688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-535434932460001753039107523 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186688_186752 :
    (∑ n ∈ Ico 186688 186752, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 186688 186752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (34 : ℕ) ∧
    (∑ n ∈ Ico 186688 186752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-374887 : ℤ) ∧
    (∑ n ∈ Ico 186688 186752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7497854925088116437379972125 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186624_186752 :
    (∑ n ∈ Ico 186624 186752, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 186624 186752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (71 : ℕ) ∧
    (∑ n ∈ Ico 186624 186752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-401659 : ℤ) ∧
    (∑ n ∈ Ico 186624 186752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8033289857548118190419079648 : ℤ) := by
  rcases cdemPrefixStats_186624_186688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186688_186752 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186624 ≤ 186688) (by norm_num : 186688 ≤ 186752), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186624 ≤ 186688) (by norm_num : 186688 ≤ 186752), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186624 ≤ 186688) (by norm_num : 186688 ≤ 186752), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186624 ≤ 186688) (by norm_num : 186688 ≤ 186752), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186752_186816 :
    (∑ n ∈ Ico 186752 186816, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 186752 186816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 186752 186816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (160589 : ℤ) ∧
    (∑ n ∈ Ico 186752 186816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3211828068796897745171951777 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186816_186880 :
    (∑ n ∈ Ico 186816 186880, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 186816 186880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 186816 186880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-26744 : ℤ) ∧
    (∑ n ∈ Ico 186816 186880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-534919402106749137413389639 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186752_186880 :
    (∑ n ∈ Ico 186752 186880, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 186752 186880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 186752 186880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (133845 : ℤ) ∧
    (∑ n ∈ Ico 186752 186880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2676908666690148607758562138 : ℤ) := by
  rcases cdemPrefixStats_186752_186816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186816_186880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186752 ≤ 186816) (by norm_num : 186816 ≤ 186880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186752 ≤ 186816) (by norm_num : 186816 ≤ 186880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186752 ≤ 186816) (by norm_num : 186816 ≤ 186880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186752 ≤ 186816) (by norm_num : 186816 ≤ 186880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186624_186880 :
    (∑ n ∈ Ico 186624 186880, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 186624 186880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 186624 186880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-267814 : ℤ) ∧
    (∑ n ∈ Ico 186624 186880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5356381190857969582660517510 : ℤ) := by
  rcases cdemPrefixStats_186624_186752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186752_186880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186624 ≤ 186752) (by norm_num : 186752 ≤ 186880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186624 ≤ 186752) (by norm_num : 186752 ≤ 186880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186624 ≤ 186752) (by norm_num : 186752 ≤ 186880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186624 ≤ 186752) (by norm_num : 186752 ≤ 186880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186368_186880 :
    (∑ n ∈ Ico 186368 186880, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 186368 186880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 186368 186880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (295197 : ℤ) ∧
    (∑ n ∈ Ico 186368 186880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5904107575698322426173378713 : ℤ) := by
  rcases cdemPrefixStats_186368_186624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186624_186880 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186368 ≤ 186624) (by norm_num : 186624 ≤ 186880), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186368 ≤ 186624) (by norm_num : 186624 ≤ 186880), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186624) (by norm_num : 186624 ≤ 186880), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186624) (by norm_num : 186624 ≤ 186880), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186880_186944 :
    (∑ n ∈ Ico 186880 186944, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 186880 186944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 186880 186944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (267489 : ℤ) ∧
    (∑ n ∈ Ico 186880 186944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5349865200098624770069698471 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186944_187008 :
    (∑ n ∈ Ico 186944 187008, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 186944 187008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 186944 187008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26715 : ℤ) ∧
    (∑ n ∈ Ico 186944 187008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (534270163001469818041593561 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_186880_187008 :
    (∑ n ∈ Ico 186880 187008, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 186880 187008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 186880 187008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (294204 : ℤ) ∧
    (∑ n ∈ Ico 186880 187008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5884135363100094588111292032 : ℤ) := by
  rcases cdemPrefixStats_186880_186944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186944_187008 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186880 ≤ 186944) (by norm_num : 186944 ≤ 187008), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186880 ≤ 186944) (by norm_num : 186944 ≤ 187008), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186880 ≤ 186944) (by norm_num : 186944 ≤ 187008), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186880 ≤ 186944) (by norm_num : 186944 ≤ 187008), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187008_187072 :
    (∑ n ∈ Ico 187008 187072, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 187008 187072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187008 187072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (80177 : ℤ) ∧
    (∑ n ∈ Ico 187008 187072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1603597648420208489140113264 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187072_187136 :
    (∑ n ∈ Ico 187072 187136, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 187072 187136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187072 187136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240497 : ℤ) ∧
    (∑ n ∈ Ico 187072 187136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4810107721102139844715877733 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187008_187136 :
    (∑ n ∈ Ico 187008 187136, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 187008 187136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 187008 187136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-160320 : ℤ) ∧
    (∑ n ∈ Ico 187008 187136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3206510072681931355575764469 : ℤ) := by
  rcases cdemPrefixStats_187008_187072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187072_187136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187008 ≤ 187072) (by norm_num : 187072 ≤ 187136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187008 ≤ 187072) (by norm_num : 187072 ≤ 187136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187008 ≤ 187072) (by norm_num : 187072 ≤ 187136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187008 ≤ 187072) (by norm_num : 187072 ≤ 187136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186880_187136 :
    (∑ n ∈ Ico 186880 187136, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 186880 187136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 186880 187136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (133884 : ℤ) ∧
    (∑ n ∈ Ico 186880 187136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2677625290418163232535527563 : ℤ) := by
  rcases cdemPrefixStats_186880_187008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187008_187136 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186880 ≤ 187008) (by norm_num : 187008 ≤ 187136), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186880 ≤ 187008) (by norm_num : 187008 ≤ 187136), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186880 ≤ 187008) (by norm_num : 187008 ≤ 187136), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186880 ≤ 187008) (by norm_num : 187008 ≤ 187136), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187136_187200 :
    (∑ n ∈ Ico 187136 187200, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 187136 187200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187136 187200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-240420 : ℤ) ∧
    (∑ n ∈ Ico 187136 187200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4808462953752047205062023644 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187200_187264 :
    (∑ n ∈ Ico 187200 187264, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 187200 187264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 187200 187264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106821 : ℤ) ∧
    (∑ n ∈ Ico 187200 187264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2136444051432810252375335855 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187136_187264 :
    (∑ n ∈ Ico 187136 187264, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 187136 187264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 187136 187264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133599 : ℤ) ∧
    (∑ n ∈ Ico 187136 187264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2672018902319236952686687789 : ℤ) := by
  rcases cdemPrefixStats_187136_187200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187200_187264 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187136 ≤ 187200) (by norm_num : 187200 ≤ 187264), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187136 ≤ 187200) (by norm_num : 187200 ≤ 187264), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187136 ≤ 187200) (by norm_num : 187200 ≤ 187264), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187136 ≤ 187200) (by norm_num : 187200 ≤ 187264), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187264_187328 :
    (∑ n ∈ Ico 187264 187328, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 187264 187328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 187264 187328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-106769 : ℤ) ∧
    (∑ n ∈ Ico 187264 187328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2135463061224197976717568953 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187328_187392 :
    (∑ n ∈ Ico 187328 187392, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 187328 187392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 187328 187392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-426983 : ℤ) ∧
    (∑ n ∈ Ico 187328 187392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8539857899248705837942080717 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187264_187392 :
    (∑ n ∈ Ico 187264 187392, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 187264 187392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 187264 187392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-533752 : ℤ) ∧
    (∑ n ∈ Ico 187264 187392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10675320960472903814659649670 : ℤ) := by
  rcases cdemPrefixStats_187264_187328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187328_187392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187264 ≤ 187328) (by norm_num : 187328 ≤ 187392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187264 ≤ 187328) (by norm_num : 187328 ≤ 187392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187264 ≤ 187328) (by norm_num : 187328 ≤ 187392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187264 ≤ 187328) (by norm_num : 187328 ≤ 187392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187136_187392 :
    (∑ n ∈ Ico 187136 187392, mobiusTreeValue 16 mobiusTable1200001 n) = (-25 : ℤ) ∧
    (∑ n ∈ Ico 187136 187392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 187136 187392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-667351 : ℤ) ∧
    (∑ n ∈ Ico 187136 187392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13347339862792140767346337459 : ℤ) := by
  rcases cdemPrefixStats_187136_187264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187264_187392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187136 ≤ 187264) (by norm_num : 187264 ≤ 187392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187136 ≤ 187264) (by norm_num : 187264 ≤ 187392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187136 ≤ 187264) (by norm_num : 187264 ≤ 187392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187136 ≤ 187264) (by norm_num : 187264 ≤ 187392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186880_187392 :
    (∑ n ∈ Ico 186880 187392, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 186880 187392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 186880 187392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-533467 : ℤ) ∧
    (∑ n ∈ Ico 186880 187392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10669714572373977534810809896 : ℤ) := by
  rcases cdemPrefixStats_186880_187136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187136_187392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186880 ≤ 187136) (by norm_num : 187136 ≤ 187392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186880 ≤ 187136) (by norm_num : 187136 ≤ 187392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186880 ≤ 187136) (by norm_num : 187136 ≤ 187392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186880 ≤ 187136) (by norm_num : 187136 ≤ 187392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186368_187392 :
    (∑ n ∈ Ico 186368 187392, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 186368 187392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (617 : ℕ) ∧
    (∑ n ∈ Ico 186368 187392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-238270 : ℤ) ∧
    (∑ n ∈ Ico 186368 187392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4765606996675655108637431183 : ℤ) := by
  rcases cdemPrefixStats_186368_186880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186880_187392 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186368 ≤ 186880) (by norm_num : 186880 ≤ 187392), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186368 ≤ 186880) (by norm_num : 186880 ≤ 187392), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186880) (by norm_num : 186880 ≤ 187392), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 186880) (by norm_num : 186880 ≤ 187392), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187392_187456 :
    (∑ n ∈ Ico 187392 187456, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 187392 187456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187392 187456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-80038 : ℤ) ∧
    (∑ n ∈ Ico 187392 187456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1600774063840625776751630828 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187456_187520 :
    (∑ n ∈ Ico 187456 187520, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 187456 187520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187456 187520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26672 : ℤ) ∧
    (∑ n ∈ Ico 187456 187520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (533458504431250507675838434 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187392_187520 :
    (∑ n ∈ Ico 187392 187520, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 187392 187520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 187392 187520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53366 : ℤ) ∧
    (∑ n ∈ Ico 187392 187520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1067315559409375269075792394 : ℤ) := by
  rcases cdemPrefixStats_187392_187456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187456_187520 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187392 ≤ 187456) (by norm_num : 187456 ≤ 187520), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187392 ≤ 187456) (by norm_num : 187456 ≤ 187520), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187456) (by norm_num : 187456 ≤ 187520), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187456) (by norm_num : 187456 ≤ 187520), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187520_187584 :
    (∑ n ∈ Ico 187520 187584, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 187520 187584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 187520 187584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159938 : ℤ) ∧
    (∑ n ∈ Ico 187520 187584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3198791534016849580287276036 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187584_187648 :
    (∑ n ∈ Ico 187584 187648, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 187584 187648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 187584 187648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106594 : ℤ) ∧
    (∑ n ∈ Ico 187584 187648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2131849573739888446154141054 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187520_187648 :
    (∑ n ∈ Ico 187520 187648, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 187520 187648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 187520 187648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53344 : ℤ) ∧
    (∑ n ∈ Ico 187520 187648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1066941960276961134133134982 : ℤ) := by
  rcases cdemPrefixStats_187520_187584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187584_187648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187520 ≤ 187584) (by norm_num : 187584 ≤ 187648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187520 ≤ 187584) (by norm_num : 187584 ≤ 187648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187520 ≤ 187584) (by norm_num : 187584 ≤ 187648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187520 ≤ 187584) (by norm_num : 187584 ≤ 187648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187392_187648 :
    (∑ n ∈ Ico 187392 187648, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 187392 187648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 187392 187648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-106710 : ℤ) ∧
    (∑ n ∈ Ico 187392 187648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2134257519686336403208927376 : ℤ) := by
  rcases cdemPrefixStats_187392_187520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187520_187648 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187392 ≤ 187520) (by norm_num : 187520 ≤ 187648), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187392 ≤ 187520) (by norm_num : 187520 ≤ 187648), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187520) (by norm_num : 187520 ≤ 187648), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187520) (by norm_num : 187520 ≤ 187648), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187648_187712 :
    (∑ n ∈ Ico 187648 187712, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 187648 187712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187648 187712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133231 : ℤ) ∧
    (∑ n ∈ Ico 187648 187712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2664588970250572744391629668 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187712_187776 :
    (∑ n ∈ Ico 187712 187776, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 187712 187776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 187712 187776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 187712 187776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-161724258035730427605866 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187648_187776 :
    (∑ n ∈ Ico 187648 187776, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 187648 187776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 187648 187776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133240 : ℤ) ∧
    (∑ n ∈ Ico 187648 187776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2664750694508608474819235534 : ℤ) := by
  rcases cdemPrefixStats_187648_187712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187712_187776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187648 ≤ 187712) (by norm_num : 187712 ≤ 187776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187648 ≤ 187712) (by norm_num : 187712 ≤ 187776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187648 ≤ 187712) (by norm_num : 187712 ≤ 187776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187648 ≤ 187712) (by norm_num : 187712 ≤ 187776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187776_187840 :
    (∑ n ∈ Ico 187776 187840, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 187776 187840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187776 187840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (346089 : ℤ) ∧
    (∑ n ∈ Ico 187776 187840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6921891998497741566878371517 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187840_187904 :
    (∑ n ∈ Ico 187840 187904, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 187840 187904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 187840 187904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (159687 : ℤ) ∧
    (∑ n ∈ Ico 187840 187904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3193802658720594331679179704 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187776_187904 :
    (∑ n ∈ Ico 187776 187904, mobiusTreeValue 16 mobiusTable1200001 n) = (19 : ℤ) ∧
    (∑ n ∈ Ico 187776 187904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 187776 187904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (505776 : ℤ) ∧
    (∑ n ∈ Ico 187776 187904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10115694657218335898557551221 : ℤ) := by
  rcases cdemPrefixStats_187776_187840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187840_187904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187776 ≤ 187840) (by norm_num : 187840 ≤ 187904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187776 ≤ 187840) (by norm_num : 187840 ≤ 187904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187776 ≤ 187840) (by norm_num : 187840 ≤ 187904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187776 ≤ 187840) (by norm_num : 187840 ≤ 187904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187648_187904 :
    (∑ n ∈ Ico 187648 187904, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 187648 187904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 187648 187904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (372536 : ℤ) ∧
    (∑ n ∈ Ico 187648 187904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7450943962709727423738315687 : ℤ) := by
  rcases cdemPrefixStats_187648_187776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187776_187904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187648 ≤ 187776) (by norm_num : 187776 ≤ 187904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187648 ≤ 187776) (by norm_num : 187776 ≤ 187904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187648 ≤ 187776) (by norm_num : 187776 ≤ 187904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187648 ≤ 187776) (by norm_num : 187776 ≤ 187904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187392_187904 :
    (∑ n ∈ Ico 187392 187904, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 187392 187904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 187392 187904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265826 : ℤ) ∧
    (∑ n ∈ Ico 187392 187904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5316686443023391020529388311 : ℤ) := by
  rcases cdemPrefixStats_187392_187648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187648_187904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187392 ≤ 187648) (by norm_num : 187648 ≤ 187904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187392 ≤ 187648) (by norm_num : 187648 ≤ 187904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187648) (by norm_num : 187648 ≤ 187904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187648) (by norm_num : 187648 ≤ 187904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187904_187968 :
    (∑ n ∈ Ico 187904 187968, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 187904 187968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 187904 187968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-79843 : ℤ) ∧
    (∑ n ∈ Ico 187904 187968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1596908213601046368791759389 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187968_188032 :
    (∑ n ∈ Ico 187968 188032, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 187968 188032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 187968 188032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53177 : ℤ) ∧
    (∑ n ∈ Ico 187968 188032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1063558230860454619080375050 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_187904_188032 :
    (∑ n ∈ Ico 187904 188032, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 187904 188032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 187904 188032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-133020 : ℤ) ∧
    (∑ n ∈ Ico 187904 188032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2660466444461500987872134439 : ℤ) := by
  rcases cdemPrefixStats_187904_187968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187968_188032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187904 ≤ 187968) (by norm_num : 187968 ≤ 188032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187904 ≤ 187968) (by norm_num : 187968 ≤ 188032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187904 ≤ 187968) (by norm_num : 187968 ≤ 188032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187904 ≤ 187968) (by norm_num : 187968 ≤ 188032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188032_188096 :
    (∑ n ∈ Ico 188032 188096, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 188032 188096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 188032 188096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (345631 : ℤ) ∧
    (∑ n ∈ Ico 188032 188096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6912738392028312113389078832 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188096_188160 :
    (∑ n ∈ Ico 188096 188160, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 188096 188160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 188096 188160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (26608 : ℤ) ∧
    (∑ n ∈ Ico 188096 188160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (532146350196501787098793754 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188032_188160 :
    (∑ n ∈ Ico 188032 188160, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 188032 188160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (74 : ℕ) ∧
    (∑ n ∈ Ico 188032 188160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (372239 : ℤ) ∧
    (∑ n ∈ Ico 188032 188160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7444884742224813900487872586 : ℤ) := by
  rcases cdemPrefixStats_188032_188096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188096_188160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188032 ≤ 188096) (by norm_num : 188096 ≤ 188160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188032 ≤ 188096) (by norm_num : 188096 ≤ 188160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188032 ≤ 188096) (by norm_num : 188096 ≤ 188160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188032 ≤ 188096) (by norm_num : 188096 ≤ 188160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187904_188160 :
    (∑ n ∈ Ico 187904 188160, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 187904 188160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 187904 188160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (239219 : ℤ) ∧
    (∑ n ∈ Ico 187904 188160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4784418297763312912615738147 : ℤ) := by
  rcases cdemPrefixStats_187904_188032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188032_188160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187904 ≤ 188032) (by norm_num : 188032 ≤ 188160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187904 ≤ 188032) (by norm_num : 188032 ≤ 188160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187904 ≤ 188032) (by norm_num : 188032 ≤ 188160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187904 ≤ 188032) (by norm_num : 188032 ≤ 188160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188160_188224 :
    (∑ n ∈ Ico 188160 188224, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 188160 188224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 188160 188224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53148 : ℤ) ∧
    (∑ n ∈ Ico 188160 188224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1063024009327630074964870327 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188224_188288 :
    (∑ n ∈ Ico 188224 188288, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 188224 188288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 188224 188288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (212500 : ℤ) ∧
    (∑ n ∈ Ico 188224 188288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4250048988585462488602443755 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188160_188288 :
    (∑ n ∈ Ico 188160 188288, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 188160 188288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 188160 188288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (265648 : ℤ) ∧
    (∑ n ∈ Ico 188160 188288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5313072997913092563567314082 : ℤ) := by
  rcases cdemPrefixStats_188160_188224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188224_188288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188160 ≤ 188224) (by norm_num : 188224 ≤ 188288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188160 ≤ 188224) (by norm_num : 188224 ≤ 188288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188160 ≤ 188224) (by norm_num : 188224 ≤ 188288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188160 ≤ 188224) (by norm_num : 188224 ≤ 188288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188288_188352 :
    (∑ n ∈ Ico 188288 188352, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 188288 188352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 188288 188352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-185860 : ℤ) ∧
    (∑ n ∈ Ico 188288 188352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3717291700697478325560858463 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188352_188416 :
    (∑ n ∈ Ico 188352 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 188352 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 188352 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-265428 : ℤ) ∧
    (∑ n ∈ Ico 188352 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5308638954838372681910021016 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_188288_188416 :
    (∑ n ∈ Ico 188288 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (-17 : ℤ) ∧
    (∑ n ∈ Ico 188288 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 188288 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-451288 : ℤ) ∧
    (∑ n ∈ Ico 188288 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9025930655535851007470879479 : ℤ) := by
  rcases cdemPrefixStats_188288_188352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188352_188416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188288 ≤ 188352) (by norm_num : 188352 ≤ 188416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188288 ≤ 188352) (by norm_num : 188352 ≤ 188416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188288 ≤ 188352) (by norm_num : 188352 ≤ 188416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188288 ≤ 188352) (by norm_num : 188352 ≤ 188416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_188160_188416 :
    (∑ n ∈ Ico 188160 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 188160 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 188160 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-185640 : ℤ) ∧
    (∑ n ∈ Ico 188160 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3712857657622758443903565397 : ℤ) := by
  rcases cdemPrefixStats_188160_188288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188288_188416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 188160 ≤ 188288) (by norm_num : 188288 ≤ 188416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 188160 ≤ 188288) (by norm_num : 188288 ≤ 188416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 188160 ≤ 188288) (by norm_num : 188288 ≤ 188416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 188160 ≤ 188288) (by norm_num : 188288 ≤ 188416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187904_188416 :
    (∑ n ∈ Ico 187904 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 187904 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 187904 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (53579 : ℤ) ∧
    (∑ n ∈ Ico 187904 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1071560640140554468712172750 : ℤ) := by
  rcases cdemPrefixStats_187904_188160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_188160_188416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187904 ≤ 188160) (by norm_num : 188160 ≤ 188416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187904 ≤ 188160) (by norm_num : 188160 ≤ 188416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187904 ≤ 188160) (by norm_num : 188160 ≤ 188416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187904 ≤ 188160) (by norm_num : 188160 ≤ 188416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_187392_188416 :
    (∑ n ∈ Ico 187392 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 187392 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 187392 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (319405 : ℤ) ∧
    (∑ n ∈ Ico 187392 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6388247083163945489241561061 : ℤ) := by
  rcases cdemPrefixStats_187392_187904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187904_188416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 187392 ≤ 187904) (by norm_num : 187904 ≤ 188416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 187392 ≤ 187904) (by norm_num : 187904 ≤ 188416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187904) (by norm_num : 187904 ≤ 188416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 187392 ≤ 187904) (by norm_num : 187904 ≤ 188416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_186368_188416 :
    (∑ n ∈ Ico 186368 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 186368 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1239 : ℕ) ∧
    (∑ n ∈ Ico 186368 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (81135 : ℤ) ∧
    (∑ n ∈ Ico 186368 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1622640086488290380604129878 : ℤ) := by
  rcases cdemPrefixStats_186368_187392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_187392_188416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 186368 ≤ 187392) (by norm_num : 187392 ≤ 188416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 186368 ≤ 187392) (by norm_num : 187392 ≤ 188416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 187392) (by norm_num : 187392 ≤ 188416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 186368 ≤ 187392) (by norm_num : 187392 ≤ 188416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_184320_188416 :
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2488 : ℕ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381835 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7636878746389338738820734466 : ℤ) := by
  rcases cdemPrefixStats_184320_186368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_186368_188416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 184320 ≤ 186368) (by norm_num : 186368 ≤ 188416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 184320 ≤ 186368) (by norm_num : 186368 ≤ 188416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 186368) (by norm_num : 186368 ≤ 188416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 184320 ≤ 186368) (by norm_num : 186368 ≤ 188416), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup045_checked_complete :
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2488 : ℕ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381835 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7636878746389338738820734466 : ℤ) := cdemPrefixStats_184320_188416
end Helfgott
#print axioms Helfgott.cdemPrefixGroup045_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2488 : ℕ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381835 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7636878746389338738820734466 : ℤ) := Helfgott.cdemPrefixGroup045_checked_complete
#print axioms solution
