-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup047_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:57:19.104991+00:00
-- url     : https://prove2.me/submissions/1a98353e-613d-4cd6-af8f-5a0074d5931d

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
private theorem cdemPrefixStats_192512_192576 :
    (∑ n ∈ Ico 192512 192576, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 192512 192576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 192512 192576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51933 : ℤ) ∧
    (∑ n ∈ Ico 192512 192576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1038634610497897202126061680 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192576_192640 :
    (∑ n ∈ Ico 192576 192640, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 192576 192640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 192576 192640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-259576 : ℤ) ∧
    (∑ n ∈ Ico 192576 192640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5191590494804057870004100890 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192512_192640 :
    (∑ n ∈ Ico 192512 192640, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 192512 192640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 192512 192640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-311509 : ℤ) ∧
    (∑ n ∈ Ico 192512 192640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6230225105301955072130162570 : ℤ) := by
  rcases cdemPrefixStats_192512_192576 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192576_192640 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192512 ≤ 192576) (by norm_num : 192576 ≤ 192640), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192512 ≤ 192576) (by norm_num : 192576 ≤ 192640), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 192576) (by norm_num : 192576 ≤ 192640), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 192576) (by norm_num : 192576 ≤ 192640), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192640_192704 :
    (∑ n ∈ Ico 192640 192704, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 192640 192704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 192640 192704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (259512 : ℤ) ∧
    (∑ n ∈ Ico 192640 192704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5190348295542610005055235471 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192704_192768 :
    (∑ n ∈ Ico 192704 192768, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 192704 192768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 192704 192768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103741 : ℤ) ∧
    (∑ n ∈ Ico 192704 192768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2074844640592816641466325815 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192640_192768 :
    (∑ n ∈ Ico 192640 192768, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 192640 192768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 192640 192768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (155771 : ℤ) ∧
    (∑ n ∈ Ico 192640 192768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3115503654949793363588909656 : ℤ) := by
  rcases cdemPrefixStats_192640_192704 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192704_192768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192640 ≤ 192704) (by norm_num : 192704 ≤ 192768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192640 ≤ 192704) (by norm_num : 192704 ≤ 192768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192640 ≤ 192704) (by norm_num : 192704 ≤ 192768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192640 ≤ 192704) (by norm_num : 192704 ≤ 192768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192512_192768 :
    (∑ n ∈ Ico 192512 192768, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 192512 192768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 192512 192768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155738 : ℤ) ∧
    (∑ n ∈ Ico 192512 192768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3114721450352161708541252914 : ℤ) := by
  rcases cdemPrefixStats_192512_192640 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192640_192768 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192512 ≤ 192640) (by norm_num : 192640 ≤ 192768), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192512 ≤ 192640) (by norm_num : 192640 ≤ 192768), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 192640) (by norm_num : 192640 ≤ 192768), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 192640) (by norm_num : 192640 ≤ 192768), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192768_192832 :
    (∑ n ∈ Ico 192768 192832, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 192768 192832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 192768 192832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25941 : ℤ) ∧
    (∑ n ∈ Ico 192768 192832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-518771695178852973427085213 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192832_192896 :
    (∑ n ∈ Ico 192832 192896, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 192832 192896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 192832 192896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-311073 : ℤ) ∧
    (∑ n ∈ Ico 192832 192896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6221592384073842262702381460 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192768_192896 :
    (∑ n ∈ Ico 192768 192896, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 192768 192896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 192768 192896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-337014 : ℤ) ∧
    (∑ n ∈ Ico 192768 192896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6740364079252695236129466673 : ℤ) := by
  rcases cdemPrefixStats_192768_192832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192832_192896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192768 ≤ 192832) (by norm_num : 192832 ≤ 192896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192768 ≤ 192832) (by norm_num : 192832 ≤ 192896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192768 ≤ 192832) (by norm_num : 192832 ≤ 192896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192768 ≤ 192832) (by norm_num : 192832 ≤ 192896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192896_192960 :
    (∑ n ∈ Ico 192896 192960, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 192896 192960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 192896 192960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129570 : ℤ) ∧
    (∑ n ∈ Ico 192896 192960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2591430918083502671040388835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192960_193024 :
    (∑ n ∈ Ico 192960 193024, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 192960 193024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 192960 193024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25914 : ℤ) ∧
    (∑ n ∈ Ico 192960 193024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-518298483891914530420884710 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_192896_193024 :
    (∑ n ∈ Ico 192896 193024, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 192896 193024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 192896 193024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (103656 : ℤ) ∧
    (∑ n ∈ Ico 192896 193024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2073132434191588140619504125 : ℤ) := by
  rcases cdemPrefixStats_192896_192960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192960_193024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192896 ≤ 192960) (by norm_num : 192960 ≤ 193024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192896 ≤ 192960) (by norm_num : 192960 ≤ 193024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192896 ≤ 192960) (by norm_num : 192960 ≤ 193024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192896 ≤ 192960) (by norm_num : 192960 ≤ 193024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192768_193024 :
    (∑ n ∈ Ico 192768 193024, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 192768 193024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 192768 193024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-233358 : ℤ) ∧
    (∑ n ∈ Ico 192768 193024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4667231645061107095509962548 : ℤ) := by
  rcases cdemPrefixStats_192768_192896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192896_193024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192768 ≤ 192896) (by norm_num : 192896 ≤ 193024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192768 ≤ 192896) (by norm_num : 192896 ≤ 193024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192768 ≤ 192896) (by norm_num : 192896 ≤ 193024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192768 ≤ 192896) (by norm_num : 192896 ≤ 193024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192512_193024 :
    (∑ n ∈ Ico 192512 193024, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 192512 193024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 192512 193024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-389096 : ℤ) ∧
    (∑ n ∈ Ico 192512 193024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7781953095413268804051215462 : ℤ) := by
  rcases cdemPrefixStats_192512_192768 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_192768_193024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192512 ≤ 192768) (by norm_num : 192768 ≤ 193024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192512 ≤ 192768) (by norm_num : 192768 ≤ 193024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 192768) (by norm_num : 192768 ≤ 193024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 192768) (by norm_num : 192768 ≤ 193024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193024_193088 :
    (∑ n ∈ Ico 193024 193088, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 193024 193088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 193024 193088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (103603 : ℤ) ∧
    (∑ n ∈ Ico 193024 193088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2072028927084209253372852425 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193088_193152 :
    (∑ n ∈ Ico 193088 193152, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 193088 193152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193088 193152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232996 : ℤ) ∧
    (∑ n ∈ Ico 193088 193152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4660044076044926558662959951 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193024_193152 :
    (∑ n ∈ Ico 193024 193152, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 193024 193152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 193024 193152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-129393 : ℤ) ∧
    (∑ n ∈ Ico 193024 193152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2588015148960717305290107526 : ℤ) := by
  rcases cdemPrefixStats_193024_193088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193088_193152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193024 ≤ 193088) (by norm_num : 193088 ≤ 193152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193024 ≤ 193088) (by norm_num : 193088 ≤ 193152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193024 ≤ 193088) (by norm_num : 193088 ≤ 193152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193024 ≤ 193088) (by norm_num : 193088 ≤ 193152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193152_193216 :
    (∑ n ∈ Ico 193152 193216, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 193152 193216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193152 193216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25856 : ℤ) ∧
    (∑ n ∈ Ico 193152 193216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (517110721028060414933656315 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193216_193280 :
    (∑ n ∈ Ico 193216 193280, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 193216 193280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193216 193280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232879 : ℤ) ∧
    (∑ n ∈ Ico 193216 193280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4657656491352386887706197304 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193152_193280 :
    (∑ n ∈ Ico 193152 193280, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 193152 193280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 193152 193280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-207023 : ℤ) ∧
    (∑ n ∈ Ico 193152 193280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4140545770324326472772540989 : ℤ) := by
  rcases cdemPrefixStats_193152_193216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193216_193280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193152 ≤ 193216) (by norm_num : 193216 ≤ 193280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193152 ≤ 193216) (by norm_num : 193216 ≤ 193280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193152 ≤ 193216) (by norm_num : 193216 ≤ 193280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193152 ≤ 193216) (by norm_num : 193216 ≤ 193280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193024_193280 :
    (∑ n ∈ Ico 193024 193280, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 193024 193280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 193024 193280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-336416 : ℤ) ∧
    (∑ n ∈ Ico 193024 193280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6728560919285043778062648515 : ℤ) := by
  rcases cdemPrefixStats_193024_193152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193152_193280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193024 ≤ 193152) (by norm_num : 193152 ≤ 193280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193024 ≤ 193152) (by norm_num : 193152 ≤ 193280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193024 ≤ 193152) (by norm_num : 193152 ≤ 193280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193024 ≤ 193152) (by norm_num : 193152 ≤ 193280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193280_193344 :
    (∑ n ∈ Ico 193280 193344, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 193280 193344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193280 193344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77606 : ℤ) ∧
    (∑ n ∈ Ico 193280 193344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1552171050949414563287460413 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193344_193408 :
    (∑ n ∈ Ico 193344 193408, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 193344 193408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 193344 193408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103417 : ℤ) ∧
    (∑ n ∈ Ico 193344 193408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2068418097989504212360467334 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193280_193408 :
    (∑ n ∈ Ico 193280 193408, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 193280 193408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 193280 193408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-181023 : ℤ) ∧
    (∑ n ∈ Ico 193280 193408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3620589148938918775647927747 : ℤ) := by
  rcases cdemPrefixStats_193280_193344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193344_193408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193280 ≤ 193344) (by norm_num : 193344 ≤ 193408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193280 ≤ 193344) (by norm_num : 193344 ≤ 193408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193280 ≤ 193344) (by norm_num : 193344 ≤ 193408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193280 ≤ 193344) (by norm_num : 193344 ≤ 193408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193408_193472 :
    (∑ n ∈ Ico 193408 193472, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 193408 193472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 193408 193472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103392 : ℤ) ∧
    (∑ n ∈ Ico 193408 193472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2067880770681473391902380795 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193472_193536 :
    (∑ n ∈ Ico 193472 193536, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 193472 193536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 193472 193536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129185 : ℤ) ∧
    (∑ n ∈ Ico 193472 193536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2583661582987494095449599893 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193408_193536 :
    (∑ n ∈ Ico 193408 193536, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 193408 193536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 193408 193536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25793 : ℤ) ∧
    (∑ n ∈ Ico 193408 193536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (515780812306020703547219098 : ℤ) := by
  rcases cdemPrefixStats_193408_193472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193472_193536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193408 ≤ 193472) (by norm_num : 193472 ≤ 193536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193408 ≤ 193472) (by norm_num : 193472 ≤ 193536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193408 ≤ 193472) (by norm_num : 193472 ≤ 193536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193408 ≤ 193472) (by norm_num : 193472 ≤ 193536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193280_193536 :
    (∑ n ∈ Ico 193280 193536, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 193280 193536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 193280 193536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155230 : ℤ) ∧
    (∑ n ∈ Ico 193280 193536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3104808336632898072100708649 : ℤ) := by
  rcases cdemPrefixStats_193280_193408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193408_193536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193280 ≤ 193408) (by norm_num : 193408 ≤ 193536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193280 ≤ 193408) (by norm_num : 193408 ≤ 193536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193280 ≤ 193408) (by norm_num : 193408 ≤ 193536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193280 ≤ 193408) (by norm_num : 193408 ≤ 193536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193024_193536 :
    (∑ n ∈ Ico 193024 193536, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 193024 193536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 193024 193536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-491646 : ℤ) ∧
    (∑ n ∈ Ico 193024 193536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9833369255917941850163357164 : ℤ) := by
  rcases cdemPrefixStats_193024_193280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193280_193536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193024 ≤ 193280) (by norm_num : 193280 ≤ 193536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193024 ≤ 193280) (by norm_num : 193280 ≤ 193536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193024 ≤ 193280) (by norm_num : 193280 ≤ 193536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193024 ≤ 193280) (by norm_num : 193280 ≤ 193536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192512_193536 :
    (∑ n ∈ Ico 192512 193536, mobiusTreeValue 16 mobiusTable1200001 n) = (-34 : ℤ) ∧
    (∑ n ∈ Ico 192512 193536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 192512 193536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-880742 : ℤ) ∧
    (∑ n ∈ Ico 192512 193536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17615322351331210654214572626 : ℤ) := by
  rcases cdemPrefixStats_192512_193024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193024_193536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192512 ≤ 193024) (by norm_num : 193024 ≤ 193536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192512 ≤ 193024) (by norm_num : 193024 ≤ 193536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 193024) (by norm_num : 193024 ≤ 193536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 193024) (by norm_num : 193024 ≤ 193536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193536_193600 :
    (∑ n ∈ Ico 193536 193600, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 193536 193600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 193536 193600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103304 : ℤ) ∧
    (∑ n ∈ Ico 193536 193600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2066091638023442552719080819 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193600_193664 :
    (∑ n ∈ Ico 193600 193664, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 193600 193664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193600 193664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25789 : ℤ) ∧
    (∑ n ∈ Ico 193600 193664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (515755417593026308114142415 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193536_193664 :
    (∑ n ∈ Ico 193536 193664, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 193536 193664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 193536 193664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77515 : ℤ) ∧
    (∑ n ∈ Ico 193536 193664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1550336220430416244604938404 : ℤ) := by
  rcases cdemPrefixStats_193536_193600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193600_193664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193536 ≤ 193600) (by norm_num : 193600 ≤ 193664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193536 ≤ 193600) (by norm_num : 193600 ≤ 193664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 193600) (by norm_num : 193600 ≤ 193664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 193600) (by norm_num : 193600 ≤ 193664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193664_193728 :
    (∑ n ∈ Ico 193664 193728, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 193664 193728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193664 193728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (129065 : ℤ) ∧
    (∑ n ∈ Ico 193664 193728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2581361917089998171571365498 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193728_193792 :
    (∑ n ∈ Ico 193728 193792, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 193728 193792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 193728 193792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51596 : ℤ) ∧
    (∑ n ∈ Ico 193728 193792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1031938439479375675989825280 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193664_193792 :
    (∑ n ∈ Ico 193664 193792, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 193664 193792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 193664 193792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77469 : ℤ) ∧
    (∑ n ∈ Ico 193664 193792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1549423477610622495581540218 : ℤ) := by
  rcases cdemPrefixStats_193664_193728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193728_193792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193664 ≤ 193728) (by norm_num : 193728 ≤ 193792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193664 ≤ 193728) (by norm_num : 193728 ≤ 193792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193664 ≤ 193728) (by norm_num : 193728 ≤ 193792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193664 ≤ 193728) (by norm_num : 193728 ≤ 193792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193536_193792 :
    (∑ n ∈ Ico 193536 193792, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 193536 193792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 193536 193792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 193536 193792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-912742819793749023398186 : ℤ) := by
  rcases cdemPrefixStats_193536_193664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193664_193792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193536 ≤ 193664) (by norm_num : 193664 ≤ 193792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193536 ≤ 193664) (by norm_num : 193664 ≤ 193792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 193664) (by norm_num : 193664 ≤ 193792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 193664) (by norm_num : 193664 ≤ 193792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193792_193856 :
    (∑ n ∈ Ico 193792 193856, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 193792 193856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 193792 193856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103183 : ℤ) ∧
    (∑ n ∈ Ico 193792 193856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2063682709769442473413027124 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193856_193920 :
    (∑ n ∈ Ico 193856 193920, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 193856 193920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193856 193920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (180506 : ℤ) ∧
    (∑ n ∈ Ico 193856 193920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3610153560597738988793555408 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193792_193920 :
    (∑ n ∈ Ico 193792 193920, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 193792 193920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 193792 193920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77323 : ℤ) ∧
    (∑ n ∈ Ico 193792 193920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1546470850828296515380528284 : ℤ) := by
  rcases cdemPrefixStats_193792_193856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193856_193920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193792 ≤ 193856) (by norm_num : 193856 ≤ 193920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193792 ≤ 193856) (by norm_num : 193856 ≤ 193920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193792 ≤ 193856) (by norm_num : 193856 ≤ 193920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193792 ≤ 193856) (by norm_num : 193856 ≤ 193920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193920_193984 :
    (∑ n ∈ Ico 193920 193984, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 193920 193984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 193920 193984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-232041 : ℤ) ∧
    (∑ n ∈ Ico 193920 193984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4640932170155136608709490879 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193984_194048 :
    (∑ n ∈ Ico 193984 194048, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 193984 194048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 193984 194048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51562 : ℤ) ∧
    (∑ n ∈ Ico 193984 194048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1031230696872874928534502870 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_193920_194048 :
    (∑ n ∈ Ico 193920 194048, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 193920 194048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 193920 194048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-180479 : ℤ) ∧
    (∑ n ∈ Ico 193920 194048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3609701473282261680174988009 : ℤ) := by
  rcases cdemPrefixStats_193920_193984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193984_194048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193920 ≤ 193984) (by norm_num : 193984 ≤ 194048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193920 ≤ 193984) (by norm_num : 193984 ≤ 194048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193920 ≤ 193984) (by norm_num : 193984 ≤ 194048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193920 ≤ 193984) (by norm_num : 193984 ≤ 194048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193792_194048 :
    (∑ n ∈ Ico 193792 194048, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 193792 194048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 193792 194048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103156 : ℤ) ∧
    (∑ n ∈ Ico 193792 194048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2063230622453965164794459725 : ℤ) := by
  rcases cdemPrefixStats_193792_193920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193920_194048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193792 ≤ 193920) (by norm_num : 193920 ≤ 194048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193792 ≤ 193920) (by norm_num : 193920 ≤ 194048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193792 ≤ 193920) (by norm_num : 193920 ≤ 194048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193792 ≤ 193920) (by norm_num : 193920 ≤ 194048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193536_194048 :
    (∑ n ∈ Ico 193536 194048, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 193536 194048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 193536 194048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-103202 : ℤ) ∧
    (∑ n ∈ Ico 193536 194048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2064143365273758913817857911 : ℤ) := by
  rcases cdemPrefixStats_193536_193792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193792_194048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193536 ≤ 193792) (by norm_num : 193792 ≤ 194048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193536 ≤ 193792) (by norm_num : 193792 ≤ 194048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 193792) (by norm_num : 193792 ≤ 194048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 193792) (by norm_num : 193792 ≤ 194048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194048_194112 :
    (∑ n ∈ Ico 194048 194112, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 194048 194112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 194048 194112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25754 : ℤ) ∧
    (∑ n ∈ Ico 194048 194112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-515081511623496490649721339 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194112_194176 :
    (∑ n ∈ Ico 194112 194176, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 194112 194176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 194112 194176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-257562 : ℤ) ∧
    (∑ n ∈ Ico 194112 194176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5151328023254507752021447320 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194048_194176 :
    (∑ n ∈ Ico 194048 194176, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 194048 194176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 194048 194176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-283316 : ℤ) ∧
    (∑ n ∈ Ico 194048 194176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5666409534878004242671168659 : ℤ) := by
  rcases cdemPrefixStats_194048_194112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194112_194176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194048 ≤ 194112) (by norm_num : 194112 ≤ 194176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194048 ≤ 194112) (by norm_num : 194112 ≤ 194176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194048 ≤ 194112) (by norm_num : 194112 ≤ 194176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194048 ≤ 194112) (by norm_num : 194112 ≤ 194176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194176_194240 :
    (∑ n ∈ Ico 194176 194240, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 194176 194240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 194176 194240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102994 : ℤ) ∧
    (∑ n ∈ Ico 194176 194240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2059925805300645712921750116 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194240_194304 :
    (∑ n ∈ Ico 194240 194304, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 194240 194304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 194240 194304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25764 : ℤ) ∧
    (∑ n ∈ Ico 194240 194304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (515311932360134474162790036 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194176_194304 :
    (∑ n ∈ Ico 194176 194304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 194176 194304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 194176 194304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77230 : ℤ) ∧
    (∑ n ∈ Ico 194176 194304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1544613872940511238758960080 : ℤ) := by
  rcases cdemPrefixStats_194176_194240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194240_194304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194176 ≤ 194240) (by norm_num : 194240 ≤ 194304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194176 ≤ 194240) (by norm_num : 194240 ≤ 194304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194176 ≤ 194240) (by norm_num : 194240 ≤ 194304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194176 ≤ 194240) (by norm_num : 194240 ≤ 194304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194048_194304 :
    (∑ n ∈ Ico 194048 194304, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 194048 194304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 194048 194304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-360546 : ℤ) ∧
    (∑ n ∈ Ico 194048 194304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7211023407818515481430128739 : ℤ) := by
  rcases cdemPrefixStats_194048_194176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194176_194304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194048 ≤ 194176) (by norm_num : 194176 ≤ 194304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194048 ≤ 194176) (by norm_num : 194176 ≤ 194304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194048 ≤ 194176) (by norm_num : 194176 ≤ 194304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194048 ≤ 194176) (by norm_num : 194176 ≤ 194304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194304_194368 :
    (∑ n ∈ Ico 194304 194368, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 194304 194368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 194304 194368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (334460 : ℤ) ∧
    (∑ n ∈ Ico 194304 194368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6689370971661166410361485071 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194368_194432 :
    (∑ n ∈ Ico 194368 194432, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 194368 194432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 194368 194432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 194368 194432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39672487841276202037758 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194304_194432 :
    (∑ n ∈ Ico 194304 194432, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 194304 194432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 194304 194432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (334457 : ℤ) ∧
    (∑ n ∈ Ico 194304 194432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6689331299173325134159447313 : ℤ) := by
  rcases cdemPrefixStats_194304_194368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194368_194432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194304 ≤ 194368) (by norm_num : 194368 ≤ 194432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194304 ≤ 194368) (by norm_num : 194368 ≤ 194432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194304 ≤ 194368) (by norm_num : 194368 ≤ 194432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194304 ≤ 194368) (by norm_num : 194368 ≤ 194432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194432_194496 :
    (∑ n ∈ Ico 194432 194496, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 194432 194496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 194432 194496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24 : ℤ) ∧
    (∑ n ∈ Ico 194432 194496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (431000571379879970339472 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194496_194560 :
    (∑ n ∈ Ico 194496 194560, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 194496 194560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 194496 194560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51427 : ℤ) ∧
    (∑ n ∈ Ico 194496 194560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1028502258025935401110983057 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194432_194560 :
    (∑ n ∈ Ico 194432 194560, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 194432 194560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 194432 194560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51403 : ℤ) ∧
    (∑ n ∈ Ico 194432 194560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1028071257454555521140643585 : ℤ) := by
  rcases cdemPrefixStats_194432_194496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194496_194560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194432 ≤ 194496) (by norm_num : 194496 ≤ 194560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194432 ≤ 194496) (by norm_num : 194496 ≤ 194560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194432 ≤ 194496) (by norm_num : 194496 ≤ 194560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194432 ≤ 194496) (by norm_num : 194496 ≤ 194560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194304_194560 :
    (∑ n ∈ Ico 194304 194560, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 194304 194560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 194304 194560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (283054 : ℤ) ∧
    (∑ n ∈ Ico 194304 194560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5661260041718769613018803728 : ℤ) := by
  rcases cdemPrefixStats_194304_194432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194432_194560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194304 ≤ 194432) (by norm_num : 194432 ≤ 194560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194304 ≤ 194432) (by norm_num : 194432 ≤ 194560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194304 ≤ 194432) (by norm_num : 194432 ≤ 194560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194304 ≤ 194432) (by norm_num : 194432 ≤ 194560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194048_194560 :
    (∑ n ∈ Ico 194048 194560, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 194048 194560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (307 : ℕ) ∧
    (∑ n ∈ Ico 194048 194560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77492 : ℤ) ∧
    (∑ n ∈ Ico 194048 194560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1549763366099745868411325011 : ℤ) := by
  rcases cdemPrefixStats_194048_194304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194304_194560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194048 ≤ 194304) (by norm_num : 194304 ≤ 194560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194048 ≤ 194304) (by norm_num : 194304 ≤ 194560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194048 ≤ 194304) (by norm_num : 194304 ≤ 194560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194048 ≤ 194304) (by norm_num : 194304 ≤ 194560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_193536_194560 :
    (∑ n ∈ Ico 193536 194560, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 193536 194560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 193536 194560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-180694 : ℤ) ∧
    (∑ n ∈ Ico 193536 194560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3613906731373504782229182922 : ℤ) := by
  rcases cdemPrefixStats_193536_194048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194048_194560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 193536 ≤ 194048) (by norm_num : 194048 ≤ 194560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 193536 ≤ 194048) (by norm_num : 194048 ≤ 194560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 194048) (by norm_num : 194048 ≤ 194560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 193536 ≤ 194048) (by norm_num : 194048 ≤ 194560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192512_194560 :
    (∑ n ∈ Ico 192512 194560, mobiusTreeValue 16 mobiusTable1200001 n) = (-41 : ℤ) ∧
    (∑ n ∈ Ico 192512 194560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1237 : ℕ) ∧
    (∑ n ∈ Ico 192512 194560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1061436 : ℤ) ∧
    (∑ n ∈ Ico 192512 194560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21229229082704715436443755548 : ℤ) := by
  rcases cdemPrefixStats_192512_193536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_193536_194560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192512 ≤ 193536) (by norm_num : 193536 ≤ 194560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192512 ≤ 193536) (by norm_num : 193536 ≤ 194560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 193536) (by norm_num : 193536 ≤ 194560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 193536) (by norm_num : 193536 ≤ 194560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194560_194624 :
    (∑ n ∈ Ico 194560 194624, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 194560 194624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 194560 194624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77071 : ℤ) ∧
    (∑ n ∈ Ico 194560 194624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1541420534316926726771007596 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194624_194688 :
    (∑ n ∈ Ico 194624 194688, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 194624 194688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 194624 194688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102736 : ℤ) ∧
    (∑ n ∈ Ico 194624 194688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2054714511627981311179363937 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194560_194688 :
    (∑ n ∈ Ico 194560 194688, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 194560 194688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 194560 194688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25665 : ℤ) ∧
    (∑ n ∈ Ico 194560 194688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-513293977311054584408356341 : ℤ) := by
  rcases cdemPrefixStats_194560_194624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194624_194688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194560 ≤ 194624) (by norm_num : 194624 ≤ 194688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194560 ≤ 194624) (by norm_num : 194624 ≤ 194688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 194624) (by norm_num : 194624 ≤ 194688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 194624) (by norm_num : 194624 ≤ 194688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194688_194752 :
    (∑ n ∈ Ico 194688 194752, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 194688 194752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 194688 194752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-205430 : ℤ) ∧
    (∑ n ∈ Ico 194688 194752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4108684985110140752778383671 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194752_194816 :
    (∑ n ∈ Ico 194752 194816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 194752 194816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 194752 194816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51359 : ℤ) ∧
    (∑ n ∈ Ico 194752 194816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1027200088345548340677324674 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194688_194816 :
    (∑ n ∈ Ico 194688 194816, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 194688 194816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 194688 194816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-154071 : ℤ) ∧
    (∑ n ∈ Ico 194688 194816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3081484896764592412101058997 : ℤ) := by
  rcases cdemPrefixStats_194688_194752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194752_194816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194688 ≤ 194752) (by norm_num : 194752 ≤ 194816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194688 ≤ 194752) (by norm_num : 194752 ≤ 194816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194688 ≤ 194752) (by norm_num : 194752 ≤ 194816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194688 ≤ 194752) (by norm_num : 194752 ≤ 194816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194560_194816 :
    (∑ n ∈ Ico 194560 194816, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 194560 194816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 194560 194816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-179736 : ℤ) ∧
    (∑ n ∈ Ico 194560 194816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3594778874075646996509415338 : ℤ) := by
  rcases cdemPrefixStats_194560_194688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194688_194816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194560 ≤ 194688) (by norm_num : 194688 ≤ 194816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194560 ≤ 194688) (by norm_num : 194688 ≤ 194816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 194688) (by norm_num : 194688 ≤ 194816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 194688) (by norm_num : 194688 ≤ 194816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194816_194880 :
    (∑ n ∈ Ico 194816 194880, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 194816 194880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 194816 194880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-128315 : ℤ) ∧
    (∑ n ∈ Ico 194816 194880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2566324146136938525591737426 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194880_194944 :
    (∑ n ∈ Ico 194880 194944, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 194880 194944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 194880 194944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51313 : ℤ) ∧
    (∑ n ∈ Ico 194880 194944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1026262032573145686809913928 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194816_194944 :
    (∑ n ∈ Ico 194816 194944, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 194816 194944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 194816 194944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-77002 : ℤ) ∧
    (∑ n ∈ Ico 194816 194944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1540062113563792838781823498 : ℤ) := by
  rcases cdemPrefixStats_194816_194880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194880_194944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194816 ≤ 194880) (by norm_num : 194880 ≤ 194944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194816 ≤ 194880) (by norm_num : 194880 ≤ 194944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194816 ≤ 194880) (by norm_num : 194880 ≤ 194944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194816 ≤ 194880) (by norm_num : 194880 ≤ 194944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194944_195008 :
    (∑ n ∈ Ico 194944 195008, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 194944 195008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 194944 195008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-179526 : ℤ) ∧
    (∑ n ∈ Ico 194944 195008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3590543195400297767466194835 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195008_195072 :
    (∑ n ∈ Ico 195008 195072, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 195008 195072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 195008 195072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-333255 : ℤ) ∧
    (∑ n ∈ Ico 195008 195072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6665196952739748193680882216 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_194944_195072 :
    (∑ n ∈ Ico 194944 195072, mobiusTreeValue 16 mobiusTable1200001 n) = (-20 : ℤ) ∧
    (∑ n ∈ Ico 194944 195072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 194944 195072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-512781 : ℤ) ∧
    (∑ n ∈ Ico 194944 195072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10255740148140045961147077051 : ℤ) := by
  rcases cdemPrefixStats_194944_195008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195008_195072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194944 ≤ 195008) (by norm_num : 195008 ≤ 195072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194944 ≤ 195008) (by norm_num : 195008 ≤ 195072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194944 ≤ 195008) (by norm_num : 195008 ≤ 195072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194944 ≤ 195008) (by norm_num : 195008 ≤ 195072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194816_195072 :
    (∑ n ∈ Ico 194816 195072, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 194816 195072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 194816 195072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-589783 : ℤ) ∧
    (∑ n ∈ Ico 194816 195072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11795802261703838799928900549 : ℤ) := by
  rcases cdemPrefixStats_194816_194944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194944_195072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194816 ≤ 194944) (by norm_num : 194944 ≤ 195072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194816 ≤ 194944) (by norm_num : 194944 ≤ 195072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194816 ≤ 194944) (by norm_num : 194944 ≤ 195072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194816 ≤ 194944) (by norm_num : 194944 ≤ 195072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194560_195072 :
    (∑ n ∈ Ico 194560 195072, mobiusTreeValue 16 mobiusTable1200001 n) = (-30 : ℤ) ∧
    (∑ n ∈ Ico 194560 195072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (316 : ℕ) ∧
    (∑ n ∈ Ico 194560 195072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-769519 : ℤ) ∧
    (∑ n ∈ Ico 194560 195072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15390581135779485796438315887 : ℤ) := by
  rcases cdemPrefixStats_194560_194816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194816_195072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194560 ≤ 194816) (by norm_num : 194816 ≤ 195072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194560 ≤ 194816) (by norm_num : 194816 ≤ 195072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 194816) (by norm_num : 194816 ≤ 195072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 194816) (by norm_num : 194816 ≤ 195072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195072_195136 :
    (∑ n ∈ Ico 195072 195136, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 195072 195136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 195072 195136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51253 : ℤ) ∧
    (∑ n ∈ Ico 195072 195136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1025083852652970633711383485 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195136_195200 :
    (∑ n ∈ Ico 195136 195200, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 195136 195200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 195136 195200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102475 : ℤ) ∧
    (∑ n ∈ Ico 195136 195200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2049550515384037687186860662 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195072_195200 :
    (∑ n ∈ Ico 195072 195200, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 195072 195200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 195072 195200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-153728 : ℤ) ∧
    (∑ n ∈ Ico 195072 195200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3074634368037008320898244147 : ℤ) := by
  rcases cdemPrefixStats_195072_195136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195136_195200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195072 ≤ 195136) (by norm_num : 195136 ≤ 195200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195072 ≤ 195136) (by norm_num : 195136 ≤ 195200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195072 ≤ 195136) (by norm_num : 195136 ≤ 195200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195072 ≤ 195136) (by norm_num : 195136 ≤ 195200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195200_195264 :
    (∑ n ∈ Ico 195200 195264, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 195200 195264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 195200 195264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (128079 : ℤ) ∧
    (∑ n ∈ Ico 195200 195264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2561601278288162417358379244 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195264_195328 :
    (∑ n ∈ Ico 195264 195328, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 195264 195328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 195264 195328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51184 : ℤ) ∧
    (∑ n ∈ Ico 195264 195328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1023771869725068216500399397 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195200_195328 :
    (∑ n ∈ Ico 195200 195328, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 195200 195328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 195200 195328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (179263 : ℤ) ∧
    (∑ n ∈ Ico 195200 195328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3585373148013230633858778641 : ℤ) := by
  rcases cdemPrefixStats_195200_195264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195264_195328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195200 ≤ 195264) (by norm_num : 195264 ≤ 195328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195200 ≤ 195264) (by norm_num : 195264 ≤ 195328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195200 ≤ 195264) (by norm_num : 195264 ≤ 195328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195200 ≤ 195264) (by norm_num : 195264 ≤ 195328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195072_195328 :
    (∑ n ∈ Ico 195072 195328, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 195072 195328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 195072 195328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25535 : ℤ) ∧
    (∑ n ∈ Ico 195072 195328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (510738779976222312960534494 : ℤ) := by
  rcases cdemPrefixStats_195072_195200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195200_195328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195072 ≤ 195200) (by norm_num : 195200 ≤ 195328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195072 ≤ 195200) (by norm_num : 195200 ≤ 195328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195072 ≤ 195200) (by norm_num : 195200 ≤ 195328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195072 ≤ 195200) (by norm_num : 195200 ≤ 195328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195328_195392 :
    (∑ n ∈ Ico 195328 195392, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 195328 195392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 195328 195392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (179151 : ℤ) ∧
    (∑ n ∈ Ico 195328 195392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3583070932838629182601476895 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195392_195456 :
    (∑ n ∈ Ico 195392 195456, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 195392 195456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 195392 195456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (102335 : ℤ) ∧
    (∑ n ∈ Ico 195392 195456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2046721601230893785408603842 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195328_195456 :
    (∑ n ∈ Ico 195328 195456, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 195328 195456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 195328 195456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (281486 : ℤ) ∧
    (∑ n ∈ Ico 195328 195456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5629792534069522968010080737 : ℤ) := by
  rcases cdemPrefixStats_195328_195392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195392_195456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195328 ≤ 195392) (by norm_num : 195392 ≤ 195456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195328 ≤ 195392) (by norm_num : 195392 ≤ 195456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195328 ≤ 195392) (by norm_num : 195392 ≤ 195456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195328 ≤ 195392) (by norm_num : 195392 ≤ 195456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195456_195520 :
    (∑ n ∈ Ico 195456 195520, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 195456 195520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 195456 195520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51157 : ℤ) ∧
    (∑ n ∈ Ico 195456 195520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1023156579974975123847232913 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195520_195584 :
    (∑ n ∈ Ico 195520 195584, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 195520 195584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 195520 195584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (204507 : ℤ) ∧
    (∑ n ∈ Ico 195520 195584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4090290521590442612705247354 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195456_195584 :
    (∑ n ∈ Ico 195456 195584, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 195456 195584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 195456 195584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (153350 : ℤ) ∧
    (∑ n ∈ Ico 195456 195584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3067133941615467488858014441 : ℤ) := by
  rcases cdemPrefixStats_195456_195520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195520_195584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195456 ≤ 195520) (by norm_num : 195520 ≤ 195584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195456 ≤ 195520) (by norm_num : 195520 ≤ 195584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195456 ≤ 195520) (by norm_num : 195520 ≤ 195584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195456 ≤ 195520) (by norm_num : 195520 ≤ 195584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195328_195584 :
    (∑ n ∈ Ico 195328 195584, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 195328 195584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 195328 195584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (434836 : ℤ) ∧
    (∑ n ∈ Ico 195328 195584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8696926475684990456868095178 : ℤ) := by
  rcases cdemPrefixStats_195328_195456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195456_195584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195328 ≤ 195456) (by norm_num : 195456 ≤ 195584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195328 ≤ 195456) (by norm_num : 195456 ≤ 195584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195328 ≤ 195456) (by norm_num : 195456 ≤ 195584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195328 ≤ 195456) (by norm_num : 195456 ≤ 195584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195072_195584 :
    (∑ n ∈ Ico 195072 195584, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 195072 195584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 195072 195584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (460371 : ℤ) ∧
    (∑ n ∈ Ico 195072 195584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9207665255661212769828629672 : ℤ) := by
  rcases cdemPrefixStats_195072_195328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195328_195584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195072 ≤ 195328) (by norm_num : 195328 ≤ 195584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195072 ≤ 195328) (by norm_num : 195328 ≤ 195584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195072 ≤ 195328) (by norm_num : 195328 ≤ 195584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195072 ≤ 195328) (by norm_num : 195328 ≤ 195584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194560_195584 :
    (∑ n ∈ Ico 194560 195584, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 194560 195584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (628 : ℕ) ∧
    (∑ n ∈ Ico 194560 195584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-309148 : ℤ) ∧
    (∑ n ∈ Ico 194560 195584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6182915880118273026609686215 : ℤ) := by
  rcases cdemPrefixStats_194560_195072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195072_195584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194560 ≤ 195072) (by norm_num : 195072 ≤ 195584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194560 ≤ 195072) (by norm_num : 195072 ≤ 195584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 195072) (by norm_num : 195072 ≤ 195584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 195072) (by norm_num : 195072 ≤ 195584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195584_195648 :
    (∑ n ∈ Ico 195584 195648, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 195584 195648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 195584 195648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (7 : ℤ) ∧
    (∑ n ∈ Ico 195584 195648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41777748531170535213599 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195648_195712 :
    (∑ n ∈ Ico 195648 195712, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 195648 195712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 195648 195712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15 : ℤ) ∧
    (∑ n ∈ Ico 195648 195712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (295066316596443686836207 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195584_195712 :
    (∑ n ∈ Ico 195584 195712, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 195584 195712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 195584 195712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (22 : ℤ) ∧
    (∑ n ∈ Ico 195584 195712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (336844065127614222049806 : ℤ) := by
  rcases cdemPrefixStats_195584_195648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195648_195712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195584 ≤ 195648) (by norm_num : 195648 ≤ 195712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195584 ≤ 195648) (by norm_num : 195648 ≤ 195712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 195648) (by norm_num : 195648 ≤ 195712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 195648) (by norm_num : 195648 ≤ 195712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195712_195776 :
    (∑ n ∈ Ico 195712 195776, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 195712 195776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 195712 195776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-153284 : ℤ) ∧
    (∑ n ∈ Ico 195712 195776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3065674310627648879344036922 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195776_195840 :
    (∑ n ∈ Ico 195776 195840, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 195776 195840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 195776 195840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102144 : ℤ) ∧
    (∑ n ∈ Ico 195776 195840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2042924439432981025494006827 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195712_195840 :
    (∑ n ∈ Ico 195712 195840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 195712 195840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 195712 195840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-255428 : ℤ) ∧
    (∑ n ∈ Ico 195712 195840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5108598750060629904838043749 : ℤ) := by
  rcases cdemPrefixStats_195712_195776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195776_195840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195712 ≤ 195776) (by norm_num : 195776 ≤ 195840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195712 ≤ 195776) (by norm_num : 195776 ≤ 195840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195712 ≤ 195776) (by norm_num : 195776 ≤ 195840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195712 ≤ 195776) (by norm_num : 195776 ≤ 195840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195584_195840 :
    (∑ n ∈ Ico 195584 195840, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 195584 195840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 195584 195840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-255406 : ℤ) ∧
    (∑ n ∈ Ico 195584 195840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5108261905995502290615993943 : ℤ) := by
  rcases cdemPrefixStats_195584_195712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195712_195840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195584 ≤ 195712) (by norm_num : 195712 ≤ 195840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195584 ≤ 195712) (by norm_num : 195712 ≤ 195840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 195712) (by norm_num : 195712 ≤ 195840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 195712) (by norm_num : 195712 ≤ 195840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195840_195904 :
    (∑ n ∈ Ico 195840 195904, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 195840 195904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 195840 195904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (102116 : ℤ) ∧
    (∑ n ∈ Ico 195840 195904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2042301156220237284261059481 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195904_195968 :
    (∑ n ∈ Ico 195904 195968, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 195904 195968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 195904 195968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25520 : ℤ) ∧
    (∑ n ∈ Ico 195904 195968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-510438445474695544957611969 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195840_195968 :
    (∑ n ∈ Ico 195840 195968, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 195840 195968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 195840 195968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76596 : ℤ) ∧
    (∑ n ∈ Ico 195840 195968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1531862710745541739303447512 : ℤ) := by
  rcases cdemPrefixStats_195840_195904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195904_195968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195840 ≤ 195904) (by norm_num : 195904 ≤ 195968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195840 ≤ 195904) (by norm_num : 195904 ≤ 195968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195840 ≤ 195904) (by norm_num : 195904 ≤ 195968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195840 ≤ 195904) (by norm_num : 195904 ≤ 195968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195968_196032 :
    (∑ n ∈ Ico 195968 196032, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 195968 196032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 195968 196032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51015 : ℤ) ∧
    (∑ n ∈ Ico 195968 196032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1020278032693706339467472097 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196032_196096 :
    (∑ n ∈ Ico 196032 196096, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 196032 196096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 196032 196096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51024 : ℤ) ∧
    (∑ n ∈ Ico 196032 196096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1020504316312877700080033517 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_195968_196096 :
    (∑ n ∈ Ico 195968 196096, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 195968 196096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 195968 196096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102039 : ℤ) ∧
    (∑ n ∈ Ico 195968 196096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2040782349006584039547505614 : ℤ) := by
  rcases cdemPrefixStats_195968_196032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196032_196096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195968 ≤ 196032) (by norm_num : 196032 ≤ 196096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195968 ≤ 196032) (by norm_num : 196032 ≤ 196096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195968 ≤ 196032) (by norm_num : 196032 ≤ 196096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195968 ≤ 196032) (by norm_num : 196032 ≤ 196096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195840_196096 :
    (∑ n ∈ Ico 195840 196096, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 195840 196096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 195840 196096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25443 : ℤ) ∧
    (∑ n ∈ Ico 195840 196096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-508919638261042300244058102 : ℤ) := by
  rcases cdemPrefixStats_195840_195968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195968_196096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195840 ≤ 195968) (by norm_num : 195968 ≤ 196096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195840 ≤ 195968) (by norm_num : 195968 ≤ 196096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195840 ≤ 195968) (by norm_num : 195968 ≤ 196096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195840 ≤ 195968) (by norm_num : 195968 ≤ 196096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195584_196096 :
    (∑ n ∈ Ico 195584 196096, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 195584 196096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 195584 196096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-280849 : ℤ) ∧
    (∑ n ∈ Ico 195584 196096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5617181544256544590860052045 : ℤ) := by
  rcases cdemPrefixStats_195584_195840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195840_196096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195584 ≤ 195840) (by norm_num : 195840 ≤ 196096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195584 ≤ 195840) (by norm_num : 195840 ≤ 196096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 195840) (by norm_num : 195840 ≤ 196096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 195840) (by norm_num : 195840 ≤ 196096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196096_196160 :
    (∑ n ∈ Ico 196096 196160, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 196096 196160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 196096 196160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76497 : ℤ) ∧
    (∑ n ∈ Ico 196096 196160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1529953862573497996921651466 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196160_196224 :
    (∑ n ∈ Ico 196160 196224, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 196160 196224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 196160 196224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50925 : ℤ) ∧
    (∑ n ∈ Ico 196160 196224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1018609390518560964834865401 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196096_196224 :
    (∑ n ∈ Ico 196096 196224, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 196096 196224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 196096 196224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127422 : ℤ) ∧
    (∑ n ∈ Ico 196096 196224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2548563253092058961756516867 : ℤ) := by
  rcases cdemPrefixStats_196096_196160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196160_196224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196096 ≤ 196160) (by norm_num : 196160 ≤ 196224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196096 ≤ 196160) (by norm_num : 196160 ≤ 196224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196096 ≤ 196160) (by norm_num : 196160 ≤ 196224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196096 ≤ 196160) (by norm_num : 196160 ≤ 196224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196224_196288 :
    (∑ n ∈ Ico 196224 196288, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 196224 196288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 196224 196288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (50949 : ℤ) ∧
    (∑ n ∈ Ico 196224 196288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1018949894757264760421476625 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196288_196352 :
    (∑ n ∈ Ico 196288 196352, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 196288 196352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196288 196352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25460 : ℤ) ∧
    (∑ n ∈ Ico 196288 196352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (509260886013602625558628220 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196224_196352 :
    (∑ n ∈ Ico 196224 196352, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 196224 196352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 196224 196352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (76409 : ℤ) ∧
    (∑ n ∈ Ico 196224 196352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1528210780770867385980104845 : ℤ) := by
  rcases cdemPrefixStats_196224_196288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196288_196352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196224 ≤ 196288) (by norm_num : 196288 ≤ 196352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196224 ≤ 196288) (by norm_num : 196288 ≤ 196352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196224 ≤ 196288) (by norm_num : 196288 ≤ 196352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196224 ≤ 196288) (by norm_num : 196288 ≤ 196352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196096_196352 :
    (∑ n ∈ Ico 196096 196352, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 196096 196352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 196096 196352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (203831 : ℤ) ∧
    (∑ n ∈ Ico 196096 196352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4076774033862926347736621712 : ℤ) := by
  rcases cdemPrefixStats_196096_196224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196224_196352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196096 ≤ 196224) (by norm_num : 196224 ≤ 196352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196096 ≤ 196224) (by norm_num : 196224 ≤ 196352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196096 ≤ 196224) (by norm_num : 196224 ≤ 196352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196096 ≤ 196224) (by norm_num : 196224 ≤ 196352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196352_196416 :
    (∑ n ∈ Ico 196352 196416, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 196352 196416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196352 196416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (280058 : ℤ) ∧
    (∑ n ∈ Ico 196352 196416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5601234726118566121610451236 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196416_196480 :
    (∑ n ∈ Ico 196416 196480, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 196416 196480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 196416 196480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-25434 : ℤ) ∧
    (∑ n ∈ Ico 196416 196480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-508667457166644273318807608 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196352_196480 :
    (∑ n ∈ Ico 196352 196480, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 196352 196480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 196352 196480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (254624 : ℤ) ∧
    (∑ n ∈ Ico 196352 196480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5092567268951921848291643628 : ℤ) := by
  rcases cdemPrefixStats_196352_196416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196416_196480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196352 ≤ 196416) (by norm_num : 196416 ≤ 196480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196352 ≤ 196416) (by norm_num : 196416 ≤ 196480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196352 ≤ 196416) (by norm_num : 196416 ≤ 196480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196352 ≤ 196416) (by norm_num : 196416 ≤ 196480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196480_196544 :
    (∑ n ∈ Ico 196480 196544, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 196480 196544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 196480 196544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-152646 : ℤ) ∧
    (∑ n ∈ Ico 196480 196544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3053002678442728543063172594 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196544_196608 :
    (∑ n ∈ Ico 196544 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 196544 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 196544 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-76318 : ℤ) ∧
    (∑ n ∈ Ico 196544 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1526360244972942012404084394 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_196480_196608 :
    (∑ n ∈ Ico 196480 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 196480 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 196480 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-228964 : ℤ) ∧
    (∑ n ∈ Ico 196480 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4579362923415670555467256988 : ℤ) := by
  rcases cdemPrefixStats_196480_196544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196544_196608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196480 ≤ 196544) (by norm_num : 196544 ≤ 196608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196480 ≤ 196544) (by norm_num : 196544 ≤ 196608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196480 ≤ 196544) (by norm_num : 196544 ≤ 196608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196480 ≤ 196544) (by norm_num : 196544 ≤ 196608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196352_196608 :
    (∑ n ∈ Ico 196352 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 196352 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 196352 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (25660 : ℤ) ∧
    (∑ n ∈ Ico 196352 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (513204345536251292824386640 : ℤ) := by
  rcases cdemPrefixStats_196352_196480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196480_196608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196352 ≤ 196480) (by norm_num : 196480 ≤ 196608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196352 ≤ 196480) (by norm_num : 196480 ≤ 196608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196352 ≤ 196480) (by norm_num : 196480 ≤ 196608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196352 ≤ 196480) (by norm_num : 196480 ≤ 196608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_196096_196608 :
    (∑ n ∈ Ico 196096 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 196096 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 196096 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (229491 : ℤ) ∧
    (∑ n ∈ Ico 196096 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4589978379399177640561008352 : ℤ) := by
  rcases cdemPrefixStats_196096_196352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196352_196608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 196096 ≤ 196352) (by norm_num : 196352 ≤ 196608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 196096 ≤ 196352) (by norm_num : 196352 ≤ 196608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 196096 ≤ 196352) (by norm_num : 196352 ≤ 196608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 196096 ≤ 196352) (by norm_num : 196352 ≤ 196608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_195584_196608 :
    (∑ n ∈ Ico 195584 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 195584 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 195584 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51358 : ℤ) ∧
    (∑ n ∈ Ico 195584 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1027203164857366950299043693 : ℤ) := by
  rcases cdemPrefixStats_195584_196096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_196096_196608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 195584 ≤ 196096) (by norm_num : 196096 ≤ 196608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 195584 ≤ 196096) (by norm_num : 196096 ≤ 196608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 196096) (by norm_num : 196096 ≤ 196608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 195584 ≤ 196096) (by norm_num : 196096 ≤ 196608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_194560_196608 :
    (∑ n ∈ Ico 194560 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 194560 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1246 : ℕ) ∧
    (∑ n ∈ Ico 194560 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-360506 : ℤ) ∧
    (∑ n ∈ Ico 194560 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7210119044975639976908729908 : ℤ) := by
  rcases cdemPrefixStats_194560_195584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_195584_196608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 194560 ≤ 195584) (by norm_num : 195584 ≤ 196608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 194560 ≤ 195584) (by norm_num : 195584 ≤ 196608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 195584) (by norm_num : 195584 ≤ 196608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 194560 ≤ 195584) (by norm_num : 195584 ≤ 196608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_192512_196608 :
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-55 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1421942 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28439348127680355413352485456 : ℤ) := by
  rcases cdemPrefixStats_192512_194560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_194560_196608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 192512 ≤ 194560) (by norm_num : 194560 ≤ 196608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 192512 ≤ 194560) (by norm_num : 194560 ≤ 196608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 194560) (by norm_num : 194560 ≤ 196608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 192512 ≤ 194560) (by norm_num : 194560 ≤ 196608), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup047_checked_complete :
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-55 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1421942 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28439348127680355413352485456 : ℤ) := cdemPrefixStats_192512_196608
end Helfgott
#print axioms Helfgott.cdemPrefixGroup047_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-55 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1421942 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28439348127680355413352485456 : ℤ) := Helfgott.cdemPrefixGroup047_checked_complete
#print axioms solution
