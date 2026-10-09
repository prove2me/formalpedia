-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup038_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:40:06.458273+00:00
-- url     : https://prove2.me/submissions/53ceb4ee-a0b0-4328-b3df-5e9c5316ed16

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
private theorem cdemPrefixStats_155648_155712 :
    (∑ n ∈ Ico 155648 155712, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 155648 155712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 155648 155712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-64271 : ℤ) ∧
    (∑ n ∈ Ico 155648 155712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1285445761858292118047333211 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155712_155776 :
    (∑ n ∈ Ico 155712 155776, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 155712 155776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 155712 155776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (64228 : ℤ) ∧
    (∑ n ∈ Ico 155712 155776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1284579163743288875259200887 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155648_155776 :
    (∑ n ∈ Ico 155648 155776, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 155648 155776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 155648 155776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 155648 155776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-866598115003242788132324 : ℤ) := by
  rcases cdemPrefixStats_155648_155712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155712_155776 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155648 ≤ 155712) (by norm_num : 155712 ≤ 155776), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155648 ≤ 155712) (by norm_num : 155712 ≤ 155776), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 155712) (by norm_num : 155712 ≤ 155776), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 155712) (by norm_num : 155712 ≤ 155776), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155776_155840 :
    (∑ n ∈ Ico 155776 155840, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 155776 155840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 155776 155840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-256687 : ℤ) ∧
    (∑ n ∈ Ico 155776 155840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5133820236428405009026876044 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155840_155904 :
    (∑ n ∈ Ico 155840 155904, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 155840 155904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 155840 155904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-320776 : ℤ) ∧
    (∑ n ∈ Ico 155840 155904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6415606907216481835298907255 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155776_155904 :
    (∑ n ∈ Ico 155776 155904, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 155776 155904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 155776 155904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-577463 : ℤ) ∧
    (∑ n ∈ Ico 155776 155904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11549427143644886844325783299 : ℤ) := by
  rcases cdemPrefixStats_155776_155840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155840_155904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155776 ≤ 155840) (by norm_num : 155840 ≤ 155904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155776 ≤ 155840) (by norm_num : 155840 ≤ 155904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155776 ≤ 155840) (by norm_num : 155840 ≤ 155904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155776 ≤ 155840) (by norm_num : 155840 ≤ 155904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155648_155904 :
    (∑ n ∈ Ico 155648 155904, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 155648 155904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 155648 155904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-577506 : ℤ) ∧
    (∑ n ∈ Ico 155648 155904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11550293741759890087113915623 : ℤ) := by
  rcases cdemPrefixStats_155648_155776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155776_155904 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155648 ≤ 155776) (by norm_num : 155776 ≤ 155904), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155648 ≤ 155776) (by norm_num : 155776 ≤ 155904), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 155776) (by norm_num : 155776 ≤ 155904), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 155776) (by norm_num : 155776 ≤ 155904), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155904_155968 :
    (∑ n ∈ Ico 155904 155968, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 155904 155968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 155904 155968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (513022 : ℤ) ∧
    (∑ n ∈ Ico 155904 155968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10260624021963959458111972647 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155968_156032 :
    (∑ n ∈ Ico 155968 156032, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 155968 156032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 155968 156032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32080 : ℤ) ∧
    (∑ n ∈ Ico 155968 156032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (641621534502151370996054711 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_155904_156032 :
    (∑ n ∈ Ico 155904 156032, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 155904 156032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 155904 156032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (545102 : ℤ) ∧
    (∑ n ∈ Ico 155904 156032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10902245556466110829108027358 : ℤ) := by
  rcases cdemPrefixStats_155904_155968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155968_156032 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155904 ≤ 155968) (by norm_num : 155968 ≤ 156032), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155904 ≤ 155968) (by norm_num : 155968 ≤ 156032), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155904 ≤ 155968) (by norm_num : 155968 ≤ 156032), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155904 ≤ 155968) (by norm_num : 155968 ≤ 156032), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156032_156096 :
    (∑ n ∈ Ico 156032 156096, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 156032 156096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 156032 156096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (64069 : ℤ) ∧
    (∑ n ∈ Ico 156032 156096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1281398233908265731756522580 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156096_156160 :
    (∑ n ∈ Ico 156096 156160, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 156096 156160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 156096 156160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96045 : ℤ) ∧
    (∑ n ∈ Ico 156096 156160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1920938300419038450305413000 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156032_156160 :
    (∑ n ∈ Ico 156032 156160, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 156032 156160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 156032 156160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (160114 : ℤ) ∧
    (∑ n ∈ Ico 156032 156160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3202336534327304182061935580 : ℤ) := by
  rcases cdemPrefixStats_156032_156096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156096_156160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156032 ≤ 156096) (by norm_num : 156096 ≤ 156160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156032 ≤ 156096) (by norm_num : 156096 ≤ 156160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156032 ≤ 156096) (by norm_num : 156096 ≤ 156160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156032 ≤ 156096) (by norm_num : 156096 ≤ 156160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155904_156160 :
    (∑ n ∈ Ico 155904 156160, mobiusTreeValue 16 mobiusTable1200001 n) = (22 : ℤ) ∧
    (∑ n ∈ Ico 155904 156160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 155904 156160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (705216 : ℤ) ∧
    (∑ n ∈ Ico 155904 156160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14104582090793415011169962938 : ℤ) := by
  rcases cdemPrefixStats_155904_156032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156032_156160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155904 ≤ 156032) (by norm_num : 156032 ≤ 156160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155904 ≤ 156032) (by norm_num : 156032 ≤ 156160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155904 ≤ 156032) (by norm_num : 156032 ≤ 156160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155904 ≤ 156032) (by norm_num : 156032 ≤ 156160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155648_156160 :
    (∑ n ∈ Ico 155648 156160, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 155648 156160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 155648 156160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127710 : ℤ) ∧
    (∑ n ∈ Ico 155648 156160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2554288349033524924056047315 : ℤ) := by
  rcases cdemPrefixStats_155648_155904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_155904_156160 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155648 ≤ 155904) (by norm_num : 155904 ≤ 156160), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155648 ≤ 155904) (by norm_num : 155904 ≤ 156160), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 155904) (by norm_num : 155904 ≤ 156160), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 155904) (by norm_num : 155904 ≤ 156160), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156160_156224 :
    (∑ n ∈ Ico 156160 156224, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 156160 156224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 156160 156224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (128070 : ℤ) ∧
    (∑ n ∈ Ico 156160 156224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2561450737946282178622099181 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156224_156288 :
    (∑ n ∈ Ico 156224 156288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 156224 156288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 156224 156288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-32013 : ℤ) ∧
    (∑ n ∈ Ico 156224 156288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-640303103642968047149297277 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156160_156288 :
    (∑ n ∈ Ico 156160 156288, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 156160 156288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 156160 156288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (96057 : ℤ) ∧
    (∑ n ∈ Ico 156160 156288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1921147634303314131472801904 : ℤ) := by
  rcases cdemPrefixStats_156160_156224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156224_156288 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156160 ≤ 156224) (by norm_num : 156224 ≤ 156288), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156160 ≤ 156224) (by norm_num : 156224 ≤ 156288), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156160 ≤ 156224) (by norm_num : 156224 ≤ 156288), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156160 ≤ 156224) (by norm_num : 156224 ≤ 156288), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156288_156352 :
    (∑ n ∈ Ico 156288 156352, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 156288 156352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 156288 156352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31941 : ℤ) ∧
    (∑ n ∈ Ico 156288 156352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (638849927243365420540447187 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156352_156416 :
    (∑ n ∈ Ico 156352 156416, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 156352 156416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 156352 156416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (95896 : ℤ) ∧
    (∑ n ∈ Ico 156352 156416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1917974546009146583042494420 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156288_156416 :
    (∑ n ∈ Ico 156288 156416, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 156288 156416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 156288 156416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127837 : ℤ) ∧
    (∑ n ∈ Ico 156288 156416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2556824473252512003582941607 : ℤ) := by
  rcases cdemPrefixStats_156288_156352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156352_156416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156288 ≤ 156352) (by norm_num : 156352 ≤ 156416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156288 ≤ 156352) (by norm_num : 156352 ≤ 156416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156288 ≤ 156352) (by norm_num : 156352 ≤ 156416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156288 ≤ 156352) (by norm_num : 156352 ≤ 156416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156160_156416 :
    (∑ n ∈ Ico 156160 156416, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 156160 156416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 156160 156416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223894 : ℤ) ∧
    (∑ n ∈ Ico 156160 156416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4477972107555826135055743511 : ℤ) := by
  rcases cdemPrefixStats_156160_156288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156288_156416 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156160 ≤ 156288) (by norm_num : 156288 ≤ 156416), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156160 ≤ 156288) (by norm_num : 156288 ≤ 156416), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156160 ≤ 156288) (by norm_num : 156288 ≤ 156416), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156160 ≤ 156288) (by norm_num : 156288 ≤ 156416), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156416_156480 :
    (∑ n ∈ Ico 156416 156480, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 156416 156480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 156416 156480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (159761 : ℤ) ∧
    (∑ n ∈ Ico 156416 156480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3195308543866674326089251049 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156480_156544 :
    (∑ n ∈ Ico 156480 156544, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 156480 156544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 156480 156544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (63861 : ℤ) ∧
    (∑ n ∈ Ico 156480 156544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1277208306911331882419394723 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156416_156544 :
    (∑ n ∈ Ico 156416 156544, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 156416 156544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 156416 156544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (223622 : ℤ) ∧
    (∑ n ∈ Ico 156416 156544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4472516850778006208508645772 : ℤ) := by
  rcases cdemPrefixStats_156416_156480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156480_156544 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156416 ≤ 156480) (by norm_num : 156480 ≤ 156544), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156416 ≤ 156480) (by norm_num : 156480 ≤ 156544), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156416 ≤ 156480) (by norm_num : 156480 ≤ 156544), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156416 ≤ 156480) (by norm_num : 156480 ≤ 156544), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156544_156608 :
    (∑ n ∈ Ico 156544 156608, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 156544 156608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 156544 156608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (255483 : ℤ) ∧
    (∑ n ∈ Ico 156544 156608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5109756052518688828820630444 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156608_156672 :
    (∑ n ∈ Ico 156608 156672, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 156608 156672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 156608 156672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31916 : ℤ) ∧
    (∑ n ∈ Ico 156608 156672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (638337253960236518971895497 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156544_156672 :
    (∑ n ∈ Ico 156544 156672, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 156544 156672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 156544 156672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (287399 : ℤ) ∧
    (∑ n ∈ Ico 156544 156672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5748093306478925347792525941 : ℤ) := by
  rcases cdemPrefixStats_156544_156608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156608_156672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156544 ≤ 156608) (by norm_num : 156608 ≤ 156672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156544 ≤ 156608) (by norm_num : 156608 ≤ 156672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156544 ≤ 156608) (by norm_num : 156608 ≤ 156672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156544 ≤ 156608) (by norm_num : 156608 ≤ 156672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156416_156672 :
    (∑ n ∈ Ico 156416 156672, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 156416 156672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 156416 156672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (511021 : ℤ) ∧
    (∑ n ∈ Ico 156416 156672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10220610157256931556301171713 : ℤ) := by
  rcases cdemPrefixStats_156416_156544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156544_156672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156416 ≤ 156544) (by norm_num : 156544 ≤ 156672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156416 ≤ 156544) (by norm_num : 156544 ≤ 156672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156416 ≤ 156544) (by norm_num : 156544 ≤ 156672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156416 ≤ 156544) (by norm_num : 156544 ≤ 156672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156160_156672 :
    (∑ n ∈ Ico 156160 156672, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 156160 156672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 156160 156672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (734915 : ℤ) ∧
    (∑ n ∈ Ico 156160 156672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14698582264812757691356915224 : ℤ) := by
  rcases cdemPrefixStats_156160_156416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156416_156672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156160 ≤ 156416) (by norm_num : 156416 ≤ 156672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156160 ≤ 156416) (by norm_num : 156416 ≤ 156672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156160 ≤ 156416) (by norm_num : 156416 ≤ 156672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156160 ≤ 156416) (by norm_num : 156416 ≤ 156672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155648_156672 :
    (∑ n ∈ Ico 155648 156672, mobiusTreeValue 16 mobiusTable1200001 n) = (27 : ℤ) ∧
    (∑ n ∈ Ico 155648 156672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 155648 156672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (862625 : ℤ) ∧
    (∑ n ∈ Ico 155648 156672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17252870613846282615412962539 : ℤ) := by
  rcases cdemPrefixStats_155648_156160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156160_156672 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155648 ≤ 156160) (by norm_num : 156160 ≤ 156672), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155648 ≤ 156160) (by norm_num : 156160 ≤ 156672), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 156160) (by norm_num : 156160 ≤ 156672), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 156160) (by norm_num : 156160 ≤ 156672), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156672_156736 :
    (∑ n ∈ Ico 156672 156736, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 156672 156736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 156672 156736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-287165 : ℤ) ∧
    (∑ n ∈ Ico 156672 156736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5743365251694534843942001627 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156736_156800 :
    (∑ n ∈ Ico 156736 156800, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 156736 156800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 156736 156800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-127530 : ℤ) ∧
    (∑ n ∈ Ico 156736 156800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2550641952060643991528004916 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156672_156800 :
    (∑ n ∈ Ico 156672 156800, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 156672 156800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 156672 156800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-414695 : ℤ) ∧
    (∑ n ∈ Ico 156672 156800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8294007203755178835470006543 : ℤ) := by
  rcases cdemPrefixStats_156672_156736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156736_156800 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156672 ≤ 156736) (by norm_num : 156736 ≤ 156800), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156672 ≤ 156736) (by norm_num : 156736 ≤ 156800), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 156736) (by norm_num : 156736 ≤ 156800), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 156736) (by norm_num : 156736 ≤ 156800), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156800_156864 :
    (∑ n ∈ Ico 156800 156864, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 156800 156864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 156800 156864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 156800 156864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-178732751687832561794198 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156864_156928 :
    (∑ n ∈ Ico 156864 156928, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 156864 156928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 156864 156928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159318 : ℤ) ∧
    (∑ n ∈ Ico 156864 156928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3186377564424382087760232955 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156800_156928 :
    (∑ n ∈ Ico 156800 156928, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 156800 156928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 156800 156928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159331 : ℤ) ∧
    (∑ n ∈ Ico 156800 156928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3186556297176069920322027153 : ℤ) := by
  rcases cdemPrefixStats_156800_156864 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156864_156928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156800 ≤ 156864) (by norm_num : 156864 ≤ 156928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156800 ≤ 156864) (by norm_num : 156864 ≤ 156928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156800 ≤ 156864) (by norm_num : 156864 ≤ 156928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156800 ≤ 156864) (by norm_num : 156864 ≤ 156928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156672_156928 :
    (∑ n ∈ Ico 156672 156928, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 156672 156928, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 156672 156928, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-574026 : ℤ) ∧
    (∑ n ∈ Ico 156672 156928, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11480563500931248755792033696 : ℤ) := by
  rcases cdemPrefixStats_156672_156800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156800_156928 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156672 ≤ 156800) (by norm_num : 156800 ≤ 156928), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156672 ≤ 156800) (by norm_num : 156800 ≤ 156928), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 156800) (by norm_num : 156800 ≤ 156928), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 156800) (by norm_num : 156800 ≤ 156928), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156928_156992 :
    (∑ n ∈ Ico 156928 156992, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 156928 156992, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 156928 156992, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (63711 : ℤ) ∧
    (∑ n ∈ Ico 156928 156992, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1274238522354330681137228995 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156992_157056 :
    (∑ n ∈ Ico 156992 157056, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 156992 157056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 156992 157056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222889 : ℤ) ∧
    (∑ n ∈ Ico 156992 157056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4457872792847145038365868750 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_156928_157056 :
    (∑ n ∈ Ico 156928 157056, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 156928 157056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 156928 157056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-159178 : ℤ) ∧
    (∑ n ∈ Ico 156928 157056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3183634270492814357228639755 : ℤ) := by
  rcases cdemPrefixStats_156928_156992 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156992_157056 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156928 ≤ 156992) (by norm_num : 156992 ≤ 157056), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156928 ≤ 156992) (by norm_num : 156992 ≤ 157056), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156928 ≤ 156992) (by norm_num : 156992 ≤ 157056), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156928 ≤ 156992) (by norm_num : 156992 ≤ 157056), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157056_157120 :
    (∑ n ∈ Ico 157056 157120, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 157056 157120, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 157056 157120, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (159142 : ℤ) ∧
    (∑ n ∈ Ico 157056 157120, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3182921172456208053812901879 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157120_157184 :
    (∑ n ∈ Ico 157120 157184, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 157120 157184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 157120 157184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127276 : ℤ) ∧
    (∑ n ∈ Ico 157120 157184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2545549372630486885812896827 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157056_157184 :
    (∑ n ∈ Ico 157056 157184, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 157056 157184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 157056 157184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (286418 : ℤ) ∧
    (∑ n ∈ Ico 157056 157184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5728470545086694939625798706 : ℤ) := by
  rcases cdemPrefixStats_157056_157120 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157120_157184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157056 ≤ 157120) (by norm_num : 157120 ≤ 157184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157056 ≤ 157120) (by norm_num : 157120 ≤ 157184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157056 ≤ 157120) (by norm_num : 157120 ≤ 157184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157056 ≤ 157120) (by norm_num : 157120 ≤ 157184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156928_157184 :
    (∑ n ∈ Ico 156928 157184, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 156928 157184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 156928 157184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127240 : ℤ) ∧
    (∑ n ∈ Ico 156928 157184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2544836274593880582397158951 : ℤ) := by
  rcases cdemPrefixStats_156928_157056 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157056_157184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156928 ≤ 157056) (by norm_num : 157056 ≤ 157184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156928 ≤ 157056) (by norm_num : 157056 ≤ 157184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156928 ≤ 157056) (by norm_num : 157056 ≤ 157184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156928 ≤ 157056) (by norm_num : 157056 ≤ 157184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156672_157184 :
    (∑ n ∈ Ico 156672 157184, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 156672 157184, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 156672 157184, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-446786 : ℤ) ∧
    (∑ n ∈ Ico 156672 157184, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8935727226337368173394874745 : ℤ) := by
  rcases cdemPrefixStats_156672_156928 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156928_157184 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156672 ≤ 156928) (by norm_num : 156928 ≤ 157184), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156672 ≤ 156928) (by norm_num : 156928 ≤ 157184), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 156928) (by norm_num : 156928 ≤ 157184), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 156928) (by norm_num : 156928 ≤ 157184), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157184_157248 :
    (∑ n ∈ Ico 157184 157248, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 157184 157248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157184 157248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318041 : ℤ) ∧
    (∑ n ∈ Ico 157184 157248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6360926599678751100407667779 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157248_157312 :
    (∑ n ∈ Ico 157248 157312, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 157248 157312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 157248 157312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-286108 : ℤ) ∧
    (∑ n ∈ Ico 157248 157312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5722242412425062596081789076 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157184_157312 :
    (∑ n ∈ Ico 157184 157312, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 157184 157312, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 157184 157312, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-604149 : ℤ) ∧
    (∑ n ∈ Ico 157184 157312, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12083169012103813696489456855 : ℤ) := by
  rcases cdemPrefixStats_157184_157248 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157248_157312 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157184 ≤ 157248) (by norm_num : 157248 ≤ 157312), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157184 ≤ 157248) (by norm_num : 157248 ≤ 157312), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157184 ≤ 157248) (by norm_num : 157248 ≤ 157312), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157184 ≤ 157248) (by norm_num : 157248 ≤ 157312), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157312_157376 :
    (∑ n ∈ Ico 157312 157376, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 157312 157376, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 157312 157376, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (127093 : ℤ) ∧
    (∑ n ∈ Ico 157312 157376, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2541905747319891454317407374 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157376_157440 :
    (∑ n ∈ Ico 157376 157440, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 157376 157440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157376 157440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-127004 : ℤ) ∧
    (∑ n ∈ Ico 157376 157440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2540169978619645797469763838 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157312_157440 :
    (∑ n ∈ Ico 157312 157440, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 157312 157440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 157312 157440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (89 : ℤ) ∧
    (∑ n ∈ Ico 157312 157440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1735768700245656847643536 : ℤ) := by
  rcases cdemPrefixStats_157312_157376 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157376_157440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157312 ≤ 157376) (by norm_num : 157376 ≤ 157440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157312 ≤ 157376) (by norm_num : 157376 ≤ 157440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157312 ≤ 157376) (by norm_num : 157376 ≤ 157440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157312 ≤ 157376) (by norm_num : 157376 ≤ 157440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157184_157440 :
    (∑ n ∈ Ico 157184 157440, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 157184 157440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 157184 157440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-604060 : ℤ) ∧
    (∑ n ∈ Ico 157184 157440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12081433243403568039641813319 : ℤ) := by
  rcases cdemPrefixStats_157184_157312 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157312_157440 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157184 ≤ 157312) (by norm_num : 157312 ≤ 157440), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157184 ≤ 157312) (by norm_num : 157312 ≤ 157440), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157184 ≤ 157312) (by norm_num : 157312 ≤ 157440), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157184 ≤ 157312) (by norm_num : 157312 ≤ 157440), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157440_157504 :
    (∑ n ∈ Ico 157440 157504, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 157440 157504, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157440 157504, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-317468 : ℤ) ∧
    (∑ n ∈ Ico 157440 157504, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6349488459836700533739503069 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157504_157568 :
    (∑ n ∈ Ico 157504 157568, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 157504 157568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 157504 157568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (95205 : ℤ) ∧
    (∑ n ∈ Ico 157504 157568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1904169514733123352143980849 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157440_157568 :
    (∑ n ∈ Ico 157440 157568, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 157440 157568, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 157440 157568, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-222263 : ℤ) ∧
    (∑ n ∈ Ico 157440 157568, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4445318945103577181595522220 : ℤ) := by
  rcases cdemPrefixStats_157440_157504 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157504_157568 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157440 ≤ 157504) (by norm_num : 157504 ≤ 157568), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157440 ≤ 157504) (by norm_num : 157504 ≤ 157568), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157440 ≤ 157504) (by norm_num : 157504 ≤ 157568), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157440 ≤ 157504) (by norm_num : 157504 ≤ 157568), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157568_157632 :
    (∑ n ∈ Ico 157568 157632, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 157568 157632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157568 157632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (190343 : ℤ) ∧
    (∑ n ∈ Ico 157568 157632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3806865132358144001935352907 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157632_157696 :
    (∑ n ∈ Ico 157632 157696, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 157632 157696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 157632 157696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-63466 : ℤ) ∧
    (∑ n ∈ Ico 157632 157696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1269324987176036932603674653 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157568_157696 :
    (∑ n ∈ Ico 157568 157696, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 157568 157696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 157568 157696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (126877 : ℤ) ∧
    (∑ n ∈ Ico 157568 157696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2537540145182107069331678254 : ℤ) := by
  rcases cdemPrefixStats_157568_157632 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157632_157696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157568 ≤ 157632) (by norm_num : 157632 ≤ 157696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157568 ≤ 157632) (by norm_num : 157632 ≤ 157696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157568 ≤ 157632) (by norm_num : 157632 ≤ 157696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157568 ≤ 157632) (by norm_num : 157632 ≤ 157696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157440_157696 :
    (∑ n ∈ Ico 157440 157696, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 157440 157696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 157440 157696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-95386 : ℤ) ∧
    (∑ n ∈ Ico 157440 157696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1907778799921470112263843966 : ℤ) := by
  rcases cdemPrefixStats_157440_157568 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157568_157696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157440 ≤ 157568) (by norm_num : 157568 ≤ 157696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157440 ≤ 157568) (by norm_num : 157568 ≤ 157696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157440 ≤ 157568) (by norm_num : 157568 ≤ 157696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157440 ≤ 157568) (by norm_num : 157568 ≤ 157696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157184_157696 :
    (∑ n ∈ Ico 157184 157696, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 157184 157696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 157184 157696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-699446 : ℤ) ∧
    (∑ n ∈ Ico 157184 157696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13989212043325038151905657285 : ℤ) := by
  rcases cdemPrefixStats_157184_157440 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157440_157696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157184 ≤ 157440) (by norm_num : 157440 ≤ 157696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157184 ≤ 157440) (by norm_num : 157440 ≤ 157696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157184 ≤ 157440) (by norm_num : 157440 ≤ 157696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157184 ≤ 157440) (by norm_num : 157440 ≤ 157696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_156672_157696 :
    (∑ n ∈ Ico 156672 157696, mobiusTreeValue 16 mobiusTable1200001 n) = (-36 : ℤ) ∧
    (∑ n ∈ Ico 156672 157696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (618 : ℕ) ∧
    (∑ n ∈ Ico 156672 157696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1146232 : ℤ) ∧
    (∑ n ∈ Ico 156672 157696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22924939269662406325300532030 : ℤ) := by
  rcases cdemPrefixStats_156672_157184 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157184_157696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 156672 ≤ 157184) (by norm_num : 157184 ≤ 157696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 156672 ≤ 157184) (by norm_num : 157184 ≤ 157696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 157184) (by norm_num : 157184 ≤ 157696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 156672 ≤ 157184) (by norm_num : 157184 ≤ 157696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155648_157696 :
    (∑ n ∈ Ico 155648 157696, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 155648 157696, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1241 : ℕ) ∧
    (∑ n ∈ Ico 155648 157696, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-283607 : ℤ) ∧
    (∑ n ∈ Ico 155648 157696, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5672068655816123709887569491 : ℤ) := by
  rcases cdemPrefixStats_155648_156672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_156672_157696 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155648 ≤ 156672) (by norm_num : 156672 ≤ 157696), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155648 ≤ 156672) (by norm_num : 156672 ≤ 157696), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 156672) (by norm_num : 156672 ≤ 157696), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 156672) (by norm_num : 156672 ≤ 157696), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157696_157760 :
    (∑ n ∈ Ico 157696 157760, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 157696 157760, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157696 157760, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (317018 : ℤ) ∧
    (∑ n ∈ Ico 157696 157760, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6340458606458048148684867545 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157760_157824 :
    (∑ n ∈ Ico 157760 157824, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 157760 157824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157760 157824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (63400 : ℤ) ∧
    (∑ n ∈ Ico 157760 157824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1268017510116864272251920416 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157696_157824 :
    (∑ n ∈ Ico 157696 157824, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 157696 157824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 157696 157824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (380418 : ℤ) ∧
    (∑ n ∈ Ico 157696 157824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7608476116574912420936787961 : ℤ) := by
  rcases cdemPrefixStats_157696_157760 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157760_157824 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157696 ≤ 157760) (by norm_num : 157760 ≤ 157824), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157696 ≤ 157760) (by norm_num : 157760 ≤ 157824), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 157760) (by norm_num : 157760 ≤ 157824), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 157760) (by norm_num : 157760 ≤ 157824), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157824_157888 :
    (∑ n ∈ Ico 157824 157888, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 157824 157888, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 157824 157888, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31648 : ℤ) ∧
    (∑ n ∈ Ico 157824 157888, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-632995123336537873314808013 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157888_157952 :
    (∑ n ∈ Ico 157888 157952, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 157888 157952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157888 157952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-253306 : ℤ) ∧
    (∑ n ∈ Ico 157888 157952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5066165005597021310164815726 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157824_157952 :
    (∑ n ∈ Ico 157824 157952, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 157824 157952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 157824 157952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-284954 : ℤ) ∧
    (∑ n ∈ Ico 157824 157952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5699160128933559183479623739 : ℤ) := by
  rcases cdemPrefixStats_157824_157888 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157888_157952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157824 ≤ 157888) (by norm_num : 157888 ≤ 157952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157824 ≤ 157888) (by norm_num : 157888 ≤ 157952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157824 ≤ 157888) (by norm_num : 157888 ≤ 157952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157824 ≤ 157888) (by norm_num : 157888 ≤ 157952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157696_157952 :
    (∑ n ∈ Ico 157696 157952, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 157696 157952, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 157696 157952, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (95464 : ℤ) ∧
    (∑ n ∈ Ico 157696 157952, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1909315987641353237457164222 : ℤ) := by
  rcases cdemPrefixStats_157696_157824 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157824_157952 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157696 ≤ 157824) (by norm_num : 157824 ≤ 157952), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157696 ≤ 157824) (by norm_num : 157824 ≤ 157952), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 157824) (by norm_num : 157824 ≤ 157952), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 157824) (by norm_num : 157824 ≤ 157952), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157952_158016 :
    (∑ n ∈ Ico 157952 158016, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 157952 158016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 157952 158016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (24 : ℤ) ∧
    (∑ n ∈ Ico 157952 158016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (424692334519494687035837 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158016_158080 :
    (∑ n ∈ Ico 158016 158080, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 158016 158080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 158016 158080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-63288 : ℤ) ∧
    (∑ n ∈ Ico 158016 158080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1265762587403443650173734386 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_157952_158080 :
    (∑ n ∈ Ico 157952 158080, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 157952 158080, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 157952 158080, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-63264 : ℤ) ∧
    (∑ n ∈ Ico 157952 158080, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1265337895068924155486698549 : ℤ) := by
  rcases cdemPrefixStats_157952_158016 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158016_158080 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157952 ≤ 158016) (by norm_num : 158016 ≤ 158080), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157952 ≤ 158016) (by norm_num : 158016 ≤ 158080), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157952 ≤ 158016) (by norm_num : 158016 ≤ 158080), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157952 ≤ 158016) (by norm_num : 158016 ≤ 158080), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158080_158144 :
    (∑ n ∈ Ico 158080 158144, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 158080 158144, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 158080 158144, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (11 : ℤ) ∧
    (∑ n ∈ Ico 158080 158144, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (171948218773871446551858 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158144_158208 :
    (∑ n ∈ Ico 158144 158208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 158144 158208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 158144 158208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (12 : ℤ) ∧
    (∑ n ∈ Ico 158144 158208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (315791609977243388434252 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158080_158208 :
    (∑ n ∈ Ico 158080 158208, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 158080 158208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 158080 158208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (23 : ℤ) ∧
    (∑ n ∈ Ico 158080 158208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (487739828751114834986110 : ℤ) := by
  rcases cdemPrefixStats_158080_158144 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158144_158208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158080 ≤ 158144) (by norm_num : 158144 ≤ 158208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158080 ≤ 158144) (by norm_num : 158144 ≤ 158208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158080 ≤ 158144) (by norm_num : 158144 ≤ 158208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158080 ≤ 158144) (by norm_num : 158144 ≤ 158208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157952_158208 :
    (∑ n ∈ Ico 157952 158208, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 157952 158208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 157952 158208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-63241 : ℤ) ∧
    (∑ n ∈ Ico 157952 158208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1264850155240173040651712439 : ℤ) := by
  rcases cdemPrefixStats_157952_158080 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158080_158208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157952 ≤ 158080) (by norm_num : 158080 ≤ 158208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157952 ≤ 158080) (by norm_num : 158080 ≤ 158208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157952 ≤ 158080) (by norm_num : 158080 ≤ 158208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157952 ≤ 158080) (by norm_num : 158080 ≤ 158208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157696_158208 :
    (∑ n ∈ Ico 157696 158208, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 157696 158208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 157696 158208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (32223 : ℤ) ∧
    (∑ n ∈ Ico 157696 158208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (644465832401180196805451783 : ℤ) := by
  rcases cdemPrefixStats_157696_157952 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157952_158208 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157696 ≤ 157952) (by norm_num : 157952 ≤ 158208), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157696 ≤ 157952) (by norm_num : 157952 ≤ 158208), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 157952) (by norm_num : 157952 ≤ 158208), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 157952) (by norm_num : 157952 ≤ 158208), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158208_158272 :
    (∑ n ∈ Ico 158208 158272, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 158208 158272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 158208 158272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-158004 : ℤ) ∧
    (∑ n ∈ Ico 158208 158272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3160228603210576225636001045 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158272_158336 :
    (∑ n ∈ Ico 158272 158336, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 158272 158336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 158272 158336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (284274 : ℤ) ∧
    (∑ n ∈ Ico 158272 158336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5685595087884640154698964062 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158208_158336 :
    (∑ n ∈ Ico 158208 158336, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 158208 158336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 158208 158336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (126270 : ℤ) ∧
    (∑ n ∈ Ico 158208 158336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2525366484674063929062963017 : ℤ) := by
  rcases cdemPrefixStats_158208_158272 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158272_158336 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158208 ≤ 158272) (by norm_num : 158272 ≤ 158336), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158208 ≤ 158272) (by norm_num : 158272 ≤ 158336), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158208 ≤ 158272) (by norm_num : 158272 ≤ 158336), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158208 ≤ 158272) (by norm_num : 158272 ≤ 158336), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158336_158400 :
    (∑ n ∈ Ico 158336 158400, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 158336 158400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 158336 158400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-252601 : ℤ) ∧
    (∑ n ∈ Ico 158336 158400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5052055951955797374246650889 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158400_158464 :
    (∑ n ∈ Ico 158400 158464, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 158400 158464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 158400 158464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (126214 : ℤ) ∧
    (∑ n ∈ Ico 158400 158464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2524276475296472312792587247 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158336_158464 :
    (∑ n ∈ Ico 158336 158464, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 158336 158464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 158336 158464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-126387 : ℤ) ∧
    (∑ n ∈ Ico 158336 158464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2527779476659325061454063642 : ℤ) := by
  rcases cdemPrefixStats_158336_158400 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158400_158464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158336 ≤ 158400) (by norm_num : 158400 ≤ 158464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158336 ≤ 158400) (by norm_num : 158400 ≤ 158464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158336 ≤ 158400) (by norm_num : 158400 ≤ 158464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158336 ≤ 158400) (by norm_num : 158400 ≤ 158464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158208_158464 :
    (∑ n ∈ Ico 158208 158464, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 158208 158464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 158208 158464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-117 : ℤ) ∧
    (∑ n ∈ Ico 158208 158464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2412991985261132391100625 : ℤ) := by
  rcases cdemPrefixStats_158208_158336 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158336_158464 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158208 ≤ 158336) (by norm_num : 158336 ≤ 158464), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158208 ≤ 158336) (by norm_num : 158336 ≤ 158464), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158208 ≤ 158336) (by norm_num : 158336 ≤ 158464), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158208 ≤ 158336) (by norm_num : 158336 ≤ 158464), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158464_158528 :
    (∑ n ∈ Ico 158464 158528, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 158464 158528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 158464 158528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (10 : ℤ) ∧
    (∑ n ∈ Ico 158464 158528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (139320418950036839531840 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158528_158592 :
    (∑ n ∈ Ico 158528 158592, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 158528 158592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 158528 158592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-189200 : ℤ) ∧
    (∑ n ∈ Ico 158528 158592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3784096371398987598542706272 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158464_158592 :
    (∑ n ∈ Ico 158464 158592, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 158464 158592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 158464 158592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-189190 : ℤ) ∧
    (∑ n ∈ Ico 158464 158592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3783957050980037561703174432 : ℤ) := by
  rcases cdemPrefixStats_158464_158528 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158528_158592 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158464 ≤ 158528) (by norm_num : 158528 ≤ 158592), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158464 ≤ 158528) (by norm_num : 158528 ≤ 158592), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158464 ≤ 158528) (by norm_num : 158528 ≤ 158592), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158464 ≤ 158528) (by norm_num : 158528 ≤ 158592), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158592_158656 :
    (∑ n ∈ Ico 158592 158656, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 158592 158656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 158592 158656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-42 : ℤ) ∧
    (∑ n ∈ Ico 158592 158656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-790875154825969130688131 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158656_158720 :
    (∑ n ∈ Ico 158656 158720, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 158656 158720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 158656 158720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (441101 : ℤ) ∧
    (∑ n ∈ Ico 158656 158720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8822156644368584316396753008 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158592_158720 :
    (∑ n ∈ Ico 158592 158720, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 158592 158720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 158592 158720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (441059 : ℤ) ∧
    (∑ n ∈ Ico 158592 158720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8821365769213758347266064877 : ℤ) := by
  rcases cdemPrefixStats_158592_158656 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158656_158720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158592 ≤ 158656) (by norm_num : 158656 ≤ 158720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158592 ≤ 158656) (by norm_num : 158656 ≤ 158720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158592 ≤ 158656) (by norm_num : 158656 ≤ 158720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158592 ≤ 158656) (by norm_num : 158656 ≤ 158720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158464_158720 :
    (∑ n ∈ Ico 158464 158720, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 158464 158720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 158464 158720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (251869 : ℤ) ∧
    (∑ n ∈ Ico 158464 158720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5037408718233720785562890445 : ℤ) := by
  rcases cdemPrefixStats_158464_158592 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158592_158720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158464 ≤ 158592) (by norm_num : 158592 ≤ 158720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158464 ≤ 158592) (by norm_num : 158592 ≤ 158720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158464 ≤ 158592) (by norm_num : 158592 ≤ 158720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158464 ≤ 158592) (by norm_num : 158592 ≤ 158720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158208_158720 :
    (∑ n ∈ Ico 158208 158720, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 158208 158720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 158208 158720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (251752 : ℤ) ∧
    (∑ n ∈ Ico 158208 158720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5034995726248459653171789820 : ℤ) := by
  rcases cdemPrefixStats_158208_158464 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158464_158720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158208 ≤ 158464) (by norm_num : 158464 ≤ 158720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158208 ≤ 158464) (by norm_num : 158464 ≤ 158720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158208 ≤ 158464) (by norm_num : 158464 ≤ 158720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158208 ≤ 158464) (by norm_num : 158464 ≤ 158720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157696_158720 :
    (∑ n ∈ Ico 157696 158720, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 157696 158720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 157696 158720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (283975 : ℤ) ∧
    (∑ n ∈ Ico 157696 158720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5679461558649639849977241603 : ℤ) := by
  rcases cdemPrefixStats_157696_158208 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158208_158720 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157696 ≤ 158208) (by norm_num : 158208 ≤ 158720), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157696 ≤ 158208) (by norm_num : 158208 ≤ 158720), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 158208) (by norm_num : 158208 ≤ 158720), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 158208) (by norm_num : 158208 ≤ 158720), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158720_158784 :
    (∑ n ∈ Ico 158720 158784, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 158720 158784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 158720 158784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-188984 : ℤ) ∧
    (∑ n ∈ Ico 158720 158784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3779785576286738840514797554 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158784_158848 :
    (∑ n ∈ Ico 158784 158848, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 158784 158848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 158784 158848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94428 : ℤ) ∧
    (∑ n ∈ Ico 158784 158848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1888589937459594237183050326 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158720_158848 :
    (∑ n ∈ Ico 158720 158848, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 158720 158848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 158720 158848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-94556 : ℤ) ∧
    (∑ n ∈ Ico 158720 158848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1891195638827144603331747228 : ℤ) := by
  rcases cdemPrefixStats_158720_158784 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158784_158848 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158720 ≤ 158784) (by norm_num : 158784 ≤ 158848), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158720 ≤ 158784) (by norm_num : 158784 ≤ 158848), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 158784) (by norm_num : 158784 ≤ 158848), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 158784) (by norm_num : 158784 ≤ 158848), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158848_158912 :
    (∑ n ∈ Ico 158848 158912, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 158848 158912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 158848 158912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (157329 : ℤ) ∧
    (∑ n ∈ Ico 158848 158912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3146625210460093976083812646 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158912_158976 :
    (∑ n ∈ Ico 158912 158976, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 158912 158976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 158912 158976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31475 : ℤ) ∧
    (∑ n ∈ Ico 158912 158976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-629500809430686663425794020 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158848_158976 :
    (∑ n ∈ Ico 158848 158976, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 158848 158976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 158848 158976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (125854 : ℤ) ∧
    (∑ n ∈ Ico 158848 158976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2517124401029407312658018626 : ℤ) := by
  rcases cdemPrefixStats_158848_158912 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158912_158976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158848 ≤ 158912) (by norm_num : 158912 ≤ 158976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158848 ≤ 158912) (by norm_num : 158912 ≤ 158976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158848 ≤ 158912) (by norm_num : 158912 ≤ 158976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158848 ≤ 158912) (by norm_num : 158912 ≤ 158976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158720_158976 :
    (∑ n ∈ Ico 158720 158976, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 158720 158976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 158720 158976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31298 : ℤ) ∧
    (∑ n ∈ Ico 158720 158976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (625928762202262709326271398 : ℤ) := by
  rcases cdemPrefixStats_158720_158848 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158848_158976 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158720 ≤ 158848) (by norm_num : 158848 ≤ 158976), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158720 ≤ 158848) (by norm_num : 158848 ≤ 158976), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 158848) (by norm_num : 158848 ≤ 158976), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 158848) (by norm_num : 158848 ≤ 158976), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158976_159040 :
    (∑ n ∈ Ico 158976 159040, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 158976 159040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 158976 159040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-125783 : ℤ) ∧
    (∑ n ∈ Ico 158976 159040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2515711499669339839885065791 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159040_159104 :
    (∑ n ∈ Ico 159040 159104, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 159040 159104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 159040 159104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62871 : ℤ) ∧
    (∑ n ∈ Ico 159040 159104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1257403044207227765243257656 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_158976_159104 :
    (∑ n ∈ Ico 158976 159104, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 158976 159104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 158976 159104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62912 : ℤ) ∧
    (∑ n ∈ Ico 158976 159104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1258308455462112074641808135 : ℤ) := by
  rcases cdemPrefixStats_158976_159040 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159040_159104 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158976 ≤ 159040) (by norm_num : 159040 ≤ 159104), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158976 ≤ 159040) (by norm_num : 159040 ≤ 159104), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158976 ≤ 159040) (by norm_num : 159040 ≤ 159104), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158976 ≤ 159040) (by norm_num : 159040 ≤ 159104), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159104_159168 :
    (∑ n ∈ Ico 159104 159168, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 159104 159168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159104 159168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (219963 : ℤ) ∧
    (∑ n ∈ Ico 159104 159168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4399278492226750073852748015 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159168_159232 :
    (∑ n ∈ Ico 159168 159232, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 159168 159232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159168 159232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-219843 : ℤ) ∧
    (∑ n ∈ Ico 159168 159232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4396835021232083338447288437 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159104_159232 :
    (∑ n ∈ Ico 159104 159232, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 159104 159232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 159104 159232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (120 : ℤ) ∧
    (∑ n ∈ Ico 159104 159232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2443470994666735405459578 : ℤ) := by
  rcases cdemPrefixStats_159104_159168 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159168_159232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159104 ≤ 159168) (by norm_num : 159168 ≤ 159232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159104 ≤ 159168) (by norm_num : 159168 ≤ 159232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159104 ≤ 159168) (by norm_num : 159168 ≤ 159232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159104 ≤ 159168) (by norm_num : 159168 ≤ 159232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158976_159232 :
    (∑ n ∈ Ico 158976 159232, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 158976 159232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 158976 159232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-62792 : ℤ) ∧
    (∑ n ∈ Ico 158976 159232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1255864984467445339236348557 : ℤ) := by
  rcases cdemPrefixStats_158976_159104 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159104_159232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158976 ≤ 159104) (by norm_num : 159104 ≤ 159232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158976 ≤ 159104) (by norm_num : 159104 ≤ 159232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158976 ≤ 159104) (by norm_num : 159104 ≤ 159232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158976 ≤ 159104) (by norm_num : 159104 ≤ 159232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158720_159232 :
    (∑ n ∈ Ico 158720 159232, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 158720 159232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 158720 159232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-31494 : ℤ) ∧
    (∑ n ∈ Ico 158720 159232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-629936222265182629910077159 : ℤ) := by
  rcases cdemPrefixStats_158720_158976 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158976_159232 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158720 ≤ 158976) (by norm_num : 158976 ≤ 159232), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158720 ≤ 158976) (by norm_num : 158976 ≤ 159232), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 158976) (by norm_num : 158976 ≤ 159232), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 158976) (by norm_num : 158976 ≤ 159232), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159232_159296 :
    (∑ n ∈ Ico 159232 159296, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 159232 159296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159232 159296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (282532 : ℤ) ∧
    (∑ n ∈ Ico 159232 159296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5650726510555698939387844765 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159296_159360 :
    (∑ n ∈ Ico 159296 159360, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 159296 159360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159296 159360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (94138 : ℤ) ∧
    (∑ n ∈ Ico 159296 159360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1882837341947470048691596385 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159232_159360 :
    (∑ n ∈ Ico 159232 159360, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 159232 159360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 159232 159360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (376670 : ℤ) ∧
    (∑ n ∈ Ico 159232 159360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7533563852503168988079441150 : ℤ) := by
  rcases cdemPrefixStats_159232_159296 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159296_159360 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159232 ≤ 159296) (by norm_num : 159296 ≤ 159360), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159232 ≤ 159296) (by norm_num : 159296 ≤ 159360), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159232 ≤ 159296) (by norm_num : 159296 ≤ 159360), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159232 ≤ 159296) (by norm_num : 159296 ≤ 159360), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159360_159424 :
    (∑ n ∈ Ico 159360 159424, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 159360 159424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159360 159424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31374 : ℤ) ∧
    (∑ n ∈ Ico 159360 159424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (627537483188159090919334472 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159424_159488 :
    (∑ n ∈ Ico 159424 159488, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 159424 159488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 159424 159488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-29 : ℤ) ∧
    (∑ n ∈ Ico 159424 159488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-515178813633908815046427 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159360_159488 :
    (∑ n ∈ Ico 159360 159488, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 159360 159488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 159360 159488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (31345 : ℤ) ∧
    (∑ n ∈ Ico 159360 159488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (627022304374525182104288045 : ℤ) := by
  rcases cdemPrefixStats_159360_159424 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159424_159488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159360 ≤ 159424) (by norm_num : 159424 ≤ 159488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159360 ≤ 159424) (by norm_num : 159424 ≤ 159488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159360 ≤ 159424) (by norm_num : 159424 ≤ 159488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159360 ≤ 159424) (by norm_num : 159424 ≤ 159488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159232_159488 :
    (∑ n ∈ Ico 159232 159488, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 159232 159488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 159232 159488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (408015 : ℤ) ∧
    (∑ n ∈ Ico 159232 159488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8160586156877694170183729195 : ℤ) := by
  rcases cdemPrefixStats_159232_159360 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159360_159488 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159232 ≤ 159360) (by norm_num : 159360 ≤ 159488), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159232 ≤ 159360) (by norm_num : 159360 ≤ 159488), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159232 ≤ 159360) (by norm_num : 159360 ≤ 159488), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159232 ≤ 159360) (by norm_num : 159360 ≤ 159488), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159488_159552 :
    (∑ n ∈ Ico 159488 159552, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 159488 159552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 159488 159552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-156708 : ℤ) ∧
    (∑ n ∈ Ico 159488 159552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3134234314454105491084666632 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159552_159616 :
    (∑ n ∈ Ico 159552 159616, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 159552 159616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 159552 159616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-156666 : ℤ) ∧
    (∑ n ∈ Ico 159552 159616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3133373881555599396141721892 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159488_159616 :
    (∑ n ∈ Ico 159488 159616, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 159488 159616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 159488 159616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-313374 : ℤ) ∧
    (∑ n ∈ Ico 159488 159616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6267608196009704887226388524 : ℤ) := by
  rcases cdemPrefixStats_159488_159552 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159552_159616 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159488 ≤ 159552) (by norm_num : 159552 ≤ 159616), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159488 ≤ 159552) (by norm_num : 159552 ≤ 159616), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159488 ≤ 159552) (by norm_num : 159552 ≤ 159616), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159488 ≤ 159552) (by norm_num : 159552 ≤ 159616), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159616_159680 :
    (∑ n ∈ Ico 159616 159680, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 159616 159680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 159616 159680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-250527 : ℤ) ∧
    (∑ n ∈ Ico 159616 159680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5010683005210023537656557215 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159680_159744 :
    (∑ n ∈ Ico 159680 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 159680 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 159680 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (62613 : ℤ) ∧
    (∑ n ∈ Ico 159680 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1252289404499064208402465675 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_159616_159744 :
    (∑ n ∈ Ico 159616 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 159616 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 159616 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-187914 : ℤ) ∧
    (∑ n ∈ Ico 159616 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3758393600710959329254091540 : ℤ) := by
  rcases cdemPrefixStats_159616_159680 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159680_159744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159616 ≤ 159680) (by norm_num : 159680 ≤ 159744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159616 ≤ 159680) (by norm_num : 159680 ≤ 159744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159616 ≤ 159680) (by norm_num : 159680 ≤ 159744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159616 ≤ 159680) (by norm_num : 159680 ≤ 159744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159488_159744 :
    (∑ n ∈ Ico 159488 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 159488 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 159488 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-501288 : ℤ) ∧
    (∑ n ∈ Ico 159488 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10026001796720664216480480064 : ℤ) := by
  rcases cdemPrefixStats_159488_159616 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159616_159744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159488 ≤ 159616) (by norm_num : 159616 ≤ 159744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159488 ≤ 159616) (by norm_num : 159616 ≤ 159744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159488 ≤ 159616) (by norm_num : 159616 ≤ 159744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159488 ≤ 159616) (by norm_num : 159616 ≤ 159744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_159232_159744 :
    (∑ n ∈ Ico 159232 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 159232 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 159232 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-93273 : ℤ) ∧
    (∑ n ∈ Ico 159232 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1865415639842970046296750869 : ℤ) := by
  rcases cdemPrefixStats_159232_159488 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159488_159744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 159232 ≤ 159488) (by norm_num : 159488 ≤ 159744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 159232 ≤ 159488) (by norm_num : 159488 ≤ 159744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 159232 ≤ 159488) (by norm_num : 159488 ≤ 159744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 159232 ≤ 159488) (by norm_num : 159488 ≤ 159744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_158720_159744 :
    (∑ n ∈ Ico 158720 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 158720 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (626 : ℕ) ∧
    (∑ n ∈ Ico 158720 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124767 : ℤ) ∧
    (∑ n ∈ Ico 158720 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2495351862108152676206828028 : ℤ) := by
  rcases cdemPrefixStats_158720_159232 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_159232_159744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 158720 ≤ 159232) (by norm_num : 159232 ≤ 159744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 158720 ≤ 159232) (by norm_num : 159232 ≤ 159744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 159232) (by norm_num : 159232 ≤ 159744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 158720 ≤ 159232) (by norm_num : 159232 ≤ 159744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_157696_159744 :
    (∑ n ∈ Ico 157696 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 157696 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1249 : ℕ) ∧
    (∑ n ∈ Ico 157696 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (159208 : ℤ) ∧
    (∑ n ∈ Ico 157696 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3184109696541487173770413575 : ℤ) := by
  rcases cdemPrefixStats_157696_158720 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_158720_159744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 157696 ≤ 158720) (by norm_num : 158720 ≤ 159744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 157696 ≤ 158720) (by norm_num : 158720 ≤ 159744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 158720) (by norm_num : 158720 ≤ 159744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 157696 ≤ 158720) (by norm_num : 158720 ≤ 159744), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_155648_159744 :
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124399 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2487958959274636536117155916 : ℤ) := by
  rcases cdemPrefixStats_155648_157696 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_157696_159744 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 155648 ≤ 157696) (by norm_num : 157696 ≤ 159744), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 155648 ≤ 157696) (by norm_num : 157696 ≤ 159744), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 157696) (by norm_num : 157696 ≤ 159744), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 155648 ≤ 157696) (by norm_num : 157696 ≤ 159744), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup038_checked_complete :
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124399 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2487958959274636536117155916 : ℤ) := cdemPrefixStats_155648_159744
end Helfgott
#print axioms Helfgott.cdemPrefixGroup038_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124399 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2487958959274636536117155916 : ℤ) := Helfgott.cdemPrefixGroup038_checked_complete
#print axioms solution
