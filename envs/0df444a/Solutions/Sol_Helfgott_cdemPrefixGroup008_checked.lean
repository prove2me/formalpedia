-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup008_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:29:20.010212+00:00
-- url     : https://prove2.me/submissions/5f362eca-3fd2-4f1c-83e3-beba3415521f

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
private theorem cdemPrefixStats_32768_32832 :
    (∑ n ∈ Ico 32768 32832, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 32768 32832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (34 : ℕ) ∧
    (∑ n ∈ Ico 32768 32832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1219877 : ℤ) ∧
    (∑ n ∈ Ico 32768 32832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24397590063824006716539962074 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32832_32896 :
    (∑ n ∈ Ico 32832 32896, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 32832 32896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 32832 32896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (761326 : ℤ) ∧
    (∑ n ∈ Ico 32832 32896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15226533309419527092179510421 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32768_32896 :
    (∑ n ∈ Ico 32768 32896, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 32768 32896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (73 : ℕ) ∧
    (∑ n ∈ Ico 32768 32896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-458551 : ℤ) ∧
    (∑ n ∈ Ico 32768 32896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9171056754404479624360451653 : ℤ) := by
  rcases cdemPrefixStats_32768_32832 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32832_32896 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32768 ≤ 32832) (by norm_num : 32832 ≤ 32896), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32768 ≤ 32832) (by norm_num : 32832 ≤ 32896), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 32832) (by norm_num : 32832 ≤ 32896), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 32832) (by norm_num : 32832 ≤ 32896), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32896_32960 :
    (∑ n ∈ Ico 32896 32960, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 32896 32960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 32896 32960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-151964 : ℤ) ∧
    (∑ n ∈ Ico 32896 32960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3039226711656495605047245226 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32960_33024 :
    (∑ n ∈ Ico 32960 33024, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 32960 33024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 32960 33024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1364257 : ℤ) ∧
    (∑ n ∈ Ico 32960 33024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-27285228113162526269784539413 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_32896_33024 :
    (∑ n ∈ Ico 32896 33024, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 32896 33024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 32896 33024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1516221 : ℤ) ∧
    (∑ n ∈ Ico 32896 33024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-30324454824819021874831784639 : ℤ) := by
  rcases cdemPrefixStats_32896_32960 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32960_33024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32896 ≤ 32960) (by norm_num : 32960 ≤ 33024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32896 ≤ 32960) (by norm_num : 32960 ≤ 33024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32896 ≤ 32960) (by norm_num : 32960 ≤ 33024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32896 ≤ 32960) (by norm_num : 32960 ≤ 33024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32768_33024 :
    (∑ n ∈ Ico 32768 33024, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 32768 33024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 32768 33024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1974772 : ℤ) ∧
    (∑ n ∈ Ico 32768 33024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39495511579223501499192236292 : ℤ) := by
  rcases cdemPrefixStats_32768_32896 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_32896_33024 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32768 ≤ 32896) (by norm_num : 32896 ≤ 33024), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32768 ≤ 32896) (by norm_num : 32896 ≤ 33024), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 32896) (by norm_num : 32896 ≤ 33024), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 32896) (by norm_num : 32896 ≤ 33024), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33024_33088 :
    (∑ n ∈ Ico 33024 33088, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 33024 33088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 33024 33088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1663773 : ℤ) ∧
    (∑ n ∈ Ico 33024 33088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33275505471031922828992483121 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33088_33152 :
    (∑ n ∈ Ico 33088 33152, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 33088 33152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 33088 33152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (453399 : ℤ) ∧
    (∑ n ∈ Ico 33088 33152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9068001562255809210190934306 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33024_33152 :
    (∑ n ∈ Ico 33024 33152, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 33024 33152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 33024 33152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1210374 : ℤ) ∧
    (∑ n ∈ Ico 33024 33152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24207503908776113618801548815 : ℤ) := by
  rcases cdemPrefixStats_33024_33088 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33088_33152 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33024 ≤ 33088) (by norm_num : 33088 ≤ 33152), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33024 ≤ 33088) (by norm_num : 33088 ≤ 33152), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33024 ≤ 33088) (by norm_num : 33088 ≤ 33152), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33024 ≤ 33088) (by norm_num : 33088 ≤ 33152), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33152_33216 :
    (∑ n ∈ Ico 33152 33216, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 33152 33216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 33152 33216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-301814 : ℤ) ∧
    (∑ n ∈ Ico 33152 33216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6036352831433909640037284700 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33216_33280 :
    (∑ n ∈ Ico 33216 33280, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 33216 33280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 33216 33280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1052492 : ℤ) ∧
    (∑ n ∈ Ico 33216 33280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21049921074392249138133365951 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33152_33280 :
    (∑ n ∈ Ico 33152 33280, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 33152 33280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 33152 33280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (750678 : ℤ) ∧
    (∑ n ∈ Ico 33152 33280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15013568242958339498096081251 : ℤ) := by
  rcases cdemPrefixStats_33152_33216 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33216_33280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33152 ≤ 33216) (by norm_num : 33216 ≤ 33280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33152 ≤ 33216) (by norm_num : 33216 ≤ 33280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33152 ≤ 33216) (by norm_num : 33216 ≤ 33280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33152 ≤ 33216) (by norm_num : 33216 ≤ 33280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33024_33280 :
    (∑ n ∈ Ico 33024 33280, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 33024 33280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 33024 33280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-459696 : ℤ) ∧
    (∑ n ∈ Ico 33024 33280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9193935665817774120705467564 : ℤ) := by
  rcases cdemPrefixStats_33024_33152 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33152_33280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33024 ≤ 33152) (by norm_num : 33152 ≤ 33280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33024 ≤ 33152) (by norm_num : 33152 ≤ 33280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33024 ≤ 33152) (by norm_num : 33152 ≤ 33280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33024 ≤ 33152) (by norm_num : 33152 ≤ 33280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32768_33280 :
    (∑ n ∈ Ico 32768 33280, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 32768 33280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (308 : ℕ) ∧
    (∑ n ∈ Ico 32768 33280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2434468 : ℤ) ∧
    (∑ n ∈ Ico 32768 33280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-48689447245041275619897703856 : ℤ) := by
  rcases cdemPrefixStats_32768_33024 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33024_33280 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32768 ≤ 33024) (by norm_num : 33024 ≤ 33280), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32768 ≤ 33024) (by norm_num : 33024 ≤ 33280), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 33024) (by norm_num : 33024 ≤ 33280), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 33024) (by norm_num : 33024 ≤ 33280), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33280_33344 :
    (∑ n ∈ Ico 33280 33344, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 33280 33344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 33280 33344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1649679 : ℤ) ∧
    (∑ n ∈ Ico 33280 33344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-32993658946016878177635766784 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33344_33408 :
    (∑ n ∈ Ico 33344 33408, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 33344 33408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 33344 33408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (748394 : ℤ) ∧
    (∑ n ∈ Ico 33344 33408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14967904544998805863995669849 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33280_33408 :
    (∑ n ∈ Ico 33280 33408, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 33280 33408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 33280 33408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-901285 : ℤ) ∧
    (∑ n ∈ Ico 33280 33408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18025754401018072313640096935 : ℤ) := by
  rcases cdemPrefixStats_33280_33344 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33344_33408 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33280 ≤ 33344) (by norm_num : 33344 ≤ 33408), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33280 ≤ 33344) (by norm_num : 33344 ≤ 33408), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33280 ≤ 33344) (by norm_num : 33344 ≤ 33408), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33280 ≤ 33344) (by norm_num : 33344 ≤ 33408), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33408_33472 :
    (∑ n ∈ Ico 33408 33472, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 33408 33472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 33408 33472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1196178 : ℤ) ∧
    (∑ n ∈ Ico 33408 33472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23923632577694012619986283109 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33472_33536 :
    (∑ n ∈ Ico 33472 33536, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 33472 33536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 33472 33536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (447353 : ℤ) ∧
    (∑ n ∈ Ico 33472 33536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8947119613579378038267768768 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33408_33536 :
    (∑ n ∈ Ico 33408 33536, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 33408 33536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 33408 33536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-748825 : ℤ) ∧
    (∑ n ∈ Ico 33408 33536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14976512964114634581718514341 : ℤ) := by
  rcases cdemPrefixStats_33408_33472 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33472_33536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33408 ≤ 33472) (by norm_num : 33472 ≤ 33536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33408 ≤ 33472) (by norm_num : 33472 ≤ 33536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33408 ≤ 33472) (by norm_num : 33472 ≤ 33536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33408 ≤ 33472) (by norm_num : 33472 ≤ 33536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33280_33536 :
    (∑ n ∈ Ico 33280 33536, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 33280 33536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 33280 33536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1650110 : ℤ) ∧
    (∑ n ∈ Ico 33280 33536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33002267365132706895358611276 : ℤ) := by
  rcases cdemPrefixStats_33280_33408 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33408_33536 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33280 ≤ 33408) (by norm_num : 33408 ≤ 33536), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33280 ≤ 33408) (by norm_num : 33408 ≤ 33536), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33280 ≤ 33408) (by norm_num : 33408 ≤ 33536), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33280 ≤ 33408) (by norm_num : 33408 ≤ 33536), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33536_33600 :
    (∑ n ∈ Ico 33536 33600, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 33536 33600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 33536 33600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1936435 : ℤ) ∧
    (∑ n ∈ Ico 33536 33600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-38728877393263200925574110391 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33600_33664 :
    (∑ n ∈ Ico 33600 33664, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 33600 33664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 33600 33664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-893168 : ℤ) ∧
    (∑ n ∈ Ico 33600 33664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17863404760074771732542408652 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33536_33664 :
    (∑ n ∈ Ico 33536 33664, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 33536 33664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 33536 33664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2829603 : ℤ) ∧
    (∑ n ∈ Ico 33536 33664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-56592282153337972658116519043 : ℤ) := by
  rcases cdemPrefixStats_33536_33600 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33600_33664 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33536 ≤ 33600) (by norm_num : 33600 ≤ 33664), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33536 ≤ 33600) (by norm_num : 33600 ≤ 33664), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33536 ≤ 33600) (by norm_num : 33600 ≤ 33664), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33536 ≤ 33600) (by norm_num : 33600 ≤ 33664), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33664_33728 :
    (∑ n ∈ Ico 33664 33728, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 33664 33728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 33664 33728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (645 : ℤ) ∧
    (∑ n ∈ Ico 33664 33728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12859946188904542982673793 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33728_33792 :
    (∑ n ∈ Ico 33728 33792, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 33728 33792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 33728 33792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-444491 : ℤ) ∧
    (∑ n ∈ Ico 33728 33792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8889856689681255126842052042 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33664_33792 :
    (∑ n ∈ Ico 33664 33792, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 33664 33792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 33664 33792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-443846 : ℤ) ∧
    (∑ n ∈ Ico 33664 33792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8876996743492350583859378249 : ℤ) := by
  rcases cdemPrefixStats_33664_33728 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33728_33792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33664 ≤ 33728) (by norm_num : 33728 ≤ 33792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33664 ≤ 33728) (by norm_num : 33728 ≤ 33792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33664 ≤ 33728) (by norm_num : 33728 ≤ 33792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33664 ≤ 33728) (by norm_num : 33728 ≤ 33792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33536_33792 :
    (∑ n ∈ Ico 33536 33792, mobiusTreeValue 16 mobiusTable1200001 n) = (-22 : ℤ) ∧
    (∑ n ∈ Ico 33536 33792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 33536 33792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3273449 : ℤ) ∧
    (∑ n ∈ Ico 33536 33792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-65469278896830323241975897292 : ℤ) := by
  rcases cdemPrefixStats_33536_33664 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33664_33792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33536 ≤ 33664) (by norm_num : 33664 ≤ 33792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33536 ≤ 33664) (by norm_num : 33664 ≤ 33792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33536 ≤ 33664) (by norm_num : 33664 ≤ 33792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33536 ≤ 33664) (by norm_num : 33664 ≤ 33792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33280_33792 :
    (∑ n ∈ Ico 33280 33792, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 33280 33792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (315 : ℕ) ∧
    (∑ n ∈ Ico 33280 33792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4923559 : ℤ) ∧
    (∑ n ∈ Ico 33280 33792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-98471546261963030137334508568 : ℤ) := by
  rcases cdemPrefixStats_33280_33536 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33536_33792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33280 ≤ 33536) (by norm_num : 33536 ≤ 33792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33280 ≤ 33536) (by norm_num : 33536 ≤ 33792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33280 ≤ 33536) (by norm_num : 33536 ≤ 33792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33280 ≤ 33536) (by norm_num : 33536 ≤ 33792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32768_33792 :
    (∑ n ∈ Ico 32768 33792, mobiusTreeValue 16 mobiusTable1200001 n) = (-49 : ℤ) ∧
    (∑ n ∈ Ico 32768 33792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 32768 33792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-7358027 : ℤ) ∧
    (∑ n ∈ Ico 32768 33792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-147160993507004305757232212424 : ℤ) := by
  rcases cdemPrefixStats_32768_33280 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33280_33792 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32768 ≤ 33280) (by norm_num : 33280 ≤ 33792), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32768 ≤ 33280) (by norm_num : 33280 ≤ 33792), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 33280) (by norm_num : 33280 ≤ 33792), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 33280) (by norm_num : 33280 ≤ 33792), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33792_33856 :
    (∑ n ∈ Ico 33792 33856, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 33792 33856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 33792 33856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (188 : ℤ) ∧
    (∑ n ∈ Ico 33792 33856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3760484042608954842808263 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33856_33920 :
    (∑ n ∈ Ico 33856 33920, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 33856 33920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 33856 33920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147342 : ℤ) ∧
    (∑ n ∈ Ico 33856 33920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2946806276616199260298638403 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33792_33920 :
    (∑ n ∈ Ico 33792 33920, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 33792 33920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 33792 33920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147154 : ℤ) ∧
    (∑ n ∈ Ico 33792 33920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2943045792573590305455830140 : ℤ) := by
  rcases cdemPrefixStats_33792_33856 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33856_33920 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33792 ≤ 33856) (by norm_num : 33856 ≤ 33920), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33792 ≤ 33856) (by norm_num : 33856 ≤ 33920), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 33856) (by norm_num : 33856 ≤ 33920), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 33856) (by norm_num : 33856 ≤ 33920), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33920_33984 :
    (∑ n ∈ Ico 33920 33984, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 33920 33984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 33920 33984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (293381 : ℤ) ∧
    (∑ n ∈ Ico 33920 33984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5867591254033830187926585448 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33984_34048 :
    (∑ n ∈ Ico 33984 34048, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 33984 34048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 33984 34048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-440778 : ℤ) ∧
    (∑ n ∈ Ico 33984 34048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8815581722431319592054667592 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_33920_34048 :
    (∑ n ∈ Ico 33920 34048, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 33920 34048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 33920 34048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-147397 : ℤ) ∧
    (∑ n ∈ Ico 33920 34048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2947990468397489404128082144 : ℤ) := by
  rcases cdemPrefixStats_33920_33984 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33984_34048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33920 ≤ 33984) (by norm_num : 33984 ≤ 34048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33920 ≤ 33984) (by norm_num : 33984 ≤ 34048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33920 ≤ 33984) (by norm_num : 33984 ≤ 34048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33920 ≤ 33984) (by norm_num : 33984 ≤ 34048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33792_34048 :
    (∑ n ∈ Ico 33792 34048, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 33792 34048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 33792 34048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-294551 : ℤ) ∧
    (∑ n ∈ Ico 33792 34048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5891036260971079709583912284 : ℤ) := by
  rcases cdemPrefixStats_33792_33920 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33920_34048 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33792 ≤ 33920) (by norm_num : 33920 ≤ 34048), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33792 ≤ 33920) (by norm_num : 33920 ≤ 34048), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 33920) (by norm_num : 33920 ≤ 34048), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 33920) (by norm_num : 33920 ≤ 34048), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34048_34112 :
    (∑ n ∈ Ico 34048 34112, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 34048 34112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34048 34112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1027297 : ℤ) ∧
    (∑ n ∈ Ico 34048 34112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (20546031007406579248197359448 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34112_34176 :
    (∑ n ∈ Ico 34112 34176, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 34112 34176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 34112 34176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1903783 : ℤ) ∧
    (∑ n ∈ Ico 34112 34176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-38075852208687517374152316440 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34048_34176 :
    (∑ n ∈ Ico 34048 34176, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 34048 34176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 34048 34176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-876486 : ℤ) ∧
    (∑ n ∈ Ico 34048 34176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17529821201280938125954956992 : ℤ) := by
  rcases cdemPrefixStats_34048_34112 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34112_34176 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34048 ≤ 34112) (by norm_num : 34112 ≤ 34176), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34048 ≤ 34112) (by norm_num : 34112 ≤ 34176), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34048 ≤ 34112) (by norm_num : 34112 ≤ 34176), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34048 ≤ 34112) (by norm_num : 34112 ≤ 34176), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34176_34240 :
    (∑ n ∈ Ico 34176 34240, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 34176 34240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 34176 34240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (731280 : ℤ) ∧
    (∑ n ∈ Ico 34176 34240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14625691574370448687815421138 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34240_34304 :
    (∑ n ∈ Ico 34240 34304, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 34240 34304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 34240 34304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-145116 : ℤ) ∧
    (∑ n ∈ Ico 34240 34304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2902340373344167015629716297 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34176_34304 :
    (∑ n ∈ Ico 34176 34304, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 34176 34304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 34176 34304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (586164 : ℤ) ∧
    (∑ n ∈ Ico 34176 34304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11723351201026281672185704841 : ℤ) := by
  rcases cdemPrefixStats_34176_34240 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34240_34304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34176 ≤ 34240) (by norm_num : 34240 ≤ 34304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34176 ≤ 34240) (by norm_num : 34240 ≤ 34304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34176 ≤ 34240) (by norm_num : 34240 ≤ 34304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34176 ≤ 34240) (by norm_num : 34240 ≤ 34304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34048_34304 :
    (∑ n ∈ Ico 34048 34304, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 34048 34304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 34048 34304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-290322 : ℤ) ∧
    (∑ n ∈ Ico 34048 34304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5806470000254656453769252151 : ℤ) := by
  rcases cdemPrefixStats_34048_34176 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34176_34304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34048 ≤ 34176) (by norm_num : 34176 ≤ 34304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34048 ≤ 34176) (by norm_num : 34176 ≤ 34304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34048 ≤ 34176) (by norm_num : 34176 ≤ 34304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34048 ≤ 34176) (by norm_num : 34176 ≤ 34304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33792_34304 :
    (∑ n ∈ Ico 33792 34304, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 33792 34304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 33792 34304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-584873 : ℤ) ∧
    (∑ n ∈ Ico 33792 34304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11697506261225736163353164435 : ℤ) := by
  rcases cdemPrefixStats_33792_34048 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34048_34304 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33792 ≤ 34048) (by norm_num : 34048 ≤ 34304), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33792 ≤ 34048) (by norm_num : 34048 ≤ 34304), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 34048) (by norm_num : 34048 ≤ 34304), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 34048) (by norm_num : 34048 ≤ 34304), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34304_34368 :
    (∑ n ∈ Ico 34304 34368, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 34304 34368, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 34304 34368, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145709 : ℤ) ∧
    (∑ n ∈ Ico 34304 34368, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2914173875430970895780100140 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34368_34432 :
    (∑ n ∈ Ico 34368 34432, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 34368 34432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 34368 34432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1162917 : ℤ) ∧
    (∑ n ∈ Ico 34368 34432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23258439214655414550450146384 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34304_34432 :
    (∑ n ∈ Ico 34304 34432, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 34304 34432, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 34304 34432, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1308626 : ℤ) ∧
    (∑ n ∈ Ico 34304 34432, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26172613090086385446230246524 : ℤ) := by
  rcases cdemPrefixStats_34304_34368 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34368_34432 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34304 ≤ 34368) (by norm_num : 34368 ≤ 34432), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34304 ≤ 34368) (by norm_num : 34368 ≤ 34432), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34304 ≤ 34368) (by norm_num : 34368 ≤ 34432), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34304 ≤ 34368) (by norm_num : 34368 ≤ 34432), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34432_34496 :
    (∑ n ∈ Ico 34432 34496, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 34432 34496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 34432 34496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1015883 : ℤ) ∧
    (∑ n ∈ Ico 34432 34496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20317792392742245860558042093 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34496_34560 :
    (∑ n ∈ Ico 34496 34560, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 34496 34560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34496 34560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1014404 : ℤ) ∧
    (∑ n ∈ Ico 34496 34560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20288165772413517971299219313 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34432_34560 :
    (∑ n ∈ Ico 34432 34560, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 34432 34560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 34432 34560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2030287 : ℤ) ∧
    (∑ n ∈ Ico 34432 34560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-40605958165155763831857261406 : ℤ) := by
  rcases cdemPrefixStats_34432_34496 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34496_34560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34432 ≤ 34496) (by norm_num : 34496 ≤ 34560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34432 ≤ 34496) (by norm_num : 34496 ≤ 34560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34432 ≤ 34496) (by norm_num : 34496 ≤ 34560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34432 ≤ 34496) (by norm_num : 34496 ≤ 34560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34304_34560 :
    (∑ n ∈ Ico 34304 34560, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 34304 34560, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 34304 34560, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-721661 : ℤ) ∧
    (∑ n ∈ Ico 34304 34560, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-14433345075069378385627014882 : ℤ) := by
  rcases cdemPrefixStats_34304_34432 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34432_34560 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34304 ≤ 34432) (by norm_num : 34432 ≤ 34560), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34304 ≤ 34432) (by norm_num : 34432 ≤ 34560), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34304 ≤ 34432) (by norm_num : 34432 ≤ 34560), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34304 ≤ 34432) (by norm_num : 34432 ≤ 34560), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34560_34624 :
    (∑ n ∈ Ico 34560 34624, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 34560 34624, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34560 34624, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-144576 : ℤ) ∧
    (∑ n ∈ Ico 34560 34624, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2891601986034255974082656947 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34624_34688 :
    (∑ n ∈ Ico 34624 34688, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 34624 34688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34624 34688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (145046 : ℤ) ∧
    (∑ n ∈ Ico 34624 34688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2900905515156028609843367030 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34560_34688 :
    (∑ n ∈ Ico 34560 34688, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 34560 34688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 34560 34688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (470 : ℤ) ∧
    (∑ n ∈ Ico 34560 34688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9303529121772635760710083 : ℤ) := by
  rcases cdemPrefixStats_34560_34624 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34624_34688 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34560 ≤ 34624) (by norm_num : 34624 ≤ 34688), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34560 ≤ 34624) (by norm_num : 34624 ≤ 34688), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34560 ≤ 34624) (by norm_num : 34624 ≤ 34688), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34560 ≤ 34624) (by norm_num : 34624 ≤ 34688), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34688_34752 :
    (∑ n ∈ Ico 34688 34752, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 34688 34752, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34688 34752, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1008066 : ℤ) ∧
    (∑ n ∈ Ico 34688 34752, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20161384469615539158830659719 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34752_34816 :
    (∑ n ∈ Ico 34752 34816, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 34752 34816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34752 34816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1293670 : ℤ) ∧
    (∑ n ∈ Ico 34752 34816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25873477379588585182954966600 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34688_34816 :
    (∑ n ∈ Ico 34688 34816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 34688 34816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 34688 34816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (285604 : ℤ) ∧
    (∑ n ∈ Ico 34688 34816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5712092909973046024124306881 : ℤ) := by
  rcases cdemPrefixStats_34688_34752 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34752_34816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34688 ≤ 34752) (by norm_num : 34752 ≤ 34816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34688 ≤ 34752) (by norm_num : 34752 ≤ 34816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34688 ≤ 34752) (by norm_num : 34752 ≤ 34816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34688 ≤ 34752) (by norm_num : 34752 ≤ 34816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34560_34816 :
    (∑ n ∈ Ico 34560 34816, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 34560 34816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 34560 34816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (286074 : ℤ) ∧
    (∑ n ∈ Ico 34560 34816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5721396439094818659885016964 : ℤ) := by
  rcases cdemPrefixStats_34560_34688 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34688_34816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34560 ≤ 34688) (by norm_num : 34688 ≤ 34816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34560 ≤ 34688) (by norm_num : 34688 ≤ 34816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34560 ≤ 34688) (by norm_num : 34688 ≤ 34816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34560 ≤ 34688) (by norm_num : 34688 ≤ 34816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34304_34816 :
    (∑ n ∈ Ico 34304 34816, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 34304 34816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 34304 34816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-435587 : ℤ) ∧
    (∑ n ∈ Ico 34304 34816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8711948635974559725741997918 : ℤ) := by
  rcases cdemPrefixStats_34304_34560 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34560_34816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34304 ≤ 34560) (by norm_num : 34560 ≤ 34816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34304 ≤ 34560) (by norm_num : 34560 ≤ 34816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34304 ≤ 34560) (by norm_num : 34560 ≤ 34816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34304 ≤ 34560) (by norm_num : 34560 ≤ 34816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_33792_34816 :
    (∑ n ∈ Ico 33792 34816, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 33792 34816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 33792 34816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1020460 : ℤ) ∧
    (∑ n ∈ Ico 33792 34816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20409454897200295889095162353 : ℤ) := by
  rcases cdemPrefixStats_33792_34304 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34304_34816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 33792 ≤ 34304) (by norm_num : 34304 ≤ 34816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 33792 ≤ 34304) (by norm_num : 34304 ≤ 34816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 34304) (by norm_num : 34304 ≤ 34816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 33792 ≤ 34304) (by norm_num : 34304 ≤ 34816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32768_34816 :
    (∑ n ∈ Ico 32768 34816, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 32768 34816, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1244 : ℕ) ∧
    (∑ n ∈ Ico 32768 34816, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-8378487 : ℤ) ∧
    (∑ n ∈ Ico 32768 34816, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-167570448404204601646327374777 : ℤ) := by
  rcases cdemPrefixStats_32768_33792 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_33792_34816 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32768 ≤ 33792) (by norm_num : 33792 ≤ 34816), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32768 ≤ 33792) (by norm_num : 33792 ≤ 34816), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 33792) (by norm_num : 33792 ≤ 34816), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 33792) (by norm_num : 33792 ≤ 34816), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34816_34880 :
    (∑ n ∈ Ico 34816 34880, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 34816 34880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 34816 34880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (861153 : ℤ) ∧
    (∑ n ∈ Ico 34816 34880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17223152558488605067548616733 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34880_34944 :
    (∑ n ∈ Ico 34880 34944, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 34880 34944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 34880 34944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (572525 : ℤ) ∧
    (∑ n ∈ Ico 34880 34944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11450574645043319381836397577 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34816_34944 :
    (∑ n ∈ Ico 34816 34944, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 34816 34944, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 34816 34944, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1433678 : ℤ) ∧
    (∑ n ∈ Ico 34816 34944, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28673727203531924449385014310 : ℤ) := by
  rcases cdemPrefixStats_34816_34880 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34880_34944 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34816 ≤ 34880) (by norm_num : 34880 ≤ 34944), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34816 ≤ 34880) (by norm_num : 34880 ≤ 34944), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 34880) (by norm_num : 34880 ≤ 34944), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 34880) (by norm_num : 34880 ≤ 34944), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34944_35008 :
    (∑ n ∈ Ico 34944 35008, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 34944 35008, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 34944 35008, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (714414 : ℤ) ∧
    (∑ n ∈ Ico 34944 35008, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14288321489022869175177231396 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35008_35072 :
    (∑ n ∈ Ico 35008 35072, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 35008 35072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 35008 35072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (428592 : ℤ) ∧
    (∑ n ∈ Ico 35008 35072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8571909361353002067631813855 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_34944_35072 :
    (∑ n ∈ Ico 34944 35072, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 34944 35072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 34944 35072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1143006 : ℤ) ∧
    (∑ n ∈ Ico 34944 35072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22860230850375871242809045251 : ℤ) := by
  rcases cdemPrefixStats_34944_35008 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35008_35072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34944 ≤ 35008) (by norm_num : 35008 ≤ 35072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34944 ≤ 35008) (by norm_num : 35008 ≤ 35072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34944 ≤ 35008) (by norm_num : 35008 ≤ 35072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34944 ≤ 35008) (by norm_num : 35008 ≤ 35072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34816_35072 :
    (∑ n ∈ Ico 34816 35072, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 34816 35072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 34816 35072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2576684 : ℤ) ∧
    (∑ n ∈ Ico 34816 35072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51533958053907795692194059561 : ℤ) := by
  rcases cdemPrefixStats_34816_34944 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34944_35072 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34816 ≤ 34944) (by norm_num : 34944 ≤ 35072), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34816 ≤ 34944) (by norm_num : 34944 ≤ 35072), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 34944) (by norm_num : 34944 ≤ 35072), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 34944) (by norm_num : 34944 ≤ 35072), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35072_35136 :
    (∑ n ∈ Ico 35072 35136, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 35072 35136, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 35072 35136, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-996596 : ℤ) ∧
    (∑ n ∈ Ico 35072 35136, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19931985420676586695864795019 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35136_35200 :
    (∑ n ∈ Ico 35136 35200, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 35136 35200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 35136 35200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (426490 : ℤ) ∧
    (∑ n ∈ Ico 35136 35200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8529767850507077873037012839 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35072_35200 :
    (∑ n ∈ Ico 35072 35200, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 35072 35200, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 35072 35200, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-570106 : ℤ) ∧
    (∑ n ∈ Ico 35072 35200, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11402217570169508822827782180 : ℤ) := by
  rcases cdemPrefixStats_35072_35136 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35136_35200 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35072 ≤ 35136) (by norm_num : 35136 ≤ 35200), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35072 ≤ 35136) (by norm_num : 35136 ≤ 35200), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35072 ≤ 35136) (by norm_num : 35136 ≤ 35200), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35072 ≤ 35136) (by norm_num : 35136 ≤ 35200), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35200_35264 :
    (∑ n ∈ Ico 35200 35264, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 35200 35264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 35200 35264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (283075 : ℤ) ∧
    (∑ n ∈ Ico 35200 35264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5661508962715004173893948246 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35264_35328 :
    (∑ n ∈ Ico 35264 35328, mobiusTreeValue 16 mobiusTable1200001 n) = (-14 : ℤ) ∧
    (∑ n ∈ Ico 35264 35328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 35264 35328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1982896 : ℤ) ∧
    (∑ n ∈ Ico 35264 35328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39658143691799869768443327817 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35200_35328 :
    (∑ n ∈ Ico 35200 35328, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 35200 35328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 35200 35328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1699821 : ℤ) ∧
    (∑ n ∈ Ico 35200 35328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33996634729084865594549379571 : ℤ) := by
  rcases cdemPrefixStats_35200_35264 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35264_35328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35200 ≤ 35264) (by norm_num : 35264 ≤ 35328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35200 ≤ 35264) (by norm_num : 35264 ≤ 35328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35200 ≤ 35264) (by norm_num : 35264 ≤ 35328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35200 ≤ 35264) (by norm_num : 35264 ≤ 35328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35072_35328 :
    (∑ n ∈ Ico 35072 35328, mobiusTreeValue 16 mobiusTable1200001 n) = (-16 : ℤ) ∧
    (∑ n ∈ Ico 35072 35328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 35072 35328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2269927 : ℤ) ∧
    (∑ n ∈ Ico 35072 35328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-45398852299254374417377161751 : ℤ) := by
  rcases cdemPrefixStats_35072_35200 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35200_35328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35072 ≤ 35200) (by norm_num : 35200 ≤ 35328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35072 ≤ 35200) (by norm_num : 35200 ≤ 35328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35072 ≤ 35200) (by norm_num : 35200 ≤ 35328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35072 ≤ 35200) (by norm_num : 35200 ≤ 35328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34816_35328 :
    (∑ n ∈ Ico 34816 35328, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 34816 35328, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 34816 35328, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (306757 : ℤ) ∧
    (∑ n ∈ Ico 34816 35328, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6135105754653421274816897810 : ℤ) := by
  rcases cdemPrefixStats_34816_35072 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35072_35328 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34816 ≤ 35072) (by norm_num : 35072 ≤ 35328), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34816 ≤ 35072) (by norm_num : 35072 ≤ 35328), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 35072) (by norm_num : 35072 ≤ 35328), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 35072) (by norm_num : 35072 ≤ 35328), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35328_35392 :
    (∑ n ∈ Ico 35328 35392, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 35328 35392, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 35328 35392, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (424562 : ℤ) ∧
    (∑ n ∈ Ico 35328 35392, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8491281901880668719870653280 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35392_35456 :
    (∑ n ∈ Ico 35392 35456, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 35392 35456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 35392 35456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-423438 : ℤ) ∧
    (∑ n ∈ Ico 35392 35456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8468840838602035135577030954 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35328_35456 :
    (∑ n ∈ Ico 35328 35456, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 35328 35456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 35328 35456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1124 : ℤ) ∧
    (∑ n ∈ Ico 35328 35456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22441063278633584293622326 : ℤ) := by
  rcases cdemPrefixStats_35328_35392 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35392_35456 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35328 ≤ 35392) (by norm_num : 35392 ≤ 35456), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35328 ≤ 35392) (by norm_num : 35392 ≤ 35456), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35328 ≤ 35392) (by norm_num : 35392 ≤ 35456), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35328 ≤ 35392) (by norm_num : 35392 ≤ 35456), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35456_35520 :
    (∑ n ∈ Ico 35456 35520, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 35456 35520, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 35456 35520, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1831308 : ℤ) ∧
    (∑ n ∈ Ico 35456 35520, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36626240799865249590667814294 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35520_35584 :
    (∑ n ∈ Ico 35520 35584, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 35520 35584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 35520 35584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1406839 : ℤ) ∧
    (∑ n ∈ Ico 35520 35584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28136835368336153125812037131 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35456_35584 :
    (∑ n ∈ Ico 35456 35584, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 35456 35584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 35456 35584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (424469 : ℤ) ∧
    (∑ n ∈ Ico 35456 35584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8489405431529096464855777163 : ℤ) := by
  rcases cdemPrefixStats_35456_35520 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35520_35584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35456 ≤ 35520) (by norm_num : 35520 ≤ 35584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35456 ≤ 35520) (by norm_num : 35520 ≤ 35584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35456 ≤ 35520) (by norm_num : 35520 ≤ 35584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35456 ≤ 35520) (by norm_num : 35520 ≤ 35584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35328_35584 :
    (∑ n ∈ Ico 35328 35584, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 35328 35584, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 35328 35584, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (425593 : ℤ) ∧
    (∑ n ∈ Ico 35328 35584, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8511846494807730049149399489 : ℤ) := by
  rcases cdemPrefixStats_35328_35456 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35456_35584 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35328 ≤ 35456) (by norm_num : 35456 ≤ 35584), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35328 ≤ 35456) (by norm_num : 35456 ≤ 35584), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35328 ≤ 35456) (by norm_num : 35456 ≤ 35584), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35328 ≤ 35456) (by norm_num : 35456 ≤ 35584), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35584_35648 :
    (∑ n ∈ Ico 35584 35648, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 35584 35648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 35584 35648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (420748 : ℤ) ∧
    (∑ n ∈ Ico 35584 35648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8414985787731240907108329543 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35648_35712 :
    (∑ n ∈ Ico 35648 35712, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 35648 35712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 35648 35712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1120844 : ℤ) ∧
    (∑ n ∈ Ico 35648 35712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22416893082269868764994024316 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35584_35712 :
    (∑ n ∈ Ico 35584 35712, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 35584 35712, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 35584 35712, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1541592 : ℤ) ∧
    (∑ n ∈ Ico 35584 35712, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30831878870001109672102353859 : ℤ) := by
  rcases cdemPrefixStats_35584_35648 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35648_35712 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35584 ≤ 35648) (by norm_num : 35648 ≤ 35712), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35584 ≤ 35648) (by norm_num : 35648 ≤ 35712), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35584 ≤ 35648) (by norm_num : 35648 ≤ 35712), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35584 ≤ 35648) (by norm_num : 35648 ≤ 35712), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35712_35776 :
    (∑ n ∈ Ico 35712 35776, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 35712 35776, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 35712 35776, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-699824 : ℤ) ∧
    (∑ n ∈ Ico 35712 35776, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13996582385496724178016669258 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35776_35840 :
    (∑ n ∈ Ico 35776 35840, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 35776 35840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 35776 35840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (977578 : ℤ) ∧
    (∑ n ∈ Ico 35776 35840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19551592898165240303282272369 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35712_35840 :
    (∑ n ∈ Ico 35712 35840, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 35712 35840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 35712 35840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (277754 : ℤ) ∧
    (∑ n ∈ Ico 35712 35840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5555010512668516125265603111 : ℤ) := by
  rcases cdemPrefixStats_35712_35776 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35776_35840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35712 ≤ 35776) (by norm_num : 35776 ≤ 35840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35712 ≤ 35776) (by norm_num : 35776 ≤ 35840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35712 ≤ 35776) (by norm_num : 35776 ≤ 35840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35712 ≤ 35776) (by norm_num : 35776 ≤ 35840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35584_35840 :
    (∑ n ∈ Ico 35584 35840, mobiusTreeValue 16 mobiusTable1200001 n) = (13 : ℤ) ∧
    (∑ n ∈ Ico 35584 35840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 35584 35840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1819346 : ℤ) ∧
    (∑ n ∈ Ico 35584 35840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (36386889382669625797367956970 : ℤ) := by
  rcases cdemPrefixStats_35584_35712 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35712_35840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35584 ≤ 35712) (by norm_num : 35712 ≤ 35840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35584 ≤ 35712) (by norm_num : 35712 ≤ 35840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35584 ≤ 35712) (by norm_num : 35712 ≤ 35840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35584 ≤ 35712) (by norm_num : 35712 ≤ 35840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35328_35840 :
    (∑ n ∈ Ico 35328 35840, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 35328 35840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (312 : ℕ) ∧
    (∑ n ∈ Ico 35328 35840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2244939 : ℤ) ∧
    (∑ n ∈ Ico 35328 35840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44898735877477355846517356459 : ℤ) := by
  rcases cdemPrefixStats_35328_35584 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35584_35840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35328 ≤ 35584) (by norm_num : 35584 ≤ 35840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35328 ≤ 35584) (by norm_num : 35584 ≤ 35840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35328 ≤ 35584) (by norm_num : 35584 ≤ 35840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35328 ≤ 35584) (by norm_num : 35584 ≤ 35840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34816_35840 :
    (∑ n ∈ Ico 34816 35840, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 34816 35840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 34816 35840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2551696 : ℤ) ∧
    (∑ n ∈ Ico 34816 35840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (51033841632130777121334254269 : ℤ) := by
  rcases cdemPrefixStats_34816_35328 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35328_35840 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34816 ≤ 35328) (by norm_num : 35328 ≤ 35840), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34816 ≤ 35328) (by norm_num : 35328 ≤ 35840), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 35328) (by norm_num : 35328 ≤ 35840), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 35328) (by norm_num : 35328 ≤ 35840), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35840_35904 :
    (∑ n ∈ Ico 35840 35904, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 35840 35904, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 35840 35904, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (140015 : ℤ) ∧
    (∑ n ∈ Ico 35840 35904, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2800353240465511870601425432 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35904_35968 :
    (∑ n ∈ Ico 35904 35968, mobiusTreeValue 16 mobiusTable1200001 n) = (11 : ℤ) ∧
    (∑ n ∈ Ico 35904 35968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 35904 35968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1530179 : ℤ) ∧
    (∑ n ∈ Ico 35904 35968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (30603703909087745282014191709 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35840_35968 :
    (∑ n ∈ Ico 35840 35968, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 35840 35968, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 35840 35968, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1670194 : ℤ) ∧
    (∑ n ∈ Ico 35840 35968, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (33404057149553257152615617141 : ℤ) := by
  rcases cdemPrefixStats_35840_35904 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35904_35968 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35840 ≤ 35904) (by norm_num : 35904 ≤ 35968), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35840 ≤ 35904) (by norm_num : 35904 ≤ 35968), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 35904) (by norm_num : 35904 ≤ 35968), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 35904) (by norm_num : 35904 ≤ 35968), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35968_36032 :
    (∑ n ∈ Ico 35968 36032, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 35968 36032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 35968 36032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1111784 : ℤ) ∧
    (∑ n ∈ Ico 35968 36032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-22235798199076028355331645827 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36032_36096 :
    (∑ n ∈ Ico 36032 36096, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 36032 36096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 36032 36096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-555037 : ℤ) ∧
    (∑ n ∈ Ico 36032 36096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11100776441471993679600282177 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_35968_36096 :
    (∑ n ∈ Ico 35968 36096, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 35968 36096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 35968 36096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1666821 : ℤ) ∧
    (∑ n ∈ Ico 35968 36096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-33336574640548022034931928004 : ℤ) := by
  rcases cdemPrefixStats_35968_36032 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36032_36096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35968 ≤ 36032) (by norm_num : 36032 ≤ 36096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35968 ≤ 36032) (by norm_num : 36032 ≤ 36096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35968 ≤ 36032) (by norm_num : 36032 ≤ 36096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35968 ≤ 36032) (by norm_num : 36032 ≤ 36096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35840_36096 :
    (∑ n ∈ Ico 35840 36096, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 35840 36096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 35840 36096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3373 : ℤ) ∧
    (∑ n ∈ Ico 35840 36096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (67482509005235117683689137 : ℤ) := by
  rcases cdemPrefixStats_35840_35968 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35968_36096 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35840 ≤ 35968) (by norm_num : 35968 ≤ 36096), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35840 ≤ 35968) (by norm_num : 35968 ≤ 36096), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 35968) (by norm_num : 35968 ≤ 36096), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 35968) (by norm_num : 35968 ≤ 36096), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36096_36160 :
    (∑ n ∈ Ico 36096 36160, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 36096 36160, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 36096 36160, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1107711 : ℤ) ∧
    (∑ n ∈ Ico 36096 36160, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22154369792491281682147131293 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36160_36224 :
    (∑ n ∈ Ico 36160 36224, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 36160 36224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 36160 36224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276308 : ℤ) ∧
    (∑ n ∈ Ico 36160 36224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5526163087536109563683054095 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36096_36224 :
    (∑ n ∈ Ico 36096 36224, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 36096 36224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 36096 36224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (831403 : ℤ) ∧
    (∑ n ∈ Ico 36096 36224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16628206704955172118464077198 : ℤ) := by
  rcases cdemPrefixStats_36096_36160 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36160_36224 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36096 ≤ 36160) (by norm_num : 36160 ≤ 36224), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36096 ≤ 36160) (by norm_num : 36160 ≤ 36224), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36096 ≤ 36160) (by norm_num : 36160 ≤ 36224), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36096 ≤ 36160) (by norm_num : 36160 ≤ 36224), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36224_36288 :
    (∑ n ∈ Ico 36224 36288, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 36224 36288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 36224 36288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-340 : ℤ) ∧
    (∑ n ∈ Ico 36224 36288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6770684963289624081089514 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36288_36352 :
    (∑ n ∈ Ico 36288 36352, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 36288 36352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 36288 36352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275737 : ℤ) ∧
    (∑ n ∈ Ico 36288 36352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5514725061909387536813761079 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36224_36352 :
    (∑ n ∈ Ico 36224 36352, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 36224 36352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 36224 36352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (275397 : ℤ) ∧
    (∑ n ∈ Ico 36224 36352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5507954376946097912732671565 : ℤ) := by
  rcases cdemPrefixStats_36224_36288 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36288_36352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36224 ≤ 36288) (by norm_num : 36288 ≤ 36352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36224 ≤ 36288) (by norm_num : 36288 ≤ 36352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36224 ≤ 36288) (by norm_num : 36288 ≤ 36352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36224 ≤ 36288) (by norm_num : 36288 ≤ 36352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36096_36352 :
    (∑ n ∈ Ico 36096 36352, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 36096 36352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 36096 36352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1106800 : ℤ) ∧
    (∑ n ∈ Ico 36096 36352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22136161081901270031196748763 : ℤ) := by
  rcases cdemPrefixStats_36096_36224 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36224_36352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36096 ≤ 36224) (by norm_num : 36224 ≤ 36352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36096 ≤ 36224) (by norm_num : 36224 ≤ 36352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36096 ≤ 36224) (by norm_num : 36224 ≤ 36352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36096 ≤ 36224) (by norm_num : 36224 ≤ 36352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35840_36352 :
    (∑ n ∈ Ico 35840 36352, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 35840 36352, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 35840 36352, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1110173 : ℤ) ∧
    (∑ n ∈ Ico 35840 36352, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (22203643590906505148880437900 : ℤ) := by
  rcases cdemPrefixStats_35840_36096 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36096_36352 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35840 ≤ 36096) (by norm_num : 36096 ≤ 36352), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35840 ≤ 36096) (by norm_num : 36096 ≤ 36352), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 36096) (by norm_num : 36096 ≤ 36352), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 36096) (by norm_num : 36096 ≤ 36352), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36352_36416 :
    (∑ n ∈ Ico 36352 36416, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 36352 36416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 36352 36416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (549633 : ℤ) ∧
    (∑ n ∈ Ico 36352 36416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (10992717496936937656906850703 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36416_36480 :
    (∑ n ∈ Ico 36416 36480, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 36416 36480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 36416 36480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (412019 : ℤ) ∧
    (∑ n ∈ Ico 36416 36480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8240389840849024123042683656 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36352_36480 :
    (∑ n ∈ Ico 36352 36480, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 36352 36480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 36352 36480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (961652 : ℤ) ∧
    (∑ n ∈ Ico 36352 36480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19233107337785961779949534359 : ℤ) := by
  rcases cdemPrefixStats_36352_36416 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36416_36480 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36352 ≤ 36416) (by norm_num : 36416 ≤ 36480), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36352 ≤ 36416) (by norm_num : 36416 ≤ 36480), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36352 ≤ 36416) (by norm_num : 36416 ≤ 36480), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36352 ≤ 36416) (by norm_num : 36416 ≤ 36480), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36480_36544 :
    (∑ n ∈ Ico 36480 36544, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 36480 36544, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 36480 36544, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (403 : ℤ) ∧
    (∑ n ∈ Ico 36480 36544, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8100335645316788224918224 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36544_36608 :
    (∑ n ∈ Ico 36544 36608, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 36544 36608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 36544 36608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2050643 : ℤ) ∧
    (∑ n ∈ Ico 36544 36608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41012973757406658920399286223 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36480_36608 :
    (∑ n ∈ Ico 36480 36608, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 36480 36608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 36480 36608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2050240 : ℤ) ∧
    (∑ n ∈ Ico 36480 36608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-41004873421761342132174367999 : ℤ) := by
  rcases cdemPrefixStats_36480_36544 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36544_36608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36480 ≤ 36544) (by norm_num : 36544 ≤ 36608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36480 ≤ 36544) (by norm_num : 36544 ≤ 36608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36480 ≤ 36544) (by norm_num : 36544 ≤ 36608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36480 ≤ 36544) (by norm_num : 36544 ≤ 36608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36352_36608 :
    (∑ n ∈ Ico 36352 36608, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 36352 36608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 36352 36608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1088588 : ℤ) ∧
    (∑ n ∈ Ico 36352 36608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-21771766083975380352224833640 : ℤ) := by
  rcases cdemPrefixStats_36352_36480 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36480_36608 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36352 ≤ 36480) (by norm_num : 36480 ≤ 36608), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36352 ≤ 36480) (by norm_num : 36480 ≤ 36608), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36352 ≤ 36480) (by norm_num : 36480 ≤ 36608), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36352 ≤ 36480) (by norm_num : 36480 ≤ 36608), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36608_36672 :
    (∑ n ∈ Ico 36608 36672, mobiusTreeValue 16 mobiusTable1200001 n) = (10 : ℤ) ∧
    (∑ n ∈ Ico 36608 36672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 36608 36672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1364911 : ℤ) ∧
    (∑ n ∈ Ico 36608 36672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27298323000111206544443850664 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36672_36736 :
    (∑ n ∈ Ico 36672 36736, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 36672 36736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 36672 36736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-409188 : ℤ) ∧
    (∑ n ∈ Ico 36672 36736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8183734672496159367248759147 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36608_36736 :
    (∑ n ∈ Ico 36608 36736, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 36608 36736, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 36608 36736, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (955723 : ℤ) ∧
    (∑ n ∈ Ico 36608 36736, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (19114588327615047177195091517 : ℤ) := by
  rcases cdemPrefixStats_36608_36672 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36672_36736 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36608 ≤ 36672) (by norm_num : 36672 ≤ 36736), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36608 ≤ 36672) (by norm_num : 36672 ≤ 36736), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36608 ≤ 36672) (by norm_num : 36672 ≤ 36736), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36608 ≤ 36672) (by norm_num : 36672 ≤ 36736), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36736_36800 :
    (∑ n ∈ Ico 36736 36800, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 36736 36800, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 36736 36800, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (41 : ℤ) ∧
    (∑ n ∈ Ico 36736 36800, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (812395630326740633384086 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36800_36864 :
    (∑ n ∈ Ico 36800 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 36800 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 36800 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271280 : ℤ) ∧
    (∑ n ∈ Ico 36800 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5425568843103357694775712191 : ℤ) := by
  decide +kernel

private theorem cdemPrefixStats_36736_36864 :
    (∑ n ∈ Ico 36736 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 36736 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 36736 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-271239 : ℤ) ∧
    (∑ n ∈ Ico 36736 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5424756447473030954142328105 : ℤ) := by
  rcases cdemPrefixStats_36736_36800 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36800_36864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36736 ≤ 36800) (by norm_num : 36800 ≤ 36864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36736 ≤ 36800) (by norm_num : 36800 ≤ 36864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36736 ≤ 36800) (by norm_num : 36800 ≤ 36864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36736 ≤ 36800) (by norm_num : 36800 ≤ 36864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36608_36864 :
    (∑ n ∈ Ico 36608 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 36608 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 36608 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (684484 : ℤ) ∧
    (∑ n ∈ Ico 36608 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13689831880142016223052763412 : ℤ) := by
  rcases cdemPrefixStats_36608_36736 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36736_36864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36608 ≤ 36736) (by norm_num : 36736 ≤ 36864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36608 ≤ 36736) (by norm_num : 36736 ≤ 36864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36608 ≤ 36736) (by norm_num : 36736 ≤ 36864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36608 ≤ 36736) (by norm_num : 36736 ≤ 36864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_36352_36864 :
    (∑ n ∈ Ico 36352 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 36352 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 36352 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-404104 : ℤ) ∧
    (∑ n ∈ Ico 36352 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8081934203833364129172070228 : ℤ) := by
  rcases cdemPrefixStats_36352_36608 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36608_36864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 36352 ≤ 36608) (by norm_num : 36608 ≤ 36864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 36352 ≤ 36608) (by norm_num : 36608 ≤ 36864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 36352 ≤ 36608) (by norm_num : 36608 ≤ 36864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 36352 ≤ 36608) (by norm_num : 36608 ≤ 36864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_35840_36864 :
    (∑ n ∈ Ico 35840 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 35840 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (625 : ℕ) ∧
    (∑ n ∈ Ico 35840 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (706069 : ℤ) ∧
    (∑ n ∈ Ico 35840 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (14121709387073141019708367672 : ℤ) := by
  rcases cdemPrefixStats_35840_36352 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_36352_36864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 35840 ≤ 36352) (by norm_num : 36352 ≤ 36864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 35840 ≤ 36352) (by norm_num : 36352 ≤ 36864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 36352) (by norm_num : 36352 ≤ 36864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 35840 ≤ 36352) (by norm_num : 36352 ≤ 36864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_34816_36864 :
    (∑ n ∈ Ico 34816 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 34816 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1247 : ℕ) ∧
    (∑ n ∈ Ico 34816 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3257765 : ℤ) ∧
    (∑ n ∈ Ico 34816 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (65155551019203918141042621941 : ℤ) := by
  rcases cdemPrefixStats_34816_35840 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_35840_36864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 34816 ≤ 35840) (by norm_num : 35840 ≤ 36864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 34816 ≤ 35840) (by norm_num : 35840 ≤ 36864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 35840) (by norm_num : 35840 ≤ 36864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 34816 ≤ 35840) (by norm_num : 35840 ≤ 36864), hR1, hR2] <;> norm_num

private theorem cdemPrefixStats_32768_36864 :
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5120722 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-102414897385000683505284752836 : ℤ) := by
  rcases cdemPrefixStats_32768_34816 with ⟨hM1, hS1, hF1, hR1⟩
  rcases cdemPrefixStats_34816_36864 with ⟨hM2, hS2, hF2, hR2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n)
      (by norm_num : 32768 ≤ 34816) (by norm_num : 34816 ≤ 36864), hM1, hM2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => (mobiusTreeValue 16 mobiusTable1200001 n).natAbs)
      (by norm_num : 32768 ≤ 34816) (by norm_num : 34816 ≤ 36864), hS1, hS2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 34816) (by norm_num : 34816 ≤ 36864), hF1, hF2] <;> norm_num
  · rw [← Finset.sum_Ico_consecutive (fun n : ℕ => mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ))
      (by norm_num : 32768 ≤ 34816) (by norm_num : 34816 ≤ 36864), hR1, hR2] <;> norm_num

theorem cdemPrefixGroup008_checked_complete :
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5120722 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-102414897385000683505284752836 : ℤ) := cdemPrefixStats_32768_36864
end Helfgott
#print axioms Helfgott.cdemPrefixGroup008_checked_complete

open Helfgott Finset
open scoped BigOperators

theorem solution :
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5120722 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-102414897385000683505284752836 : ℤ) := Helfgott.cdemPrefixGroup008_checked_complete
#print axioms solution
