-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:18:10.673921+00:00
-- url     : https://prove2.me/submissions/fc8702a3-40cc-4f05-97e6-20678948d3d1

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v x : ℝ) :
    relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by
  unfold relativeLabel label
  have h1 : ((⌊x / t + v⌋ : ℤ) : ℝ) ≤ x / t + v := Int.floor_le _
  have h2 : x / t + v < ((⌊x / t + v⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hts : 0 < t / s := div_pos ht hs
  have e : x / s = t / s * (x / t) := by field_simp
  have h3 : t / s * ((⌊x / t + v⌋ : ℤ) : ℝ) + u - t / s * v ≤ x / s + u := by
    have := mul_le_mul_of_nonneg_left (show ((⌊x / t + v⌋ : ℤ) : ℝ) - v ≤ x / t by linarith) hts.le
    rw [e]; linarith
  have h4 : x / s + u < t / s * ((⌊x / t + v⌋ : ℤ) : ℝ) + u - t / s * v + t / s := by
    have := mul_lt_mul_of_pos_left (show x / t < ((⌊x / t + v⌋ : ℤ) : ℝ) + 1 - v by linarith) hts
    rw [e]; linarith
  generalize t / s * ((⌊x / t + v⌋ : ℤ) : ℝ) + u - t / s * v = y at h3 h4 ⊢
  have h5 : ⌊y⌋ ≤ ⌊x / s + u⌋ := Int.floor_le_floor h3
  have h6 : (⌊x / s + u⌋ : ℝ) ≤ x / s + u := Int.floor_le _
  have h7 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h8 : t / s ≤ (⌈t / s⌉ : ℝ) := Int.le_ceil _
  have h9 : ((⌊x / s + u⌋ - ⌊y⌋ : ℤ) : ℝ) < ((⌈t / s⌉ + 1 : ℤ) : ℝ) := by
    push_cast; linarith
  have h10 := Int.cast_lt.mp h9
  rw [Finset.mem_Icc]
  constructor <;> omega

