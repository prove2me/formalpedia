-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:58:15.031241+00:00
-- url     : https://prove2.me/submissions/5077ecd6-2d51-47e6-a068-78042324f819

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L471-L484
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem floor_relative_bounds {a z b : ℝ} (ha : 0 < a) (hz : 0 ≤ z) (hz' : z < 1) :
    ⌊b+a*z⌋-⌊b⌋ ∈ Finset.Icc (0 : ℤ) ⌈a⌉ := by
  apply Finset.mem_Icc.mpr
  constructor
  · have h := Int.floor_le_floor (show b ≤ b+a*z by nlinarith)
    omega
  · have hlt : b+a*z < ((⌊b⌋+⌈a⌉+1 : ℤ) : ℝ) := by
      push_cast
      nlinarith [Int.lt_floor_add_one b, Int.le_ceil a]
    have hh := Int.floor_lt.mpr hlt
    omega

theorem relativeLabel_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v x : ℝ) :
    relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by
  let z := x/t+v-(label t v x : ℝ)
  have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
  have hz' : z < 1 := by
    change x/t+v-(⌊x/t+v⌋ : ℝ) < 1
    linarith [Int.lt_floor_add_one (x/t+v)]
  have he : (t/s)*(label t v x : ℝ)+u-(t/s)*v+(t/s)*z = x/s+u := by
    dsimp [z]
    field_simp; ring
  have h := floor_relative_bounds (b := (t/s)*(label t v x : ℝ)+u-(t/s)*v)
    (div_pos ht hs) hz hz'
  rw [he] at h
  exact h

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem := @_root_.OAI.EntropyRateDimension.MeasureEntropy.relativeLabel_mem
