-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteEntropy.partial_entropy_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:45:54.788018+00:00
-- url     : https://prove2.me/submissions/e2d5ede5-b411-42af-afe2-63f6202317d6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean:L235-L272
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteEntropy.partial_entropy_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_relTerm_nonneg

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

variable {J : Type v} [Fintype J]

omit [Fintype I] in
lemma partial_entropy_le (s : Finset I) {w p : I → ℝ}
    (hw : ∀ i ∈ s, 0 < w i) (hp : ∀ i ∈ s, 0 ≤ p i)
    {m : ℝ} (hm : 0 < m) (hwm : ∑ i ∈ s, w i ≤ m) :
    (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
      (∑ i ∈ s, p i) * Real.log (m / (∑ i ∈ s, p i)) := by
  let t := ∑ i ∈ s, p i
  have ht : 0 ≤ t := sum_nonneg hp
  rcases ht.eq_or_lt with ht | ht
  · have hz : ∀ i ∈ s, p i = 0 := (sum_eq_zero_iff_of_nonneg hp).1 ht.symm
    simp only [show (∑ i ∈ s, p i) = 0 from ht.symm, zero_mul]
    apply le_of_eq
    exact sum_eq_zero (fun i hi ↦ by rw [hz i hi, zero_mul])
  have hi (i : I) (his : i ∈ s) :
      p i * Real.log (w i / p i) ≤ p i * Real.log (m / t) - p i + t * w i / m := by
    rcases (hp i his).eq_or_lt with hpi | hpi
    · simp only [← hpi, zero_mul, sub_self, zero_add]
      exact (div_pos (mul_pos ht (hw i his)) hm).le
    have hq : 0 < t * w i / m := div_pos (mul_pos ht (hw i his)) hm
    have hr := relTerm_nonneg hpi.le hq.le (fun _ ↦ hq)
    have hl : Real.log (p i / (t * w i / m)) =
        Real.log (m / t) - Real.log (w i / p i) := by
      rw [Real.log_div hpi.ne' hq.ne',
        Real.log_div (mul_pos ht (hw i his)).ne' hm.ne',
        Real.log_mul ht.ne' (hw i his).ne',
        Real.log_div hm.ne' ht.ne', Real.log_div (hw i his).ne' hpi.ne']
      ring
    rw [hl] at hr
    nlinarith
  have h := sum_le_sum hi
  simp only [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_div, ← mul_sum] at h
  have hq : t * (∑ i ∈ s, w i) / m ≤ t := by
    apply (div_le_iff₀ hm).2
    exact mul_le_mul_of_nonneg_left hwm ht.le
  change (∑ i ∈ s, p i * Real.log (w i / p i)) ≤ t * Real.log (m / t)
  change (∑ i ∈ s, p i * Real.log (w i / p i)) ≤
    t * Real.log (m / t) - t + t * (∑ i ∈ s, w i) / m at h
  linarith

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.partial_entropy_le := @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.partial_entropy_le
