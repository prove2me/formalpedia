-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteEntropy.entropy_supported_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:47:27.147097+00:00
-- url     : https://prove2.me/submissions/d81e76bd-be65-4d6a-bd07-8a140bcb96f1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean:L293-L328
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteEntropy.entropy_supported_concentration. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_partial_entropy_le

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
lemma mul_log_div {p w : ℝ} (hp : 0 ≤ p) (hw : 0 < w) :
    p * Real.log (w / p) = p * Real.log w - p * Real.log p := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  · rw [Real.log_div hw.ne' hp.ne', mul_sub]

lemma prob_sum_on {p : I → ℝ} (hp : IsProb p) (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : ∑ i ∈ D, p i = 1 := by
  rw [← hp.2]
  exact sum_subset (subset_univ _) (fun i _ hi ↦ hs i hi)

lemma entropy_sum_on {w p : I → ℝ} (D : Finset I)
    (hs : ∀ i, i ∉ D → p i = 0) : entropy w p = ∑ i ∈ D, p i * Real.log (w i / p i) := by
  symm
  apply sum_subset (subset_univ _)
  intro i _ hi
  rw [hs i hi, zero_mul]

lemma entropy_supported_concentration (D s : Finset I) (hsD : s ⊆ D) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p) (hs : ∀ i, i ∉ D → p i = 0)
    {m M : ℝ} (hm : 1 ≤ m) (hM : 0 < M)
    (hwsmall : ∑ i ∈ s, w i ≤ m) (hwall : ∑ i ∈ D, w i ≤ M) :
    entropy w p ≤ Real.log 2 + Real.log m + (1 - ∑ i ∈ s, p i) * Real.log M := by
  classical
  let t := ∑ i ∈ s, p i
  let d := ∑ i ∈ D \ s, p i
  have ht : 0 ≤ t := sum_nonneg fun i _ ↦ hp.1 i
  have hd : 0 ≤ d := sum_nonneg fun i _ ↦ hp.1 i
  have htd : d + t = 1 := by
    dsimp [t, d]
    rw [sum_sdiff hsD, prob_sum_on hp D hs]
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hwc : (∑ i ∈ D \ s, w i) ≤ M := by
    apply le_trans _ hwall
    exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i hi _ ↦ (hw i hi).le)
  have ha := partial_entropy_le s (fun i hi ↦ hw i (hsD hi)) (fun i _ ↦ hp.1 i) hm0 hwsmall
  have hc := partial_entropy_le (D \ s) (fun i hi ↦ hw i (mem_sdiff.1 hi).1)
    (fun i _ ↦ hp.1 i) hM hwc
  have he : entropy w p ≤ d * Real.log (M / d) + t * Real.log (m / t) := by
    rw [entropy_sum_on D hs, ← sum_sdiff hsD]
    exact add_le_add hc ha
  rw [mul_log_div hd hM, mul_log_div ht hm0] at he
  have hbin : -t * Real.log t - d * Real.log d ≤ Real.log 2 := by
    have hb := Real.binEntropy_le_log_two (p := t)
    have hd' : d = 1 - t := by linarith
    rw [hd']
    simpa [Real.binEntropy, Real.log_inv] using hb
  have hl := Real.log_nonneg hm
  have ht1 : t ≤ 1 := by linarith
  have hmterm : t * Real.log m ≤ Real.log m := by nlinarith
  change entropy w p ≤ Real.log 2 + Real.log m + (1 - t) * Real.log M
  have hd' : 1 - t = d := by linarith
  rw [hd']
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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.entropy_supported_concentration.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.entropy_supported_concentration.{u}
