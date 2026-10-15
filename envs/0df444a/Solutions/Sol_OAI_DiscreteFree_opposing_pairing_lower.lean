-- Prove2me | solution 1 for OAI.DiscreteFree.opposing_pairing_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:27:47.805291+00:00
-- url     : https://prove2.me/submissions/3ed7b871-0a52-42c7-8c7f-ba74c5fbf00a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/SignedTests.lean:L76-L97
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.opposing_pairing_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests

-- ---- from OAI.Analysis.LipschitzFree.SignedTests ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

/-!
# Signed variation, scalar extension, and incidence averaging
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section Records

variable {D S : Type*}

end Records

section SignedTests

variable {S : Type*} [Fintype S]

theorem pairing_error_le (μ f b : S → ℝ) (E : Set S) (C : ℝ)
    (heq : ∀ j, j ∉ E → f j = b j)
    (hbound : ∀ j, |f j - b j| ≤ C) :
    |pairing μ f - pairing μ b| ≤ C * variationOn μ E := by
  classical
  unfold pairing variationOn
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    |∑ j, (μ j * f j - μ j * b j)| ≤
        ∑ j, |μ j * f j - μ j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, C * (if j ∈ E then |μ j| else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ E
      · rw [ite_eq_left hj, ← mul_sub, abs_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hbound j) (abs_nonneg _)
      · simp [hj, heq j hj]

theorem opposing_pairing_lower (μ ν f b c : S → ℝ) (E F : Set S) (L : ℝ)
    (hf : ∀ j, |f j| ≤ L)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (he : ∀ j, j ∉ E → f j = b j)
    (hF : ∀ j, j ∉ F → f j = -c j) :
    pairing μ b + pairing ν c - 2 * L * (variationOn μ E + variationOn ν F) ≤
      pairing μ f - pairing ν f := by
  have h₁ := pairing_error_le μ f b E (2 * L) he (fun j => by
    have := abs_sub (f j) (b j)
    rw [abs_of_nonneg (hb j).1] at this
    linarith [hf j, (hb j).2])
  have h₂ := pairing_error_le ν f (fun j => -c j) F (2 * L) hF
    (fun j => by
      have := abs_sub (f j) (-c j)
      rw [abs_neg, abs_of_nonneg (hc j).1] at this
      linarith [hf j, (hc j).2])
  have hneg : pairing ν (fun j => -c j) = -pairing ν c := by
    simp [pairing, Finset.sum_neg_distrib]
  rw [hneg] at h₂
  have h₁' := (abs_le.mp h₁).1
  have h₂' := (abs_le.mp h₂).2
  nlinarith

end SignedTests
section

variable {N : Type*} [MetricSpace N]

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

end DiscreteFree

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.DiscreteFree.opposing_pairing_lower := @_root_.OAI.DiscreteFree.opposing_pairing_lower
