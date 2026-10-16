-- Prove2me | solution 1 for OAI.DiscreteFree.signed_incidence_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:30:26.826645+00:00
-- url     : https://prove2.me/submissions/7b7f73e0-3958-4673-9d97-42867755675a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/SignedTests.lean:L211-L267
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.signed_incidence_obstruction. The node keeps its source
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
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

end SignedTests
section

variable {N : Type*} [MetricSpace N]

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

theorem sum_variationOn_le (μ : S → ℝ) (E : D → Set S)
    (hunique : ∀ j e f, j ∈ E e → j ∈ E f → e = f) :
    (∑ e, variationOn μ (E e)) ≤ totalVariation μ := by
  classical
  unfold variationOn totalVariation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ∃ e, j ∈ E e
  · obtain ⟨e, he⟩ := hj
    rw [Finset.sum_eq_single e]
    · simp only [ite_eq_left he, le_refl]
    · intro f _ hfe
      exact ite_eq_right (fun hf => hfe (hunique j f e hf he))
    · simp
  · have hnone : ∀ e, j ∉ E e := by simpa using hj
    simp only [ite_eq_right (hnone _), Finset.sum_const_zero]
    exact abs_nonneg _

theorem variationOn_le (μ : S → ℝ) (E : Set S) : variationOn μ E ≤ totalVariation μ := by
  classical
  unfold variationOn totalVariation
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp [abs_nonneg]

theorem signed_incidence_obstruction [Nonempty X] [Nonempty D]
    (μ : X → S → ℝ) (E : X → D → Set S) (bad : Finset X)
    (rev : (X × D) ≃ (X × D)) (p V : ℝ)
    (hp : 0 < p) (hV : 0 ≤ V)
    (hTV : ∀ x, totalVariation (μ x) ≤ V)
    (hgood : ∀ x, x ∉ bad → ∀ j e f, j ∈ E x e → j ∈ E x f → e = f)
    (hdegree : 20 * V < (Fintype.card D : ℝ))
    (hbad : 20 * V * (bad.card : ℝ) < (Fintype.card X : ℝ))
    (hedge : ∀ e : X × D,
      3 * (10 * p) / 2 - 2 * (10 * p) *
        (variationOn (μ e.1) (E e.1 e.2) +
         variationOn (μ (rev e).1) (E (rev e).1 (rev e).2)) ≤ 2 * p) : False := by
  classical
  let err : X × D → ℝ := fun e => variationOn (μ e.1) (E e.1 e.2)
  let a : ℝ := Fintype.card X
  let d : ℝ := Fintype.card D
  let b : ℝ := bad.card
  have ha : 0 < a := by dsimp [a]; exact_mod_cast Fintype.card_pos (α := X)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos (α := D)
  have hb : 0 ≤ b := by positivity
  have hvtx : ∀ x, (∑ e, err (x, e)) ≤ V + if x ∈ bad then d * V else 0 := by
    intro x
    by_cases hx : x ∈ bad
    · simp only [ite_eq_left hx]
      have hsum : (∑ e, err (x, e)) ≤ d * V := by
        calc
          _ ≤ ∑ _e : D, V := Finset.sum_le_sum (fun e _ =>
            (variationOn_le (μ x) (E x e)).trans (hTV x))
          _ = _ := by simp [d]
      linarith
    · simp only [ite_eq_right hx, add_zero]
      exact (sum_variationOn_le (μ x) (E x) (hgood x hx)).trans (hTV x)
  have hsum : (∑ e, err e) ≤ a * V + b * (d * V) := by
    calc
      _ = ∑ x, ∑ e, err (x, e) := Fintype.sum_prod_type _
      _ ≤ ∑ x, (V + if x ∈ bad then d * V else 0) :=
        Finset.sum_le_sum (fun x _ => hvtx x)
      _ = _ := by simp [Finset.sum_add_distrib, a, b]
  have hsmall : 10 * (∑ e, err e) < a * d := by
    have hd' : 20 * V < d := hdegree
    have hb' : 20 * V * b < a := hbad
    have h₁ := mul_lt_mul_of_pos_left hd' ha
    have h₂ := mul_lt_mul_of_pos_left hb' hd
    nlinarith
  have hreverse : (∑ e, err (rev e)) = ∑ e, err e := Equiv.sum_comp rev err
  have hsumedge := Finset.sum_le_sum (s := (Finset.univ : Finset (X × D)))
    (fun e _ => hedge e)
  change (∑ e, (3 * (10 * p) / 2 - 2 * (10 * p) *
      (err e + err (rev e)))) ≤ ∑ _e : X × D, 2 * p at hsumedge
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsumedge
  rw [hreverse] at hsumedge
  have hcard : (Fintype.card (X × D) : ℝ) = a * d := by simp [a, d]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsumedge
  have hap : 0 < a * d := mul_pos ha hd
  have h₃ := mul_lt_mul_of_pos_left hsmall hp
  nlinarith

end DiscreteFree

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.DiscreteFree.signed_incidence_obstruction := @_root_.OAI.DiscreteFree.signed_incidence_obstruction
