-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.dyadic_round_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:49:27.172772+00:00
-- url     : https://prove2.me/submissions/34cf5fff-01fc-4171-983f-53a18df75175

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L818-L925
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.dyadic_round_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_dyadic_potential_bound
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_matrix_signing_raw

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem matrix_signing {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
      ∀ i, |∑ k, B i k * ξ k| ≤ 8192 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card α)) := by
  obtain ⟨ξ, hξ, herr⟩ := matrix_signing_raw (Fintype.card α) rfl B hB hsR
  refine ⟨ξ, hξ, fun i ↦ (herr i).trans ?_⟩
  by_cases hs : Fintype.card α = 0
  · simp [hs]
  have hs0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hR0 : (0 : ℝ) < Fintype.card β := hs0.trans_le (by exact_mod_cast hsR)
  let x : ℝ := Fintype.card β / Fintype.card α
  have hx : 1 ≤ x := (le_div_iff₀ hs0).mpr (by simpa using (show (Fintype.card α : ℝ) ≤ Fintype.card β by exact_mod_cast hsR))
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h16 : Real.log (16 * x) ≤ 4 * Real.log (2 * x) := by
    rw [Real.log_mul (by norm_num) hx0.ne', Real.log_mul (by norm_num) hx0.ne',
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hsq : Real.sqrt ((Fintype.card α : ℝ) * Real.log (16 * x)) ≤
      2 * Real.sqrt ((Fintype.card α : ℝ) * Real.log (2 * x)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := Real.sq_sqrt (mul_nonneg hs0.le hlog2x)
    nlinarith [mul_le_mul_of_nonneg_left h16 hs0.le]
  dsimp [x] at hsq
  simp only [← mul_div_assoc] at hsq
  nlinarith

/-- Reversing a signing preserves discrepancy and allows its total sum to be nonpositive. -/
theorem matrix_signing_nonpos {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (B : β → α → ℝ) (hB : ∀ i k, |B i k| ≤ 1)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧ (∑ k, ξ k) ≤ 0 ∧
      ∀ i, |∑ k, B i k * ξ k| ≤ 8192 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card α)) := by
  obtain ⟨ξ, hξ, herr⟩ := matrix_signing B hB hsR
  by_cases hsum : (∑ k, ξ k) ≤ 0
  · exact ⟨ξ, hξ, hsum, herr⟩
  refine ⟨fun k ↦ -ξ k, ?_, ?_, ?_⟩
  · intro k
    rcases hξ k with hk | hk <;> simp [hk]
  · rw [Finset.sum_neg_distrib]
    linarith
  · intro i
    simpa only [mul_neg, Finset.sum_neg_distrib, abs_neg] using herr i

/-- One mass-nonincreasing dyadic rounding step, on the exact odd coordinates. -/
theorem dyadic_round_step {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (a : α → ℕ) (j : ℕ) (ha : ∀ k, a k ≤ 2 ^ (j + 1))
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ≤ μ) :
    ∃ b : α → ℕ, (∀ k, b k ≤ 2 ^ j) ∧
      (∑ k, (b k : ℝ) / 2 ^ j) ≤ (∑ k, (a k : ℝ) / 2 ^ (j + 1)) ∧
      ∀ i, |∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))| ≤
        8192 * ((3 / 4) ^ (j + 1) * Real.sqrt
          (μ * Real.log (2 * Fintype.card β / μ))) := by
  classical
  let U := {k : α // a k % 2 = 1}
  have hUβ : Fintype.card U ≤ Fintype.card β :=
    (Fintype.card_subtype_le _).trans hαβ
  obtain ⟨ξ, hξ, hξsum, hξerr⟩ := matrix_signing_nonpos
    (fun i (k : U) ↦ A i k) (fun i k ↦ hA i k) hUβ
  let b : α → ℕ := fun k ↦ a k / 2 +
    if hk : a k % 2 = 1 then (if ξ ⟨k, hk⟩ = 1 then 1 else 0) else 0
  let ζ : α → ℝ := fun k ↦ if hk : a k % 2 = 1 then ξ ⟨k, hk⟩ else 0
  have hb (k : α) : b k ≤ 2 ^ j := by
    have hak := ha k
    rw [pow_succ] at hak
    dsimp [b]
    by_cases hk : a k % 2 = 1
    · rw [dite_eq_left hk]
      split_ifs <;> omega
    · rw [dite_eq_right hk]
      omega
  have hnumer (k : α) : 2 * (b k : ℝ) - a k = ζ k := by
    by_cases hk : a k % 2 = 1
    · dsimp [b, ζ]
      rw [dite_eq_left hk, dite_eq_left hk]
      rcases hξ ⟨k, hk⟩ with hm | hp
      · rw [hm]
        norm_num
        have hn : 2 * (a k / 2) + 1 = a k := by omega
        have hn' : 2 * ((a k / 2 : ℕ) : ℝ) + 1 = a k := by exact_mod_cast hn
        linarith
      · rw [hp]
        norm_num

        have hn : 2 * (a k / 2) + 1 = a k := by omega
        have hn' : 2 * ((a k / 2 : ℕ) : ℝ) + 1 = a k := by exact_mod_cast hn
        linarith
    · dsimp [b, ζ]
      rw [dite_eq_right hk, dite_eq_right hk]
      norm_num
      have hn : 2 * (a k / 2) = a k := by omega
      have hn' : 2 * ((a k / 2 : ℕ) : ℝ) = a k := by exact_mod_cast hn
      linarith
  have hdiff (k : α) : (b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1) =
      ζ k / 2 ^ (j + 1) := by
    rw [pow_succ]
    have hp : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp
    nlinarith [hnumer k]
  have hζsum (f : α → ℝ) : (∑ k, f k * ζ k) = ∑ k : U, f k * ξ k := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k ↦ a k % 2 = 1)]
    have hzero : (∑ k : {k : α // ¬ a k % 2 = 1}, f k * ζ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [ζ, k.property]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    simp [ζ, k.property]
  have hmass' : (∑ k, (b k : ℝ) / 2 ^ j) ≤ ∑ k, (a k : ℝ) / 2 ^ (j + 1) := by
    have hsumdiff : (∑ k, (b k : ℝ) / 2 ^ j) - (∑ k, (a k : ℝ) / 2 ^ (j + 1)) =
        (∑ k : U, ξ k) / 2 ^ (j + 1) := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [hdiff]
      rw [← Finset.sum_div]
      congr 1
      simpa using hζsum (fun _ ↦ 1)
    have hh : (∑ k : U, ξ k) / 2 ^ (j + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hξsum (by positivity)
    linarith
  have hsmass : (Fintype.card U : ℝ) ≤ 2 ^ (j + 1) * μ := by
    have hsumU : (Fintype.card U : ℝ) ≤ ∑ k : U, (a k : ℝ) := by
      calc
        _ = ∑ _k : U, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ ↦ by
          have hk : 1 ≤ a k := by have := k.property; omega
          exact_mod_cast hk
    have hsumall : (∑ k : U, (a k : ℝ)) ≤ ∑ k : α, (a k : ℝ) := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun k ↦ a k % 2 = 1) (fun k ↦ (a k : ℝ))
      have hp : 0 ≤ ∑ k : {k : α // ¬ a k % 2 = 1}, (a k : ℝ) := by positivity
      change (∑ k : U, (a k : ℝ)) + _ = _ at hh
      linarith
    rw [← Finset.sum_div] at hmass
    have hm := (div_le_iff₀ (show (0 : ℝ) < 2 ^ (j + 1) by positivity)).mp hmass
    linarith
  refine ⟨b, hb, hmass', fun i ↦ ?_⟩
  have hsum : (∑ k, A i k * ((b k : ℝ) / 2 ^ j - (a k : ℝ) / 2 ^ (j + 1))) =
      (∑ k : U, A i k * ξ k) / 2 ^ (j + 1) := by
    simp_rw [hdiff, ← mul_div_assoc]
    rw [← Finset.sum_div, hζsum]
  rw [hsum, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (j + 1))]
  calc
    _ ≤ (8192 * Real.sqrt ((Fintype.card U : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card U))) / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_right (hξerr i) (by positivity)
    _ = 8192 * (Real.sqrt ((Fintype.card U : ℝ) *
        Real.log (2 * Fintype.card β / Fintype.card U)) / 2 ^ (j + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dyadic_potential_bound hμ hμR (Nat.cast_nonneg _) (j + 1) hsmass) (by norm_num)

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.dyadic_round_step.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.dyadic_round_step.{u,v}
