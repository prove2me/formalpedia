-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.matrix_signing_raw
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:45:03.022433+00:00
-- url     : https://prove2.me/submissions/23f9aa3b-fa4d-4040-800d-67de9da6ea88

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L638-L719
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.matrix_signing_raw. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_discrepancy_potential_contract
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exists_partial_coloring

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

/-- Iterating the zero-start partial coloring proves the square-root logarithmic matrix bound. -/
theorem matrix_signing_raw (n : ℕ) :
    ∀ {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β], Fintype.card α = n →
      ∀ B : β → α → ℝ, (∀ i k, |B i k| ≤ 1) → Fintype.card α ≤ Fintype.card β →
      ∃ ξ : α → ℝ, (∀ k, ξ k = -1 ∨ ξ k = 1) ∧
        ∀ i, |∑ k, B i k * ξ k| ≤ 4096 * Real.sqrt ((Fintype.card α : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card α)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α β _ _ _ _ hn B hB hsR
    by_cases hn0 : n = 0
    · have hc : Fintype.card α = 0 := hn.trans hn0
      let : IsEmpty α := Fintype.card_eq_zero_iff.mp hc
      refine ⟨fun _ ↦ 1, fun _ ↦ Or.inr rfl, ?_⟩
      intro i
      simp
    have hs : 0 < Fintype.card α := by omega
    have hs0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast hs
    obtain ⟨z, hz, hfix, herr⟩ := exists_partial_coloring B hB hs hsR
    let U := {k : α // z k = 0}
    have hpartitionNat : Fintype.card U + (Finset.univ.filter fun k ↦ z k ≠ 0).card =
        Fintype.card α := by
      dsimp [U]
      rw [Fintype.card_subtype]
      exact Finset.card_filter_add_card_filter_not _
    have hpartition : (Fintype.card U : ℝ) +
        ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) = Fintype.card α := by
      exact_mod_cast hpartitionNat
    have hUbound : (Fintype.card U : ℝ) ≤ (15 / 16) * Fintype.card α := by linarith
    have hUlt : Fintype.card U < n := by
      have hh : (Fintype.card U : ℝ) < Fintype.card α := by nlinarith
      have hh' : Fintype.card U < Fintype.card α := by exact_mod_cast hh
      omega
    have hUR : Fintype.card U ≤ Fintype.card β := by
      exact (Fintype.card_subtype_le (fun k ↦ z k = 0)).trans hsR
    obtain ⟨ξ, hξ, hξerr⟩ := ih (Fintype.card U) hUlt (α := U) (β := β) rfl
      (fun i k ↦ B i k) (fun i k ↦ hB i k) hUR
    let w : α → ℝ := fun k ↦ if hk : z k = 0 then ξ ⟨k, hk⟩ else z k
    have hw (k : α) : w k = -1 ∨ w k = 1 := by
      by_cases hk : z k = 0
      · simpa only [w, dite_eq_left hk] using hξ ⟨k, hk⟩
      · simp only [w, dite_eq_right hk]
        rcases hz k with hm | hzero | hp
        · exact Or.inl hm
        · exact (hk hzero).elim
        · exact Or.inr hp
    have hsum (i : β) : (∑ k, B i k * w k) = (∑ k, B i k * z k) +
        ∑ k : U, B i k * ξ k := by
      have hpart (f : α → ℝ) : (∑ k, f k) =
          (∑ k : U, f k) + ∑ k : {k : α // z k ≠ 0}, f k :=
        (Fintype.sum_subtype_add_sum_subtype (fun k ↦ z k = 0) f).symm
      rw [hpart (fun k ↦ B i k * w k), hpart (fun k ↦ B i k * z k)]
      have hzero : (∑ k : U, B i k * z k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [k.property, mul_zero]
      have hwU : (∑ k : U, B i k * w k) = ∑ k : U, B i k * ξ k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, k.property]
      have hwc : (∑ k : {k : α // z k ≠ 0}, B i k * w k) =
          ∑ k : {k : α // z k ≠ 0}, B i k * z k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [w, k.property]
      rw [hzero, zero_add, hwU, hwc, add_comm]
    refine ⟨w, hw, fun i ↦ ?_⟩
    let P := Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    have hcontract := discrepancy_potential_contract hs0
      (show (Fintype.card α : ℝ) ≤ Fintype.card β by exact_mod_cast hsR)
      (Nat.cast_nonneg (Fintype.card U)) hUbound
    change _ ≤ (63 / 64) * P at hcontract
    rw [hsum]
    calc
      _ ≤ |∑ k, B i k * z k| + |∑ k : U, B i k * ξ k| := abs_add_le _ _
      _ ≤ 64 * P + 4096 * Real.sqrt ((Fintype.card U : ℝ) *
          Real.log (16 * Fintype.card β / Fintype.card U)) := add_le_add (herr i) (hξerr i)
      _ ≤ 64 * P + 4096 * ((63 / 64) * P) := by gcongr
      _ = _ := by change _ = 4096 * P; ring

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.matrix_signing_raw.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.matrix_signing_raw.{u,v}
