-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:43:47.988063+00:00
-- url     : https://prove2.me/submissions/6bc0fad0-097d-41ef-9e95-e72affa30dc7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/FiniteInformation.lean:L25-L58
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteInformation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace LeanBlast.CourtadeKumar

theorem finite_kl_eq_entropy_sums {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (j : A → B → ℝ) (hj : ∀ a b, 0 ≤ j a b) :
    (∑ a : A, ∑ b : B,
      if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      (∑ a : A, ∑ b : B, xlogx (j a b)) -
        (∑ a : A, xlogx (∑ b : B, j a b)) -
        (∑ b : B, xlogx (∑ a : A, j a b)) := by
  classical
  have hterm (a : A) (b : B) :
      (if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      xlogx (j a b) - j a b * Real.log (∑ z : B, j a z) -
        j a b * Real.log (∑ z : A, j z b) := by
    by_cases hp : 0 < j a b
    · have hr : 0 < ∑ z : B, j a z := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj a z) (Finset.mem_univ b))
      have hc : 0 < ∑ z : A, j z b := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj z b) (Finset.mem_univ a))
      rw [ite_eq_left hp, Real.log_div (ne_of_gt hp) (ne_of_gt (mul_pos hr hc)),
        Real.log_mul (ne_of_gt hr) (ne_of_gt hc)]
      unfold xlogx
      ring
    · have hz : j a b = 0 := le_antisymm (le_of_not_gt hp) (hj a b)
      simp [hz, xlogx]
  have hrow : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : B, j a z)) =
      ∑ a : A, xlogx (∑ b : B, j a b) := by
    simp only [xlogx, Finset.sum_mul]
  have hcol : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : A, j z b)) =
      ∑ b : B, xlogx (∑ a : A, j a b) := by
    rw [Finset.sum_comm]
    simp only [xlogx, Finset.sum_mul]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hrow, hcol]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums.{u,v} := @_root_.OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums.{u,v}
