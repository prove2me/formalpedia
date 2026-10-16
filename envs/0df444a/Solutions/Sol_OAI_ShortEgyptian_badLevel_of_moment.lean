-- Prove2me | solution 1 for OAI.ShortEgyptian.badLevel_of_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:08:48.281091+00:00
-- url     : https://prove2.me/submissions/12323db7-dbf2-4dbf-a9e3-ec43f7e7a4d3

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/LevelSelection.lean:L35-L53
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.badLevel_of_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Theorems.Thm_OAI_ShortEgyptian_frequency_bad_sum

-- ---- from OAI.NumberTheory.ShortEgyptian.LevelSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uI uΩ uJ uA uD

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma badLevel_of_moment {I : Type uI} [Fintype I]
    (t : I → ℕ) (Q : ℕ) (X δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (∑ u ∈ scaleInterval X δ, ‖phaseAverage t Q u l‖^2) ≤ E) :
    ((badLevel t Q X δ).card:ℝ) ≤ E/δ^10 := by
  have hh := frequency_bad_sum (fun u : scaleInterval X δ => fun l => phaseAverage t Q u l) δ E hδ hE (by
    intro l hl
    rw [sum_coe_sort (scaleInterval X δ) (fun u : ℕ => ‖phaseAverage t Q u l‖^2)]
    exact hmoment l hl)
  rw [sum_coe_sort (scaleInterval X δ) (fun u : ℕ => if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage t Q u l‖ then (1:ℝ) else 0)] at hh
  convert hh using 1
  rw [badLevel, ←sum_boole]
  apply sum_congr rfl
  intro u _
  by_cases h : FourierBad t Q u δ
  · have h' : ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage t Q u l‖ := h
    simp only [ite_eq_left h,ite_eq_left h']
  · have h' : ¬∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage t Q u l‖ := h
    simp only [ite_eq_right h,ite_eq_right h']

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uI} : type_of% @_root_.OAI.ShortEgyptian.badLevel_of_moment.{uI} := @_root_.OAI.ShortEgyptian.badLevel_of_moment.{uI}
