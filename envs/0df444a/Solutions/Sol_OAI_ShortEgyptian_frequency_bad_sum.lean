-- Prove2me | solution 1 for OAI.ShortEgyptian.frequency_bad_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:02:00.770379+00:00
-- url     : https://prove2.me/submissions/4420e5ec-f15b-49c8-bcbb-974d5abdf45f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean:L78-L94
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.frequency_bad_sum. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_frequency_bad_probability

-- ---- from OAI.NumberTheory.ShortEgyptian.ListSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma frequency_bad_sum {Ω : Type uΩ} [Fintype Ω]
    (F : Ω → ℕ → ℂ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊, (∑ ω, ‖F ω l‖^2) ≤ E) :
    (∑ ω, if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^10 := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h => simp only [univ_eq_empty, sum_empty]; positivity
  | inr h =>
    have hN : (0:ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
    have hh := frequency_bad_probability F δ (E/Fintype.card Ω) hδ (by positivity) (by
      intro l hl
      rw [Fintype.expect_eq_sum_div_card]
      exact div_le_div_of_nonneg_right (hmoment l hl) hN.le)
    rw [Fintype.expect_eq_sum_div_card] at hh
    have heq : (E/(Fintype.card Ω:ℝ))/δ^10 = (E/δ^10)/Fintype.card Ω := by ring
    rw [heq] at hh
    exact (div_le_div_iff_of_pos_right hN).mp hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uΩ} : type_of% @_root_.OAI.ShortEgyptian.frequency_bad_sum.{uΩ} := @_root_.OAI.ShortEgyptian.frequency_bad_sum.{uΩ}
