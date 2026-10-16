-- Prove2me | solution 1 for OAI.ShortEgyptian.frequency_bad_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:59:44.515986+00:00
-- url     : https://prove2.me/submissions/ce9d94b3-dfe5-444f-bb36-f80622990385

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean:L24-L60
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.frequency_bad_probability. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeProducts ----
namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma finite_markov {A : Type uA} [Fintype A] (f : A → ℝ) (hnonneg : ∀ a, 0 ≤ f a)
    (c : ℝ) (hc : 0 < c) :
    (𝔼 a, if c ≤ f a then (1:ℝ) else 0) ≤ (𝔼 a, f a)/c := by
  apply (le_div_iff₀ hc).mpr
  rw [Finset.expect_mul]
  apply expect_le_expect
  intro a _
  split_ifs with h
  · simpa using h
  · simpa using hnonneg a

lemma finite_union_bound {A : Type uA} {J : Type uJ} [Fintype A] [Fintype J] (P : J → A → Prop) :
    (𝔼 a, if ∃ j, P j a then (1:ℝ) else 0) ≤ ∑ j, 𝔼 a, if P j a then (1:ℝ) else 0 := by
  rw [← expect_sum_comm]
  apply expect_le_expect
  intro a _
  split_ifs with h
  · obtain ⟨j,hj⟩ := h
    have hh := single_le_sum (fun j _ => by positivity : ∀ j ∈ (univ : Finset J), 0 ≤ if P j a then (1:ℝ) else 0) (mem_univ j)
    simpa [hj] using hh
  · exact sum_nonneg (fun _ _ => by positivity)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ListSelection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma frequency_bad_probability {Ω : Type uΩ} [Fintype Ω]
    (F : Ω → ℕ → ℂ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (𝔼 ω, ‖F ω l‖^2) ≤ E) :
    (𝔼 ω, if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^10 := by
  classical
  let H := Icc 1 ⌊1/δ^4⌋₊
  have hl (l : H) :
      (𝔼 ω, if δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^6 := by
    have hh := finite_markov (fun ω => ‖F ω l‖^2)
      (fun _ => sq_nonneg _) (δ^6) (pow_pos hδ 6)
    apply le_trans (b := (𝔼 ω, if δ^6 ≤ ‖F ω l‖^2 then (1:ℝ) else 0))
    · apply expect_le_expect
      intro ω _
      split_ifs with h h'
      all_goals try norm_num
      exfalso
      apply h'
      have hd : 0 ≤ δ^3 := pow_nonneg hδ.le _
      nlinarith [sq_nonneg (‖F ω l‖-δ^3)]
    · exact hh.trans (div_le_div_of_nonneg_right (hmoment l l.property) (by positivity))
  have heq (ω : Ω) : (∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖) ↔
      (∃ l : H, δ^3 < ‖F ω l‖) := by
    constructor
    · rintro ⟨l,hl,hf⟩
      exact ⟨⟨l,hl⟩,hf⟩
    · rintro ⟨l,hf⟩
      exact ⟨l,l.property,hf⟩
  simp_rw [heq]
  have hs := finite_union_bound (fun l : H => fun ω => δ^3 < ‖F ω l‖)
  apply hs.trans
  calc
    _ ≤ ∑ _l : H, E/δ^6 := sum_le_sum (fun l _ => hl l)
    _ = (⌊1/δ^4⌋₊:ℝ)*(E/δ^6) := by simp [H,Nat.card_Icc]
    _ ≤ (1/δ^4)*(E/δ^6) := by
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (div_nonneg hE (by positivity))
    _ = _ := by field_simp

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uΩ} : type_of% @_root_.OAI.ShortEgyptian.frequency_bad_probability.{uΩ} := @_root_.OAI.ShortEgyptian.frequency_bad_probability.{uΩ}
