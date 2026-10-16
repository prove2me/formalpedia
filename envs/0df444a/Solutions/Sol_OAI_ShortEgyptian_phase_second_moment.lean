-- Prove2me | solution 1 for OAI.ShortEgyptian.phase_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:47:38.619992+00:00
-- url     : https://prove2.me/submissions/4f6f05d1-50c3-4fc7-b72e-ae52bc9d5474

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DeterministicMean.lean:L89-L132
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.phase_second_moment. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.FiniteFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uG

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem complex_sum_norm_sq {ι : Type uι} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * (starRingEnd ℂ) (f j)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_comm

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.DeterministicMean ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uα uβ

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem phase_second_moment {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α]
    (s : Finset β) (f : α → β → ℂ) (hnorm : ∀ i u, ‖f i u‖ = 1)
    (E : ℝ) (hE : 0 ≤ E)
    (hcorr : ∀ i j : α, i ≠ j →
      ‖∑ u ∈ s, f i u * (starRingEnd ℂ) (f j u)‖ ≤ E) :
    (∑ u ∈ s, ‖(∑ i, f i u) / (Fintype.card α : ℂ)‖ ^ 2) ≤
      (s.card : ℝ) / Fintype.card α + E := by
  classical
  let N := Fintype.card α
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hterm (i j : α) :
      (∑ u ∈ s, (f i u * (starRingEnd ℂ) (f j u)).re) ≤
        (if i = j then (s.card : ℝ) else 0) + E := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hnorm,
        one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith
    · rw [ite_eq_right hij, zero_add, ← Complex.re_sum]
      exact (Complex.re_le_norm _).trans (hcorr i j hij)
  have hsum : (∑ u ∈ s, ‖∑ i, f i u‖ ^ 2) ≤ (N : ℝ) * s.card + N ^ 2 * E := by
    simp_rw [complex_sum_norm_sq]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i : α, ∑ j : α, ∑ u ∈ s, (f i u * (starRingEnd ℂ) (f j u)).re := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ ≤ ∑ i : α, ∑ j : α, ((if i = j then (s.card : ℝ) else 0) + E) := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = _ := by simp [Finset.sum_add_distrib, N]; ring
  have heq : (∑ u ∈ s, ‖(∑ i, f i u) / (Fintype.card α : ℂ)‖ ^ 2) =
      (∑ u ∈ s, ‖∑ i, f i u‖ ^ 2) / (N : ℝ) ^ 2 := by
    change _ = _ / (Fintype.card α : ℝ) ^ 2
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    rw [norm_div, Complex.norm_natCast, div_pow]
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
  have halg : ((s.card : ℝ) / N + E) * (N : ℝ) ^ 2 = N * s.card + N ^ 2 * E := by
    field_simp
  rw [halg]
  exact hsum

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution.{uα,uβ} : type_of% @_root_.OAI.ShortEgyptian.phase_second_moment.{uα,uβ} := @_root_.OAI.ShortEgyptian.phase_second_moment.{uα,uβ}
