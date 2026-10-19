-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.matrix_defect_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:52:52.070616+00:00
-- url     : https://prove2.me/submissions/36c35a3a-ab75-44df-a9d3-1d18dbeba294

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L968-L1041
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.matrix_defect_rounding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_dyadic_round

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Defect-sensitive rounding on a real matrix, prior to the circle discretization. -/
theorem matrix_defect_rounding {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : β → α → ℝ) (hA : ∀ i k, |A i k| ≤ 1)
    (hαβ : Fintype.card α ≤ Fintype.card β)
    (p : α → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    {μ : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ Fintype.card β)
    (hmass : (∑ k, p k) ≤ μ) :
    ∃ p' : α → ℝ, (∀ k, p' k = 0 ∨ p' k = 1) ∧ (∑ k, p' k) ≤ ∑ k, p k ∧
      ∀ i, |∑ k, A i k * (p' k - p k)| ≤
        1 + 24576 * Real.sqrt (μ * Real.log (2 * Fintype.card β / μ)) := by
  classical
  let j := Fintype.card α
  have hjNat : j ≤ 2 ^ j := by
    have hh : ∀ n : ℕ, n ≤ 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        rw [pow_succ]
        omega
    exact hh j
  have hj : (Fintype.card α : ℝ) / 2 ^ j ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    simp only [one_mul]
    exact_mod_cast hjNat
  let a : α → ℕ := fun k ↦ ⌊2 ^ j * p k⌋₊
  have ha_le (k : α) : (a k : ℝ) ≤ 2 ^ j * p k := Nat.floor_le (mul_nonneg (by positivity) (hp k).1)
  have ha_lt (k : α) : 2 ^ j * p k < (a k : ℝ) + 1 := Nat.lt_floor_add_one _
  have habound (k : α) : a k ≤ 2 ^ j := by
    have hh : (a k : ℝ) ≤ (2 : ℝ) ^ j := (ha_le k).trans
      (by nlinarith [hp k, show (0 : ℝ) ≤ 2 ^ j by positivity])
    exact_mod_cast hh
  have ha_frac (k : α) : (a k : ℝ) / 2 ^ j ≤ p k :=
    (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using ha_le k)
  have ha_err (k : α) : |(a k : ℝ) / 2 ^ j - p k| ≤ 1 / 2 ^ j := by
    rw [abs_of_nonpos (sub_nonpos.mpr (ha_frac k))]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j)).mpr
    have heq : -((a k : ℝ) / 2 ^ j - p k) * 2 ^ j = 2 ^ j * p k - a k := by
      field_simp ; ring
    rw [heq]
    linarith [ha_lt k]
  have hmass_a : (∑ k, (a k : ℝ) / 2 ^ j) ≤ ∑ k, p k :=
    Finset.sum_le_sum fun k _ ↦ ha_frac k
  have hinit (i : β) : |∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k)| ≤ 1 := by
    calc
      _ ≤ ∑ k, |A i k * ((a k : ℝ) / 2 ^ j - p k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : α, (1 : ℝ) / 2 ^ j := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact (mul_le_mul (hA i k) (ha_err k) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = (Fintype.card α : ℝ) / 2 ^ j := by simp [div_eq_mul_inv]
      _ ≤ 1 := hj
  obtain ⟨b, hb, hmassb, herrb⟩ := dyadic_round A hA hαβ hμ hμR j a habound
    (hmass_a.trans hmass)
  refine ⟨fun k ↦ (b k : ℝ), ?_, hmassb.trans hmass_a, fun i ↦ ?_⟩
  · intro k
    have hh : b k = 0 ∨ b k = 1 := by have := hb k; omega
    rcases hh with hh | hh <;> simp [hh]
  · have hsplit : (∑ k, A i k * ((b k : ℝ) - p k)) =
        (∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)) +
        ∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hsplit]
    have hroot := Real.sqrt_nonneg (μ * Real.log (2 * Fintype.card β / μ))
    calc
      _ ≤ |∑ k, A i k * ((b k : ℝ) - (a k : ℝ) / 2 ^ j)| +
          |∑ k, A i k * ((a k : ℝ) / 2 ^ j - p k)| := abs_add_le _ _
      _ ≤ 8192 * (3 * (1 - (3 / 4) ^ j) * Real.sqrt
            (μ * Real.log (2 * Fintype.card β / μ))) + 1 := add_le_add (herrb i) (hinit i)
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) j) hroot]

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u,v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.matrix_defect_rounding.{u,v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.matrix_defect_rounding.{u,v}
