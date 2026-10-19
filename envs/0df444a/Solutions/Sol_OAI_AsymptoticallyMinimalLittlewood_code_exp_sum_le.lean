-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.code_exp_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:24:55.214388+00:00
-- url     : https://prove2.me/submissions/4c28d57e-c0df-4cd3-8808-7064162831d5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L173-L197
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.code_exp_sum_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_int_geometric_sum_le

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Each integer code has exponentially decaying weight. -/
theorem int_exp_sum_le (S : Finset ℤ) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ z ∈ S, Real.exp (-a * |(z : ℝ)|)) ≤ Real.exp (4 * Real.exp (-a)) := by
  have heq (z : ℤ) : Real.exp (-a * |(z : ℝ)|) = Real.exp (-a) ^ z.natAbs := by
    have hc : (z.natAbs : ℝ) = |(z : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    rw [← hc, mul_comm, Real.exp_nat_mul]
  simp_rw [heq]
  exact int_geometric_sum_le S (Real.exp_pos _).le ha

/-- Finite families of quantization codes inherit a product partition bound. -/
theorem code_exp_sum_le {β : Type v} [Fintype β] [DecidableEq β]
    (C : Finset (β → ℤ)) (a : ℝ) (ha : Real.exp (-a) ≤ 1 / 2) :
    (∑ c ∈ C, Real.exp (-a * ∑ i, |(c i : ℝ)|)) ≤
      Real.exp (4 * Fintype.card β * Real.exp (-a)) := by
  classical
  let S : β → Finset ℤ := fun i ↦ C.image (fun c ↦ c i)
  have hsub : C ⊆ Fintype.piFinset S := by
    intro c hc
    exact Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_image.mpr ⟨c, hc, rfl⟩
  calc
    _ ≤ ∑ c ∈ Fintype.piFinset S, Real.exp (-a * ∑ i, |(c i : ℝ)|) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ (Real.exp_pos _).le)
    _ = ∏ i : β, ∑ z ∈ S i, Real.exp (-a * |(z : ℝ)|) := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      exact (Finset.prod_univ_sum S (fun _ z ↦ Real.exp (-a * |(z : ℝ)|))).symm
    _ ≤ ∏ _i : β, Real.exp (4 * Real.exp (-a)) := by
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi; exact int_exp_sum_le (S i) a ha
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{v} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.code_exp_sum_le.{v} := @_root_.OAI.AsymptoticallyMinimalLittlewood.code_exp_sum_le.{v}
