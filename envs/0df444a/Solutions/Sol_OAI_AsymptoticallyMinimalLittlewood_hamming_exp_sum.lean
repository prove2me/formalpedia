-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.hamming_exp_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:30:32.098882+00:00
-- url     : https://prove2.me/submissions/8167f02f-ef69-4dc2-a885-06f4527a5ad8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L219-L234
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.hamming_exp_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- Partition function of Hamming distance on the Boolean cube. -/
theorem hamming_exp_sum {α : Type u} [Fintype α] [DecidableEq α]
    (x : α → Bool) (a : ℝ) :
    (∑ y : α → Bool, Real.exp (-a * hammingDist x y)) =
      (1 + Real.exp (-a)) ^ Fintype.card α := by
  classical
  have hcast (y : α → Bool) : (hammingDist x y : ℝ) =
      ∑ k : α, if x k ≠ y k then (1 : ℝ) else 0 := by
    exact (Finset.sum_boole (fun k ↦ x k ≠ y k) Finset.univ).symm
  simp_rw [hcast, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun k b ↦ Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0))]
  have hstep (k : α) : (∑ b : Bool, Real.exp (-a * if x k ≠ b then (1 : ℝ) else 0)) =
      1 + Real.exp (-a) := by
    cases x k <;> simp [add_comm]
  simp_rw [hstep]
  simp

open scoped ComplexConjugate
open Finset

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff


theorem solution.{u} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.hamming_exp_sum.{u} := @_root_.OAI.AsymptoticallyMinimalLittlewood.hamming_exp_sum.{u}
