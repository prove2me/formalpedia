-- Prove2me | solution 1 for OAI.ForestSpace.TestBound.add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:30:50.245232+00:00
-- url     : https://prove2.me/submissions/59f825ab-f2e4-4bfe-a71f-c7af3f6fdfbf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Segments.lean:L89-L113
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.TestBound.add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments

-- ---- from OAI.Analysis.ForestSpace.Segments ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {V : Type} [PartialOrder V]

 theorem TestBound.add {u v : V → ℝ} {A B : ℝ}
    (hu : TestBound u (A ^ 2)) (hv : TestBound v (B ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B) : TestBound (u + v) ((A + B) ^ 2) := by
  intro ι inst S hS hd
  have h₁ := hu ι inst S hS hd
  have h₂ := hv ι inst S hS hd
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset ι)
    (fun i => segSum u (S i)) (fun i => segSum v (S i))
  have hs₁ : Real.sqrt (∑ i, segSum u (S i) ^ 2) ≤ A :=
    (Real.sqrt_le_iff).2 ⟨hA, h₁⟩
  have hs₂ : Real.sqrt (∑ i, segSum v (S i) ^ 2) ≤ B :=
    (Real.sqrt_le_iff).2 ⟨hB, h₂⟩
  have hc' : ∑ i, segSum u (S i) * segSum v (S i) ≤ A * B :=
    hc.trans (mul_le_mul hs₁ hs₂ (Real.sqrt_nonneg _) hA)
  have he : (∑ i, segSum (u + v) (S i) ^ 2) =
      (∑ i, segSum u (S i) ^ 2) + 2 * (∑ i, segSum u (S i) * segSum v (S i)) +
      (∑ i, segSum v (S i) ^ 2) := by
    simp only [segSum_add, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  nlinarith

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

end Geometry

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.TestBound.add := @_root_.OAI.ForestSpace.TestBound.add
