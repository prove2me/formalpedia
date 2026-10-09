-- Prove2me | solution 1 for OAI.Erdos3.RelativePatchSliceConclusion.congr_input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:32:51.334509+00:00
-- url     : https://prove2.me/submissions/a803a5b0-1adb-474d-915b-31cc5f1d03aa

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchSliceScore_congr_input {X : Type*} [Fintype X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    {f g : (X → ℤ) → ℝ} (hfg : ∀ x ∈ integerBox N, f x = g x)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target A = relativePatchSliceScore S g target A := by
  apply Finset.expect_congr rfl
  intro x _
  have hx : (fun i => ((S.point x i).val : ℤ)) ∈ integerBox N := by
    rw [mem_integerBox]
    intro i
    exact ⟨by positivity, by exact_mod_cast (S.point x i).isLt⟩
  rw [hfg _ hx]

theorem RelativePatchSliceConclusion.congr_input {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f g : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hfg : ∀ x ∈ integerBox N, f x = g x) :
    RelativePatchSliceConclusion s N g target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hrank, hcost, hscore⟩ := h
  refine ⟨q, hq, S, d, A, hlength, hrank, hcost, ?_⟩
  rwa [relativePatchSliceScore_congr_input S hfg target A] at hscore

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.RelativePatchSliceConclusion.congr_input.{u_1} := @OAI.Erdos3.RelativePatchSliceConclusion.congr_input.{u_1}
