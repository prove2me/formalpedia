-- Prove2me | solution 1 for Grunbaum2003.caratheodory_fin_dim
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:53:47.161253+00:00
-- url     : https://prove2.me/submissions/be59fe28-1303-4548-8f91-e6bac57d9a5e

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
open Grunbaum2003
open scoped Pointwise

theorem solution {d : ℕ}
    (S : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ S) :
    ∃ T : Finset (Fin d → ℝ), T.card ≤ d + 1 ∧ ↑T ⊆ S ∧ x ∈ convexHull ℝ ↑T := by
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  refine ⟨T,?_,Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have h := (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
  have hb := (vectorSpan ℝ (Set.range ((↑) : T → (Fin d → ℝ)))).finrank_le
  have hd : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hd] at hb
  simpa only [Fintype.card_coe] using le_trans h (Nat.add_le_add_right hb 1)
