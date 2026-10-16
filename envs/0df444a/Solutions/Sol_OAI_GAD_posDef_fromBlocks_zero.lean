-- Prove2me | solution 1 for OAI.GAD.posDef_fromBlocks_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:27:41.477011+00:00
-- url     : https://prove2.me/submissions/8886eedc-cbe4-4737-a8d9-2dfb4c9c2f84

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean:L111-L136
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.posDef_fromBlocks_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetConvexity ----
namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

end GAD

open scoped ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- A direct sum of strictly positive matrices is strictly positive. -/
theorem posDef_fromBlocks_zero {D : Matrix ι ι ℂ} {E : Matrix κ κ ℂ}
    (hD : D.PosDef) (hE : E.PosDef) :
    (Matrix.fromBlocks D 0 0 E).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.IsHermitian.fromBlocks hD.isHermitian (by simp) hE.isHermitian)
  intro x hx
  have hxsplit : x = Sum.elim (fun i ↦ x (.inl i)) (fun j ↦ x (.inr j)) := by
    ext i
    cases i <;> rfl
  rw [hxsplit, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Function.star_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim]
  have hnon : (fun i ↦ x (.inl i)) ≠ 0 ∨ (fun j ↦ x (.inr j)) ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    apply hx
    rw [hxsplit, h.1, h.2]
    ext i
    cases i <;> rfl
  rcases hnon with h | h
  · exact add_pos_of_pos_of_nonneg (hD.dotProduct_mulVec_pos h)
      (hE.posSemidef.dotProduct_mulVec_nonneg _)
  · exact add_pos_of_nonneg_of_pos (hD.posSemidef.dotProduct_mulVec_nonneg _)
      (hE.dotProduct_mulVec_pos h)

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open Matrix Set


theorem solution : type_of% @_root_.OAI.GAD.posDef_fromBlocks_zero := @_root_.OAI.GAD.posDef_fromBlocks_zero
