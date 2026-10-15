-- Prove2me | solution 1 for OAI.SquareRootDegree.cell_tuple
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:06:37.663947+00:00
-- url     : https://prove2.me/submissions/dbd6f175-d2ce-427c-a148-6cfaab60fed8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Blocks.lean:L66-L82
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.cell_tuple. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks

-- ---- from OAI.Combinatorics.BooleanFunctions.Blocks ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

theorem cell_tuple {α β κ : Type*} [Fintype κ] (F : κ → α → β) (b : κ → β) (x : α) :
    cell (fun x i => F i x) b x = ∏ i, cell (F i) (b i) x := by
  by_cases h : (fun i => F i x) = b
  · simp only [cell, h, ite_true]
    apply Eq.symm
    apply Finset.prod_eq_one
    intro i _
    rw [show F i x = b i from congrFun h i]
    simp
  · have hi : ∃ i, F i x ≠ b i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hi
    simp only [cell, h, ite_false]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem solution {α β κ : Type*} [Fintype κ] (F : κ → α → β) (b : κ → β) (x : α) :
    cell (fun x i => F i x) b x = ∏ i, cell (F i) (b i) x := by
  first
    | exact OAI.SquareRootDegree.cell_tuple F b x
    | exact OAI.SquareRootDegree.cell_tuple
    | (apply OAI.SquareRootDegree.cell_tuple <;> assumption)
    | (intros; apply OAI.SquareRootDegree.cell_tuple <;> assumption)
