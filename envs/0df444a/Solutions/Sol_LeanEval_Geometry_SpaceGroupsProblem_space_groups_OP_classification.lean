-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.space_groups_OP_classification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T08:43:13.832322+00:00
-- url     : https://prove2.me/submissions/8f9543a1-d11f-4225-a527-ecb0d4c75484
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_master_classification

open LeanEval.Geometry.SpaceGroupsProblem

/-- The list of `230` supplied by the master enumeration is, by its first two clauses,
a complete irredundant list for orientation-preserving affine conjugacy. -/
theorem solution :
    ∃ f : Fin 230 → CrystallographicGroup 3,
      (∀ G : CrystallographicGroup 3, ∃ i : Fin 230, AffOPEquivalent (f i).1 G.1) ∧
        (∀ i j : Fin 230, AffOPEquivalent (f i).1 (f j).1 → i = j) := by
  obtain ⟨f, hex, hsep, -, -⟩ := space_groups_master_classification
  exact ⟨f, hex, hsep⟩
