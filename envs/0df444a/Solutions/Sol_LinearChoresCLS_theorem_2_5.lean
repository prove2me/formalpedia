-- Prove2me | solution 1 for LinearChoresCLS.theorem_2_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:20.050473+00:00
-- url     : https://prove2.me/submissions/d139dadd-135c-440e-8b4f-a6b93106791c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT
import Theorems.Thm_UnaryQuadraticKKT_Hardness_unary_quadratic_kkt_cls_complete
import Theorems.Thm_NetworkEquilibriumCLS_LinearNash_clsHard_trans
import Theorems.Thm_LinearChoresCLS_epsQKKT_cls_membership
import Theorems.Thm_LinearChoresCLS_unary_to_epsQKKT_reduction

open NetworkEquilibriumCLS.LinearNash
open LinearChoresCLS

theorem solution :
    (∃ k : ℕ, InCLS (bounded epsQKKTSearch k)) ∧ CLSHard epsQKKTSearch := by
  refine ⟨epsQKKT_cls_membership, ?_⟩
  exact clsHard_trans
    UnaryQuadraticKKT.Hardness.unary_quadratic_kkt_cls_complete.2.1
    unary_to_epsQKKT_reduction
