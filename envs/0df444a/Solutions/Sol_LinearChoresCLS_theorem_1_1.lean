-- Prove2me | solution 1 for LinearChoresCLS.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:21:46.036101+00:00
-- url     : https://prove2.me/submissions/64ea8773-e56a-4f43-8645-834f89290ca0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LinearChoresCLS_cls_membership
import Theorems.Thm_LinearChoresCLS_theorem_2_5
import Theorems.Thm_LinearChoresCLS_reduction_figure_1
import Theorems.Thm_ConstrSOSP_searchReduces_trans

open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

/-- Restricting the target answer relation preserves a reduction when the
valid instances are unchanged. The original decoder works on every retained answer. -/
private theorem reduceToBounded {R S : SearchProblem} (h : SearchReduces R S) (k : ℕ) :
    SearchReduces R (bounded S k) := by
  obtain ⟨f, g, hf, hg, hcorrect⟩ := h
  refine ⟨f, g, hf, hg, ?_⟩
  intro x hx
  obtain ⟨hvalid, hdecode⟩ := hcorrect x hx
  exact ⟨hvalid, fun y hy => hdecode y hy.1⟩

theorem solution : ∃ k : ℕ, CLSComplete (bounded choresCESearch k) := by
  obtain ⟨k, hmember⟩ := cls_membership
  refine ⟨k, hmember, ?_⟩
  intro R hR
  have hKKT : SearchReduces R epsQKKTSearch := theorem_2_5.2 R hR
  have hCE : SearchReduces R choresCESearch :=
    ConstrSOSP.searchReduces_trans R epsQKKTSearch choresCESearch hKKT reduction_figure_1
  exact reduceToBounded hCE k
