-- Prove2me | solution 1 for MaintPOMDP.Frontier.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:15:04.181156+00:00
-- url     : https://prove2.me/submissions/e0b4a821-f2b2-4352-aa58-2a114b75baee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
import Theorems.Thm_MaintPOMDP_Frontier_theorem_1_part1
import Theorems.Thm_MaintPOMDP_Frontier_theorem_1_part2
import Theorems.Thm_MaintPOMDP_Frontier_theorem_1_part3
open Filter Topology
open MaintPOMDP.Frontier

theorem solution (M : Params) (hM : M.Standing) :
    (M.thrP ≤ M.cR → M.Solves ActSet.PR {M.uPdot} M.uFPdot) ∧
    (M.γ0 / M.γ1 * M.thrP ≤ M.cR → M.cR < M.thrP →
      M.Solves ActSet.PR {M.uPdot, M.uRPdot} M.uFPdot ∧ IsExtremeSet {M.uPdot, M.uRPdot}) ∧
    (M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP →
      ∃ mdag : ℕ, IsLeastMin M.f mdag ∧
        M.Solves ActSet.PR (M.Udag mdag) (M.f mdag + M.cF - M.cR) ∧
        IsExtremeSet (M.Udag mdag)) :=
  ⟨fun h => theorem_1_part1 M hM h, fun h1 h2 => theorem_1_part2 M hM h1 h2,
   fun h => theorem_1_part3 M hM h⟩
