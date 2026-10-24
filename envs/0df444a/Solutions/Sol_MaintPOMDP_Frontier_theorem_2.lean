-- Prove2me | solution 1 for MaintPOMDP.Frontier.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:05:59.84787+00:00
-- url     : https://prove2.me/submissions/06027e7f-52c2-4a68-8686-98284e3a44cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
import Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part1
import Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part2_RP
import Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part2_IRP
import Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part2_PIR
import Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part3
open Filter Topology
open MaintPOMDP.Frontier

theorem solution (M : Params) (hM : M.Standing) :
    -- (1) [P]
    (M.thrP ≤ M.cR → M.Solves ActSet.PIR {M.uPdot} M.uFPdot) ∧
    -- (2) R[P], IR[P], [PIR]
    (M.γ0 / M.γ1 * M.thrP ≤ M.cR → M.cR < M.thrP →
      (M.cR / (M.cP + M.β * M.γ1 * M.cF) * M.chat ≤ M.cI →
        M.Solves ActSet.PIR {M.uPdot, M.uRPdot} M.uFPdot) ∧
      (M.γ0 / M.γ1 * (1 / M.D) * M.chat ≤ M.cI →
        M.cI < M.cR / (M.cP + M.β * M.γ1 * M.cF) * M.chat →
        M.Solves ActSet.PIR {M.uPdot, M.uRPdot, M.uIRP} M.uFPdot) ∧
      (M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat → M.PIRStructure)) ∧
    -- (3) [PR], I[PR], [PIR]
    (M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP →
      ∃ mdag : ℕ, IsLeastMin M.f mdag ∧
        ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ c2 < M.cR ∧
          (∀ c : ℝ, M.cP < c → c < M.cR →
            (c2 ≤ c →
              (M.withCI c).Solves ActSet.PIR ((M.withCI c).Udag mdag)
                ((M.withCI c).f mdag + M.cF - M.cR)) ∧
            (c1 ≤ c → c < c2 →
              ∃ nI : ℕ, (M.withCI c).Solves ActSet.PIR ((M.withCI c).UIPR mdag nI)
                ((M.withCI c).f mdag + M.cF - M.cR)) ∧
            (c < c1 → (M.withCI c).PIRStructure)) ∧
          OnFrontier ((M.withCI c2).uIdag ((M.withCI c2).f mdag)) ((M.withCI c2).Udag mdag) ∧
          ∃ m1 m2 : ℕ, (∀ m, M.f m1 ≤ M.f m) ∧ (∀ m, (M.withCI c1).g m2 ≤ (M.withCI c1).g m) ∧
            M.f m1 = (M.withCI c1).g m2) :=
  ⟨fun h => theorem_2_part1 M hM h,
   fun hlo hhi => ⟨fun hcI => theorem_2_part2_RP M hM hlo hhi hcI,
     fun h1 h2 => theorem_2_part2_IRP M hM hlo hhi h1 h2,
     fun hcI => theorem_2_part2_PIR M hM hlo hhi hcI⟩,
   fun hcR => theorem_2_part3 M hM hcR⟩
