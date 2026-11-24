-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_killed_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:30.648872+00:00
-- url     : https://prove2.me/submissions/e422af90-2c47-4c6a-a19f-68da34cbd921

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_map_mem_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (killed I M) ≤ Module.rank ℂ (killed I N) := by
  refine LinearMap.rank_le_of_injective
    ((f.restrictScalars ℂ).restrict (p := killed I M) (q := killed I N)
      (fun m hm => map_mem_killed I f hm)) ?_
  intro a b hab
  exact Subtype.ext (hf (congrArg Subtype.val hab))
end GlobalTheory.SemisimpleCount
