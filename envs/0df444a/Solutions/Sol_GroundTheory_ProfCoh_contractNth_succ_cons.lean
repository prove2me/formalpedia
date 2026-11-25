-- Prove2me | solution 1 for GroundTheory.ProfCoh.contractNth_succ_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:44.892152+00:00
-- url     : https://prove2.me/submissions/4910834f-e834-4f68-bb49-3954132f11fe

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology Filter Topology
universe u
variable {α : Type*} {n : ℕ}
namespace GroundTheory.ProfCoh
theorem _root_.solution (op : α → α → α) (x : α) (g : Fin (n + 1) → α) (j : Fin (n + 1)) :
    Fin.contractNth j.succ op (Fin.cons x g : Fin (n + 2) → α) =
      Fin.cons x (Fin.contractNth j op g) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
    simp
  · rcases lt_trichotomy (i : ℕ) j with h | h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h)]
      simp only [Fin.cons_succ, ← Fin.succ_castSucc]
      rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h)]
      simp only [Fin.cons_succ, ← Fin.succ_castSucc]
      rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h)]
      simp only [Fin.cons_succ]
      rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
end GroundTheory.ProfCoh
