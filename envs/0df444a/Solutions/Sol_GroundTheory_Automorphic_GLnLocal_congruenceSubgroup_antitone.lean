-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:12.015625+00:00
-- url     : https://prove2.me/submissions/53824f6d-1074-4eb6-ba89-c828d39e7b92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : Antitone (congruenceSubgroup F n) := by
  intro m m' hmm' g hg
  rw [mem_congruenceSubgroup_iff] at hg ⊢
  exact ⟨hg.1, fun i j => (hg.2 i j).trans
    (pow_le_pow_right_of_le_one' (valuation_uniformizer_lt_one F).le hmm')⟩
end GroundTheory.Automorphic.GLnLocal
