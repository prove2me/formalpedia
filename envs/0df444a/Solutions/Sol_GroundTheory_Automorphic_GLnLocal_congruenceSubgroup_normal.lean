-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:18.489802+00:00
-- url     : https://prove2.me/submissions/0f5706cb-f1d4-4e49-b5b3-4787c68a8186

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_congruenceSubgroup

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
theorem _root_.solution (m : ℕ) :
    ((congruenceSubgroup F n m).subgroupOf (integralGL F n)).Normal :=
  ⟨fun x hx k => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_congruenceSubgroup F n k.2 hx⟩
end GroundTheory.Automorphic.GLnLocal
