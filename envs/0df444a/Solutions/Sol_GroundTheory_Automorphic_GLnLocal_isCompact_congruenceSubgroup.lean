-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:40:25.680914+00:00
-- url     : https://prove2.me/submissions/29f7ac98-8974-46ed-ad1c-195bc9c687d2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_le

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
    IsCompact (congruenceSubgroup F n m : Set (GL (Fin n) F)) :=
  (isCompact_integralGL F n).of_isClosed_subset (isClosed_congruenceSubgroup F n m)
    fun _ hx => congruenceSubgroup_le F n m hx
end GroundTheory.Automorphic.GLnLocal
