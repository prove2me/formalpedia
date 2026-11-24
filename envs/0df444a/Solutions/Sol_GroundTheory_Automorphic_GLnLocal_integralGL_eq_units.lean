-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.integralGL_eq_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:48.317696+00:00
-- url     : https://prove2.me/submissions/3d39a830-face-4519-bdb8-436e5887cbbe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_integralMatrices

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
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : integralGL F n = (integralMatrices F n).toSubmonoid.units := by
  ext g
  rw [mem_integralGL_iff, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Subring.mem_toSubmonoid, mem_integralMatrices, mem_integralMatrices]
end GroundTheory.Automorphic.GLnLocal
