-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isMaximalCompact_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:27.490749+00:00
-- url     : https://prove2.me/submissions/99f48cac-a039-4b63-aca5-2e0f40907542

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eq_integralGL_of_isCompact_of_le
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL


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
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : IsMaximalCompact (integralGL F n) :=
  ⟨isCompact_integralGL F n, fun _ hH' hle => eq_integralGL_of_isCompact_of_le F n hH' hle⟩
end GroundTheory.Automorphic.GLnLocal
