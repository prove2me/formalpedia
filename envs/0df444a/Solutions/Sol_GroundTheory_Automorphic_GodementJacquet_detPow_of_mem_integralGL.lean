-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.detPow_of_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:40.896999+00:00
-- url     : https://prove2.me/submissions/effa4890-085b-4445-afab-1ed1c04da3f3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_ordDet_of_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_detPow_eq_qs_zpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {k : GL (Fin n) F} (hk : k ∈ integralGL F n) (s : ℂ) :
    detPow k s = 1 := by
  rw [detPow_eq_qs_zpow, ordDet_of_mem_integralGL hk, zpow_zero]
end GroundTheory.Automorphic.GodementJacquet
