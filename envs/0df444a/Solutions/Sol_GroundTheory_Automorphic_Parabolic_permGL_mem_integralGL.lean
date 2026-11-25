-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.permGL_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:39.353012+00:00
-- url     : https://prove2.me/submissions/5faee35f-bea1-4f50-808e-26b1553df608

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (w : Equiv.Perm (Fin n)) : permGL F w ∈ integralGL F n := by
  rw [mem_integralGL_iff F n]
  constructor
  · intro i j
    rw [permGL_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro i j
    rw [← map_inv, permGL_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
end GroundTheory.Automorphic.Parabolic
