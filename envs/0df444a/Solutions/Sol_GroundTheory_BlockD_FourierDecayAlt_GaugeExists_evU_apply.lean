-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:25.750152+00:00
-- url     : https://prove2.me/submissions/25ce0089-0c09-4194-9694-910af46043e3

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial Formalism.REAL
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.GaugeExists
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists
theorem _root_.solution (u : ℂ) (p : A[X]) : evU u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
