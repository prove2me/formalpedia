-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.baseChange_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:24:01.899156+00:00
-- url     : https://prove2.me/submissions/6622555f-e4f1-43b8-85bf-f43db97c45fe

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_mk
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


attribute [local simp] GroundTheory.Brauer.BrauerGroup.baseChange_mk

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v
open GroundTheory.Brauer.BrauerGroup
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
namespace GroundTheory.Brauer.BrauerGroup
theorem _root_.solution (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] :
    (baseChange L M).comp (baseChange K L) = baseChange K M := by
  ext x
  induction x using Quotient.inductionOn with
  | h A => exact Quotient.sound <| isBrauerEquivalent_of_algEquiv (baseChangeCSATower L M A)
end GroundTheory.Brauer.BrauerGroup
