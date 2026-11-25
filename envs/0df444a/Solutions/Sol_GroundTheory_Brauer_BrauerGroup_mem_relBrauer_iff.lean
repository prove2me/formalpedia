-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.mem_relBrauer_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:22.70334+00:00
-- url     : https://prove2.me/submissions/6a4b9897-2c4a-4a4e-8497-778de9273cff

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
universe u v
open GroundTheory.Brauer.BrauerGroup
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
variable {K L}
namespace GroundTheory.Brauer.BrauerGroup
theorem _root_.solution (x : BrauerGroup.{u, u} K) :
    x ∈ relBrauer K L ↔ baseChange K L x = 1 :=
  MonoidHom.mem_ker
end GroundTheory.Brauer.BrauerGroup
