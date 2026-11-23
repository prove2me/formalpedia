-- Prove2me | solution 1 for GroundTheory.Brauer.BrauerGroup.one_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:43.745977+00:00
-- url     : https://prove2.me/submissions/1232b41a-f5ed-4ab3-afec-a4085022b06b

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv

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
universe u v w
variable (K : Type u) [Field K]
variable {K}
namespace GroundTheory.Brauer
namespace BrauerGroup
theorem _root_.solution : (1 : BrauerGroup.{u, u} K) = ⟦oneCSA K⟧ := rfl
end BrauerGroup
end GroundTheory.Brauer
