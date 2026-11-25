-- Prove2me | solution 1 for GroundTheory.Brauer.degree_tensorCSA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:07:10.597739+00:00
-- url     : https://prove2.me/submissions/139f30a4-97be-4939-a4f8-9af01aebab26

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_degree_tensorProduct

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
open Module TensorProduct
universe u v w
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution (A B : CSA.{u, v} K) :
    degree K (tensorCSA A B) = degree K A * degree K B :=
  degree_tensorProduct K A B
end GroundTheory.Brauer
