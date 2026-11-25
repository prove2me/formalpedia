-- Prove2me | solution 1 for GroundTheory.Brauer.degree_baseChangeCSA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:33:02.040688+00:00
-- url     : https://prove2.me/submissions/fb0ad7de-fe6d-4867-81c8-ab96ce717eda

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_degree_baseChange

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
theorem _root_.solution (L : Type w) [Field L] [Algebra K L] (A : CSA.{u, v} K) :
    degree L (baseChangeCSA L A) = degree K A :=
  degree_baseChange K A L
end GroundTheory.Brauer
