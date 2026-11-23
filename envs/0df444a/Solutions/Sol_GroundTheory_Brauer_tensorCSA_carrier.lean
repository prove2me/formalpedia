-- Prove2me | solution 1 for GroundTheory.Brauer.tensorCSA_carrier
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:46.333052+00:00
-- url     : https://prove2.me/submissions/337bb76f-cbd7-4e24-835f-3ef44cfe1f39

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple

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
open TensorProduct Algebra.TensorProduct
universe u v
variable {K : Type u} [Field K]
namespace GroundTheory.Brauer
theorem _root_.solution (A B : CSA.{u, v} K) : (tensorCSA A B : Type v) = (A ⊗[K] B) := rfl
end GroundTheory.Brauer
