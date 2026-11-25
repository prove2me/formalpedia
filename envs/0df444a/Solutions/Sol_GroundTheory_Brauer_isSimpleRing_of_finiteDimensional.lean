-- Prove2me | solution 1 for GroundTheory.Brauer.isSimpleRing_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:14.958344+00:00
-- url     : https://prove2.me/submissions/70abed4c-5c0e-4dc2-919f-cee046a83dcf

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting

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
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
namespace GroundTheory.Brauer
theorem _root_.solution (S : Subalgebra K D) [FiniteDimensional K S] :
    IsSimpleRing S :=
  letI := divisionRingOfFiniteDimensional S
  DivisionRing.isSimpleRing S
end GroundTheory.Brauer
