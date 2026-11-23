-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.exp_ofNat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:23.164641+00:00
-- url     : https://prove2.me/submissions/d89f5e0b-4479-47db-bbc4-4a9be7915e67

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution (n : ℕ) (p : Nat.Primes) : (ofNat n).exp p = n.factorization p := rfl
end GroundTheory.ProfCoh.Supernatural
