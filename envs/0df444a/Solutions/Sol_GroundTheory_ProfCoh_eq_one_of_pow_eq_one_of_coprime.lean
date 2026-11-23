-- Prove2me | solution 1 for GroundTheory.ProfCoh.eq_one_of_pow_eq_one_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:07.77506+00:00
-- url     : https://prove2.me/submissions/f252b607-80b0-4edd-9e7a-2493f1d9370d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure

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
variable {Q Q' : Type*} [Group Q] [Group Q']
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} {x : Q} (hx : (orderOf x).Coprime p)
    (h : x ^ p = 1) : x = 1 :=
  orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hx dvd_rfl (orderOf_dvd_of_pow_eq_one h))
end GroundTheory.ProfCoh
