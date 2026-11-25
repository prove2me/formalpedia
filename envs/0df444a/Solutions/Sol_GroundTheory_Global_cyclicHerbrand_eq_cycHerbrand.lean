-- Prove2me | solution 1 for GroundTheory.Global.cyclicHerbrand_eq_cycHerbrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:47.947812+00:00
-- url     : https://prove2.me/submissions/8e7e7533-62f5-4bd0-a937-8d9f110dcd0b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction
open scoped TensorProduct
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution {M : Type*} [AddCommGroup M] (ρ : Representation ℤ G M)
    (σ : G) : cyclicHerbrand ρ σ = cycHerbrand ρ σ :=
  rfl
end GroundTheory.Global
