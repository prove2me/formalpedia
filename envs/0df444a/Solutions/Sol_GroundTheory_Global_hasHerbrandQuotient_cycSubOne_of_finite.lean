-- Prove2me | solution 1 for GroundTheory.Global.hasHerbrandQuotient_cycSubOne_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:13.645798+00:00
-- url     : https://prove2.me/submissions/bd5d2668-6b89-4e45-8741-1e4f7a400f2e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Theorems.Thm_GroundTheory_Global_hasCyclicHerbrand_of_finite


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
open GroundTheory.GroupCoh
variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]
namespace GroundTheory.Global
theorem _root_.solution [Module.Finite ℤ A] (ρ : Representation ℤ G A)
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) :=
  hasCyclicHerbrand_of_finite ρ hσ
end GroundTheory.Global
