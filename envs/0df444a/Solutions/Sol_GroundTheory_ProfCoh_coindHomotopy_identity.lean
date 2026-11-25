-- Prove2me | solution 1 for GroundTheory.ProfCoh.coindHomotopy_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:13.862645+00:00
-- url     : https://prove2.me/submissions/2e60863b-d954-4044-ac23-3c1bd63a37f4

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Theorems.Thm_GroundTheory_ProfCoh_coindHomotopy_identity_apply

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
open CategoryTheory groupCohomology Filter Topology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {X : Type u} [AddCommGroup X] [Module k X]
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ)
    (f : locallyConstantCochains (discreteCoind k G X) (n + 1)) :
    (dLocallyConstant (discreteCoind k G X) n).hom (coindHomotopy k X n f) +
      coindHomotopy k X (n + 1) ((dLocallyConstant (discreteCoind k G X) (n + 1)).hom f) = f := by
  apply Subtype.ext
  funext g
  apply LocallyConstant.ext
  intro x
  exact coindHomotopy_identity_apply (k := k) f.1 _ _ (fun _ _ => rfl) (fun _ _ => rfl) g x
end GroundTheory.ProfCoh
