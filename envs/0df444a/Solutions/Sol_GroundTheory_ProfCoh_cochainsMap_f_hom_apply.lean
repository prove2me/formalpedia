-- Prove2me | solution 1 for GroundTheory.ProfCoh.cochainsMap_f_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:24.932808+00:00
-- url     : https://prove2.me/submissions/7a7cc2ed-e507-48ff-ad3a-eaccd148e69b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality

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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
namespace GroundTheory.ProfCoh
theorem _root_.solution (f : A ⟶ B) (n : ℕ) (c : locallyConstantCochains A n) :
    ((cochainsMap f).f n).hom c = cochainsMapLinear f n c :=
  rfl
end GroundTheory.ProfCoh
