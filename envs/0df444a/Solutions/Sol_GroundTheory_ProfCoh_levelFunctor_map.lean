-- Prove2me | solution 1 for GroundTheory.ProfCoh.levelFunctor_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:15.012703+00:00
-- url     : https://prove2.me/submissions/a6dc23c7-3192-4dad-ac5e-c1dd0162ae68

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs

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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : Rep.{u} k G)
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) {U V : (OpenNormalSubgroup G)ᵒᵖ} (f : U ⟶ V) :
    (levelFunctor A n).map f = transition A (leOfHom f.unop) n :=
  rfl
end GroundTheory.ProfCoh
