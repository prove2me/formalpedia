-- Prove2me | solution 1 for GroundTheory.ProfCoh.subrepCohomology_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:24.611886+00:00
-- url     : https://prove2.me/submissions/f6560fce-d6e8-4693-bd9e-c658a8da2de4

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_FilteredHomology
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion

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
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))
variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) {i j : ι} (h : i ⟶ j) :
    (subrepCohomology A W hW hstable n).map h =
      cohomologyMap (subrepInclusion A W hW hstable (leOfHom h)) n :=
  rfl
end GroundTheory.ProfCoh
