-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_cohomologyMap_subtype_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:43.382829+00:00
-- url     : https://prove2.me/submissions/f2a468a5-bcdb-43ab-86fc-96ce522641f1

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
variable [CompactSpace G]
include hW
namespace GroundTheory.ProfCoh
theorem _root_.solution [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : cohomology A n) :
    ∃ (i : ι) (y : cohomology (A.subrepresentation (W i) (hstable i)) n),
      (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = x :=
  exists_homologyMap_eq_of_cocone (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion n)
    (subrepCochainsCocone_inj A W hW hstable _) x
end GroundTheory.ProfCoh
