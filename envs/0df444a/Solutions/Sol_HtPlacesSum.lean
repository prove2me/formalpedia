-- Prove2me | solution 1 for HtPlacesSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:37:16.267484+00:00
-- url     : https://prove2.me/submissions/0723d731-94f4-46e8-9b56-98b890d6e468

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_PlacesOverHeightOnePrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumTheorem_HtPlacesSum
import Theorems.Thm_PI_HtPlacesSumWork_places_over_height_one_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
    [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
    [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.places_over_la 𝒜 d :=
  PI.HtPlacesSumWork.places_over_height_one_prime 𝒜 d
