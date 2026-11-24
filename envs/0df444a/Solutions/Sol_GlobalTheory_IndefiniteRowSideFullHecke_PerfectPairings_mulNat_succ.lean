-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings.mulNat_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:15.22535+00:00
-- url     : https://prove2.me/submissions/09ac6c52-ae64-41cd-aa7f-db96b72e4673

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
namespace GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (n : ℕ) :
    mulNat G (n + 1) = G.add (mulNat G n) (pt R d 0) := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
