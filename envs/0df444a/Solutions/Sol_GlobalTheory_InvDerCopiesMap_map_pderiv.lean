-- Prove2me | solution 1 for GlobalTheory.InvDerCopiesMap.map_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:19.598231+00:00
-- url     : https://prove2.me/submissions/3340f62f-68ba-44d9-b1b1-30c891aeec0d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MapDofNIterate

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
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.InvDerCopiesMap
open MvPowerSeries
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
namespace GlobalTheory.InvDerCopiesMap
theorem _root_.solution {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]
end GlobalTheory.InvDerCopiesMap
