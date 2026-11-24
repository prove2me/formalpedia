-- Prove2me | solution 1 for GlobalTheory.InvDerMap.map_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:24.376646+00:00
-- url     : https://prove2.me/submissions/efa575ad-8687-46e3-aa5d-840cc5d0a728

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.InvDerMap
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
namespace GlobalTheory.InvDerMap
theorem _root_.solution {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]
end GlobalTheory.InvDerMap
