-- Prove2me | solution 1 for GlobalTheory.InvDerMap.map_Dof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:12.34627+00:00
-- url     : https://prove2.me/submissions/edd59179-adfc-4b86-a121-42496595427e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Theorems.Thm_GlobalTheory_InvDerMap_map_pderiv
import Theorems.Thm_GlobalTheory_InvDerMap_map_ev_axis

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
theorem _root_.solution {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) :
    MvPowerSeries.map φ (Dof F u f) =
      Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  simp only [Dof, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]
end GlobalTheory.InvDerMap
