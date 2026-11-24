-- Prove2me | solution 1 for GlobalTheory.InvDerCopiesMap.map_DofN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:40.863983+00:00
-- url     : https://prove2.me/submissions/ece4dcde-a868-406d-be23-5c9e5ee2b6e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MapDofNIterate
import Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_pderiv
import Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_ev_axis

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
theorem _root_.solution {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f : PS R n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  simp only [DofN, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]
end GlobalTheory.InvDerCopiesMap
