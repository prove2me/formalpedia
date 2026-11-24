-- Prove2me | solution 1 for GlobalTheory.InvDerCopiesMap.map_DmonN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:06.037427+00:00
-- url     : https://prove2.me/submissions/37916521-62b4-411a-b69b-30b89f80a897

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MapDofNIterate
import Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_DofN_iterate

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
theorem _root_.solution {d n : ℕ} (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun i => MvPowerSeries.map φ (F i)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_DofN_iterate, ih]
end GlobalTheory.InvDerCopiesMap
