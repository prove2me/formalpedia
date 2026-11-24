-- Prove2me | solution 1 for GlobalTheory.map_dmonOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:53.986511+00:00
-- url     : https://prove2.me/submissions/fa3cb559-a273-4cc7-ad34-602f97cadb4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Theorems.Thm_GlobalTheory_InvDerMap_map_Dof_iterate

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (F : Fin d → PS R 2 d)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ (DmonOf F u m f) =
      DmonOf (fun i => MvPowerSeries.map φ (F i)) (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, InvDerMap.map_Dof_iterate, ih]
end GlobalTheory
