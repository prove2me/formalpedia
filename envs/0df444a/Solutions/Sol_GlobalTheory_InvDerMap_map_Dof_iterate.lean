-- Prove2me | solution 1 for GlobalTheory.InvDerMap.map_Dof_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:16.718213+00:00
-- url     : https://prove2.me/submissions/0abc31c5-e0b5-47b3-99dd-8b84d2b2ac14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Theorems.Thm_GlobalTheory_InvDerMap_map_Dof

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
theorem _root_.solution {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ ((Dof F u)^[n] f) =
      (Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)))^[n] (MvPowerSeries.map φ f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_Dof, ih]
end GlobalTheory.InvDerMap
