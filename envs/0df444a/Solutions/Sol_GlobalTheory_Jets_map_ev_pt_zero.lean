-- Prove2me | solution 1 for GlobalTheory.Jets.map_ev_pt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:51.664658+00:00
-- url     : https://prove2.me/submissions/fc04874b-3d40-4dca-96c4-b93c27888a5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Theorems.Thm_GlobalTheory_Jets_hasSubst_pt_zero

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
open GlobalTheory GlobalTheory.Jets
namespace GlobalTheory.Jets
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (φ : R →+* S)
    (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d))]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j <;> simp [pt]
end GlobalTheory.Jets
