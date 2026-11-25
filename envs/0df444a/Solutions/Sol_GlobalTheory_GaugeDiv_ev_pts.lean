-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.ev_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:23.541983+00:00
-- url     : https://prove2.me/submissions/628ab7f3-46db-4607-900a-e88bc890f7b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution (g : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] g = g := by
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [ev, e, MvPowerSeries.subst_self]
  rfl
end GlobalTheory.GaugeDiv
