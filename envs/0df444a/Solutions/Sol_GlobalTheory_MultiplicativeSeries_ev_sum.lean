-- Prove2me | solution 1 for GlobalTheory.MultiplicativeSeries.ev_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:00:42.536964+00:00
-- url     : https://prove2.me/submissions/17b17109-ff92-4458-8239-bb0dda52fad2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
import Theorems.Thm_GlobalTheory_GaugeAdjoint_hasSubst_pts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.MultiplicativeSeries
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ}
namespace GlobalTheory.MultiplicativeSeries
theorem _root_.solution {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) {ι : Type}
    (t : Finset ι) (f : ι → PS R m d) : ev a (∑ i ∈ t, f i) = ∑ i ∈ t, ev a (f i) := by
  unfold ev
  rw [← coe_substAlgHom (hasSubst_pts ha), map_sum]
end GlobalTheory.MultiplicativeSeries
