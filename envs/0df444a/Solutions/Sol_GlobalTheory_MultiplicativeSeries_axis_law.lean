-- Prove2me | solution 1 for GlobalTheory.MultiplicativeSeries.axis_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:44.480808+00:00
-- url     : https://prove2.me/submissions/3b9c645e-31fd-41ac-8902-0e5a7147452a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pt_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_axis_pt_zero
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_axis
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_ev_ev_two


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
theorem _root_.solution (G : FGLaw R d) :
    (fun i => ev (n := 1) ![pt R d 0, 0] (G.F i)) = pt R d 0 := by
  funext i
  rw [← G.comm i, ev_ev_two (const_pt 1) (const_pt 0) const_axis, axis_pt_zero, axis_pt_one,
    G.unit i]
  rfl
end GlobalTheory.MultiplicativeSeries
