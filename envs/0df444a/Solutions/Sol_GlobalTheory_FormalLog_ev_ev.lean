-- Prove2me | solution 1 for GlobalTheory.FormalLog.ev_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:58.713304+00:00
-- url     : https://prove2.me/submissions/fb8b4f11-2dcf-4f37-a674-6f5ba0c8aa56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d m n : ℕ}
namespace GlobalTheory.FormalLog
theorem _root_.solution {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  unfold ev
  rw [subst_comp_subst_apply hb.hasSubst ha.hasSubst]
end GlobalTheory.FormalLog
