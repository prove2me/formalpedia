-- Prove2me | solution 1 for GlobalTheory.FormalLog.pderiv_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:15.475853+00:00
-- url     : https://prove2.me/submissions/1564db27-071b-4497-9af0-f019af29ac08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Theorems.Thm_GlobalTheory_FormalLog_pt_apply
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt


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
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace GlobalTheory.FormalLog
theorem _root_.solution {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv k v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  classical
  rw [pt_apply, pderiv_X]
  simp [Pi.single_apply, eq_comm]
end GlobalTheory.FormalLog
