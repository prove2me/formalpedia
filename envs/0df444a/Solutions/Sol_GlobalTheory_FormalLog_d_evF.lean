-- Prove2me | solution 1 for GlobalTheory.FormalLog.d_evF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:17.424366+00:00
-- url     : https://prove2.me/submissions/966a657b-7146-45de-abab-4aecd379aaf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_czFF
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_ev


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
theorem _root_.solution (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv k v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv k ((0 : Fin 1), c) h) * pderiv k v (G.F c) := by
  rw [pderiv_ev (czFF G), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl
end GlobalTheory.FormalLog
