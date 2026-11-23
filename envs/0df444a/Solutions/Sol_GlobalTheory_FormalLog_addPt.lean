-- Prove2me | solution 1 for GlobalTheory.FormalLog.addPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:23.932801+00:00
-- url     : https://prove2.me/submissions/cc799577-1ff6-4036-ab25-b3900e423e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_ev_pt


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
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
namespace GlobalTheory.FormalLog
theorem _root_.solution : (![G.add (pt k (n := 2) d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) = ![G.F] := by
  funext j c
  fin_cases j
  show ev (n := 2) ![pt k d 0, pt k d 1] (G.F c) = G.F c
  have e : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k (n := 2) d j := by
    funext j; fin_cases j <;> rfl
  rw [e, ev_pt]
end GlobalTheory.FormalLog
