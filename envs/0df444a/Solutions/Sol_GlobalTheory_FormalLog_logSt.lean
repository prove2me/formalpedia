-- Prove2me | solution 1 for GlobalTheory.FormalLog.logSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:58:55.871798+00:00
-- url     : https://prove2.me/submissions/afa0dbd7-47d2-4548-b51e-8735874a5f7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_logOf
import Theorems.Thm_GlobalTheory_FormalLog_logOf_add
import Theorems.Thm_GlobalTheory_FormalLog_addPt
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_cc_om
import Theorems.Thm_GlobalTheory_FormalLog_constantCoeff_prim


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
theorem _root_.solution : LogSt := by
  intro k _ _ d G
  refine ⟨fun i => logOf G i, fun i => constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (logOf G i) = (1 : Matrix (Fin d) (Fin d) k) i j
    have h := congrArg constantCoeff (pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · funext i
    show ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (logOf G i) =
      ev (n := 2) ![pt k d 0] (logOf G i) + ev (n := 2) ![pt k d 1] (logOf G i)
    rw [addPt]
    exact logOf_add G i
end GlobalTheory.FormalLog
