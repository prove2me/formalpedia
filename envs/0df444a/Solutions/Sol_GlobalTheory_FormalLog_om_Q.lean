-- Prove2me | solution 1 for GlobalTheory.FormalLog.om_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:27.752857+00:00
-- url     : https://prove2.me/submissions/44ef4933-35d2-4d2e-8f1d-24ba0004b22f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_om_mul
import Theorems.Thm_GlobalTheory_FormalLog_mul_om
import Theorems.Thm_GlobalTheory_FormalLog_map_ev_mul
import Theorems.Thm_GlobalTheory_FormalLog_map_ev_one
import Theorems.Thm_GlobalTheory_FormalLog_CZ_pt
import Theorems.Thm_GlobalTheory_FormalLog_czFF
import Theorems.Thm_GlobalTheory_FormalLog_czY
import Theorems.Thm_GlobalTheory_FormalLog_jac_F


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
theorem _root_.solution (i b : Fin d) : ∑ j, ev (n := 2) ![G.F] (Om G i j) * Ar G j b = ev (n := 2) ![pt k d 1] (Om G i b) := by
  have hJ : (JM G).map (ev (n := 2) ![G.F]) = Matrix.of (Ar G) * (JM G).map (ev (n := 2) ![pt k d 1]) := by
    refine Matrix.ext fun i b => ?_
    simp only [Matrix.map_apply, JM, Matrix.of_apply, Matrix.mul_apply]
    exact jac_F G i b
  have hy : (JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1]) = 1 := by
    rw [← map_ev_mul czY, mul_om, map_ev_one czY]
  have hF : (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) = 1 := by
    rw [← map_ev_mul (czFF G), om_mul, map_ev_one (czFF G)]
  have key : (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) = (Om G).map (ev (n := 2) ![pt k d 1]) := by
    calc _ = (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) *
          ((JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1])) := by rw [hy, Matrix.mul_one]
      _ = (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) *
          (Om G).map (ev (n := 2) ![pt k d 1]) := by rw [hJ, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = _ := by rw [hF, Matrix.one_mul]
  have := congrFun (congrFun key i) b
  simpa [Matrix.mul_apply] using this
end GlobalTheory.FormalLog
