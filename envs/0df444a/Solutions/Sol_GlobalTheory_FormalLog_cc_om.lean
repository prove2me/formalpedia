-- Prove2me | solution 1 for GlobalTheory.FormalLog.cc_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:05.803882+00:00
-- url     : https://prove2.me/submissions/ea3e6c2e-93aa-45e7-9dd9-9af5a87f70d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Theorems.Thm_GlobalTheory_FormalLog_jm_map_cc
import Theorems.Thm_GlobalTheory_FormalLog_mul_om

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
theorem _root_.solution : (Om G).map constantCoeff = 1 := by
  have h := congrArg (fun M => M.map constantCoeff) (mul_om G)
  simp only [Matrix.map_mul (f := constantCoeff), jm_map_cc, Matrix.one_mul] at h
  rw [h]; refine Matrix.ext fun i j => ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
end GlobalTheory.FormalLog
