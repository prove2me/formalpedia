-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_dslopeIter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:41.541133+00:00
-- url     : https://prove2.me/submissions/5791217d-7e99-4549-b4f6-ec2afa5239e9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_dslopeIter_succ__14849de0e418

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {p : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p) (k : ℕ) :
    AnalyticAt ℂ (dslopeIter p k g) p := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [dslopeIter_succ']
    obtain ⟨q, hq⟩ := ih
    exact hq.has_fpower_series_dslope_fslope.analyticAt
end GroundTheory.Global.Elliptic
