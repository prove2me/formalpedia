-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_pow_meromorphicShift_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:21.154205+00:00
-- url     : https://prove2.me/submissions/97d88cd0-8470-47af-9efe-3eb4b334332f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue

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
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (fun z ↦ (z - p) ^ meromorphicShift f p * f z) p := by
  classical
  have := Nat.find_spec hf
  simp only [smul_eq_mul] at this
  unfold meromorphicShift
  rw [dif_pos hf]
  convert this
end GroundTheory.Global.Elliptic
