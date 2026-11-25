-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_pow_mul_of_meromorphicShift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:46.484226+00:00
-- url     : https://prove2.me/submissions/cb63e191-b548-48be-9352-fc8c0743d5eb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_meromorphicShift_mul

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
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    {n : ℕ} (hn : meromorphicShift f p ≤ n) : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p := by
  induction n, hn using Nat.le_induction with
  | base => exact analyticAt_pow_meromorphicShift_mul hf
  | succ n _ ih =>
    have e : (fun z ↦ (z - p) ^ (n + 1) * f z) = fun z ↦ (z - p) * ((z - p) ^ n * f z) := by
      funext z; ring
    rw [e]
    exact (analyticAt_id.sub analyticAt_const).mul ih
end GroundTheory.Global.Elliptic
