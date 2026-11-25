-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.meromorphicShift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:16.7528+00:00
-- url     : https://prove2.me/submissions/f9a82a56-d35a-4d72-b52a-44590afdbb80

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
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} {n : ℕ}
    (h : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p) : meromorphicShift f p ≤ n := by
  classical
  have hf : MeromorphicAt f p := ⟨n, by simpa [smul_eq_mul] using h⟩
  unfold meromorphicShift
  rw [dif_pos hf]
  convert Nat.find_min' hf (by simpa [smul_eq_mul] using h)
end GroundTheory.Global.Elliptic
