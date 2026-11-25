-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_laurentNumerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:20.320804+00:00
-- url     : https://prove2.me/submissions/ba023d7c-0711-4ec9-b253-0350fe009803

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_mul_of_meromorphicShift_le

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
    AnalyticAt ℂ (laurentNumerator f p) p :=
  analyticAt_pow_mul_of_meromorphicShift_le hf (Nat.le_succ _)
end GroundTheory.Global.Elliptic
