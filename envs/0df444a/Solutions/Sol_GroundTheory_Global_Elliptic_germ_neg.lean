-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.germ_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:39.370286+00:00
-- url     : https://prove2.me/submissions/b64fbccc-956b-4f42-8a3f-44b770828ad1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : Meromorphic f) : germ (-f) = -germ f := by
  rw [germ_of hf, germ_of hf.neg, ← map_neg]
  rfl
end GroundTheory.Global.Elliptic
