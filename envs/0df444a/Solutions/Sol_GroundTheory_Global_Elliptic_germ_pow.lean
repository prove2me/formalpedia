-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.germ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:47:26.518507+00:00
-- url     : https://prove2.me/submissions/aef379cd-f8fa-4bc8-ae25-54e529118bb1

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
theorem _root_.solution {f : ℂ → ℂ} (hf : Meromorphic f) (n : ℕ) : germ (f ^ n) = germ f ^ n := by
  rw [germ_of hf, germ_of (hf.pow (n := n)), ← map_pow]
  rfl
end GroundTheory.Global.Elliptic
