-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.germ_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:36.361156+00:00
-- url     : https://prove2.me/submissions/d7324db6-35a9-4433-95d3-0cd9169f72b4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
import Theorems.Thm_GroundTheory_Global_Elliptic_germ_inv

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
theorem _root_.solution {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f / g) = germ f / germ g := by
  rw [div_eq_mul_inv, germ_mul hf hg.inv, germ_inv hg, ← div_eq_mul_inv]
end GroundTheory.Global.Elliptic
