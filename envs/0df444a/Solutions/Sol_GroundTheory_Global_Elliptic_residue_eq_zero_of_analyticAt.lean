-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_eq_zero_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:11.374369+00:00
-- url     : https://prove2.me/submissions/ba1ac8d0-9054-4516-ab1a-853ebefd8f7d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_of_eventuallyEq

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
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 :=
  residue_eq_of_eventuallyEq hf (Eventually.of_forall fun z ↦ by simp)
end GroundTheory.Global.Elliptic
