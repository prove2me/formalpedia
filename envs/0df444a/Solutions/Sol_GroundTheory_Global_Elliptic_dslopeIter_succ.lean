-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.dslopeIter_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:25.891887+00:00
-- url     : https://prove2.me/submissions/53ec5128-7f00-43c1-b650-6c468f866be8

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
theorem _root_.solution (p : ℂ) (k : ℕ) (g : ℂ → ℂ) :
    dslopeIter p (k + 1) g = dslopeIter p k (Function.swap dslope p g) :=
  Function.iterate_succ_apply _ _ _
end GroundTheory.Global.Elliptic
