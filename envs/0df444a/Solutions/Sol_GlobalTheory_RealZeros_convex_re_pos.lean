-- Prove2me | solution 1 for GlobalTheory.RealZeros.convex_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:38.039965+00:00
-- url     : https://prove2.me/submissions/b6ebb093-8e7a-4f59-8929-b0ce43779901

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution : Convex ℝ {s : ℂ | 0 < s.re} := convex_halfSpace_re_gt 0
end GlobalTheory.RealZeros
