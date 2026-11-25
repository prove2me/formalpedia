-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.isOpen_range_modularJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:56.408702+00:00
-- url     : https://prove2.me/submissions/28f43807-dca4-4559-b5f3-85252efede91

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantSurjective
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticOnNhd_modularJC
import Theorems.Thm_GroundTheory_Global_Elliptic_range_modularJ
import Theorems.Thm_GroundTheory_Global_Elliptic_not_exists_modularJC_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution : IsOpen (range modularJ) := by
  rw [range_modularJ]
  rcases analyticOnNhd_modularJC.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected with h | h
  · exact absurd h not_exists_modularJC_const
  · exact h _ subset_rfl isOpen_upperHalfPlaneSet
end GroundTheory.Global.Elliptic
