-- Prove2me | solution 1 for GlobalTheory.shiftAct_diffElt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:24.03711+00:00
-- url     : https://prove2.me/submissions/609f7f83-0ef7-45a1-a71d-196de862a80f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution (g : G) (φ : G → M) : shiftAct G M (diffElt g) φ = bwdDiff g φ := by
  ext x
  rw [diffElt, map_sub, map_one, LinearMap.sub_apply, Pi.sub_apply, shiftAct_of]; rfl
end GlobalTheory
