-- Prove2me | solution 1 for GlobalTheory.multiDiff_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:44.218407+00:00
-- url     : https://prove2.me/submissions/0dbc3dbd-d76b-4111-a8ed-3caef7168ac0

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
theorem _root_.solution {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) (a x : G) :
    multiDiff g (fun y ↦ φ (a + y)) x = multiDiff g φ (a + x) := by
  simp only [multiDiff, add_sub_assoc]
end GlobalTheory
