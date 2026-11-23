-- Prove2me | solution 1 for GlobalTheory.OppRad.un_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:30.757056+00:00
-- url     : https://prove2.me/submissions/078adf65-1424-426c-b542-5e3229e791e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]
namespace GlobalTheory.OppRad
theorem _root_.solution (x : R) (h : x * x = 0) : (un x h).val = 1 + x := rfl
end GlobalTheory.OppRad
