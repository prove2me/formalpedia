-- Prove2me | solution 1 for GlobalTheory.CommTriang.blockOne_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:45.784304+00:00
-- url     : https://prove2.me/submissions/b9390e8a-cfd3-4877-91eb-fb08f7d89588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisFurther
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonEigenvectorCommuting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CommTriang
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CommTriang
theorem _root_.solution (Q : Matrix (Fin n) (Fin n) k) : blockOne Q 0 0 = 1 := rfl
end GlobalTheory.CommTriang
