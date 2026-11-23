-- Prove2me | solution 1 for GlobalTheory.CommTriang.blockOne_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:44.884933+00:00
-- url     : https://prove2.me/submissions/e51ba4e4-f45a-4bee-8128-911ce9659c39

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
theorem _root_.solution (Q : Matrix (Fin n) (Fin n) k) (b : Fin n) : blockOne Q 0 b.succ = 0 := rfl
end GlobalTheory.CommTriang
