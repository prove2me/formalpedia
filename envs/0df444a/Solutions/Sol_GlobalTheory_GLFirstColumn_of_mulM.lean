-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.of_mulM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:09.229022+00:00
-- url     : https://prove2.me/submissions/f6a76263-bfca-4ebf-b07c-b8821052d066

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {m : ℕ} (x y : Fin m → Fin m → ℂ) :
    Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := rfl
end GlobalTheory.GLFirstColumn
