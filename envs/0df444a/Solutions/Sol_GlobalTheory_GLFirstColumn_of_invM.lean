-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.of_invM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:49.39099+00:00
-- url     : https://prove2.me/submissions/cc144820-3a61-453b-8129-8a847b428fd5

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
theorem _root_.solution {m : ℕ} (x : Fin m → Fin m → ℂ) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := rfl
end GlobalTheory.GLFirstColumn
