-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.continuous_detM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:09.103805+00:00
-- url     : https://prove2.me/submissions/4962e4e9-484d-420d-93c5-60dfd3832435

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
theorem _root_.solution {m : ℕ} : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det :=
  Continuous.matrix_det continuous_id
end GlobalTheory.GLFirstColumn
