-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.wt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:44.281822+00:00
-- url     : https://prove2.me/submissions/f88fb5a3-6153-4ada-8d04-c45551c6af6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_of_mulM

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
theorem _root_.solution {m : ℕ} (a y : Fin m → Fin m → ℂ) : wt (mulM a y) = wt a * wt y := by
  unfold wt
  rw [of_mulM, det_mul, norm_mul, mul_pow, mul_inv, mul_pow, ENNReal.ofReal_mul (by positivity)]
end GlobalTheory.GLFirstColumn
