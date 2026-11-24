-- Prove2me | solution 1 for GlobalTheory.DetFactor.toGL_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:05.64328+00:00
-- url     : https://prove2.me/submissions/bbb90c00-50fa-4adb-b19f-388db19f0e2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory.DetFactor
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M := rfl
end GlobalTheory.DetFactor
