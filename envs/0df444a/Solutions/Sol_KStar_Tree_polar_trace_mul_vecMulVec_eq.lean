-- Prove2me | solution 1 for KStar.Tree.polar_trace_mul_vecMulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:43.910024+00:00
-- url     : https://prove2.me/submissions/6f5d7a36-1d1a-4aa1-be25-f3033de57b36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TwistTrace
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_PolarTraceMulVecMulVecEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
open Matrix
namespace KStar.Tree
theorem _root_.solution {A : Type} [CommRing A] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (a b : Fin r → A) :
    (M * Matrix.vecMulVec a b).trace = M.mulVec a ⬝ᵥ b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Finset.sum_mul, mul_assoc]
end KStar.Tree
