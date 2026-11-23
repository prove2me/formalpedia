-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:21.51586+00:00
-- url     : https://prove2.me/submissions/3b94ee7e-e993-48b3-a3b5-a8cee8f94935

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (x y : R) (n : ℤ) :
    psiAt W x y n =
      normEDS (2 * y + W.a₁ * x + W.a₃) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  rw [psiAt, WeierstrassCurve.ψ, ← coe_evalEvalRingHom, map_normEDS]
  simp only [coe_evalEvalRingHom, ψ₂, evalEval_polynomialY, evalEval_C]
end GroundTheory.Arith.Abelian
