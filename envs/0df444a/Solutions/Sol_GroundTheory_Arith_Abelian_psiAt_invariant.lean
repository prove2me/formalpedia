-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:37.129507+00:00
-- url     : https://prove2.me/submissions/ac59bf4f-5258-4e77-96f1-7c69fe2827c9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_normEDS_invariant


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
    W.Ψ₃.eval x * (psiAt W x y (n + 2) * psiAt W x y (n - 1) ^ 2 +
        psiAt W x y (n - 2) * psiAt W x y (n + 1) ^ 2) =
      ((2 * y + W.a₁ * x + W.a₃) ^ 4 + W.preΨ₄.eval x) * psiAt W x y (n - 1) *
          psiAt W x y n * psiAt W x y (n + 1) -
        (2 * y + W.a₁ * x + W.a₃) ^ 2 * W.Ψ₃.eval x * psiAt W x y n ^ 3 := by
  simp only [psiAt_eq]
  exact normEDS_invariant ..
end GroundTheory.Arith.Abelian
