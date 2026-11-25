-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_somos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:38.660495+00:00
-- url     : https://prove2.me/submissions/e5a797aa-637e-489d-8922-31b797850b4c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_normEDS_somos


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
    psiAt W x y (n + 2) * psiAt W x y (n - 2) =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 * psiAt W x y (n + 1) * psiAt W x y (n - 1) -
        W.Ψ₃.eval x * psiAt W x y n ^ 2 := by
  simp only [psiAt_eq]
  exact normEDS_somos ..
end GroundTheory.Arith.Abelian
