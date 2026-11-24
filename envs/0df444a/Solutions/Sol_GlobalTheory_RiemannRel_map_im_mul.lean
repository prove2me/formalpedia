-- Prove2me | solution 1 for GlobalTheory.RiemannRel.map_im_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:56:39.795552+00:00
-- url     : https://prove2.me/submissions/de6afb2b-6ee9-46a7-8873-99af171e5dbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelPeriodOfSymplecticBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix
open GlobalTheory GlobalTheory.RiemannRel
namespace GlobalTheory.RiemannRel
theorem _root_.solution {n : Type} [Fintype n] (P Q : Matrix n n ℂ) :
    (P * Q).map Complex.im = P.map Complex.re * Q.map Complex.im + P.map Complex.im * Q.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]
end GlobalTheory.RiemannRel
