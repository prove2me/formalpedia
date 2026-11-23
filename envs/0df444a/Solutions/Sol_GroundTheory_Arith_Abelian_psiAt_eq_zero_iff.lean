-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.psiAt_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:39.388007+00:00
-- url     : https://prove2.me/submissions/0b72b7d2-1093-41bd-84dc-9eea7f097536

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_sq

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
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
omit [DecidableEq F]
include h₀
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (n : ℤ) : psiAt W x₀ y₀ n = 0 ↔ (W.ΨSq n).eval x₀ = 0 := by
  rw [← psiAt_sq W h₀.1, pow_eq_zero_iff two_ne_zero]
end GroundTheory.Arith.Abelian
