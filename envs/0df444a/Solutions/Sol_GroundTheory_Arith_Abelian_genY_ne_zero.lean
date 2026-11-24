-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.genY_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:54.334021+00:00
-- url     : https://prove2.me/submissions/ada3a332-88b0-4473-96c3-9b795480a2b5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint

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
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : genY W ≠ 0 := by
  rw [genY, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  have := CoordinateRing.smul_basis_eq_zero (W' := W.toAffine) (p := 0) (q := 1)
    (by rw [zero_smul, zero_add, one_smul]; exact h)
  exact one_ne_zero this.2
end GroundTheory.Arith.Abelian
