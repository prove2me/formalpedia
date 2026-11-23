-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.aeval_genX_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:19.230487+00:00
-- url     : https://prove2.me/submissions/a710715f-8d97-4aee-a52c-3e5a32c58b14

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_transcendental_genX

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
theorem _root_.solution (p : F[X]) : aeval (genX W) p = 0 ↔ p = 0 := by
  have := (transcendental_iff_injective.mp (transcendental_genX W))
  exact ⟨fun h => this (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
end GroundTheory.Arith.Abelian
