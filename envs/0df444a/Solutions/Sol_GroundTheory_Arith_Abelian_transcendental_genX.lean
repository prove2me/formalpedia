-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.transcendental_genX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:01.334045+00:00
-- url     : https://prove2.me/submissions/b88d6e2d-30e8-4d4c-8f1d-a10912f4e664

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_genX_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : Transcendental F (genX W) := by
  rw [transcendental_iff_injective]
  intro p q h
  simp only [genX_eq, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply] at h
  exact (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
    (FaithfulSMul.algebraMap_injective F[X] W.toAffine.CoordinateRing) h
end GroundTheory.Arith.Abelian
