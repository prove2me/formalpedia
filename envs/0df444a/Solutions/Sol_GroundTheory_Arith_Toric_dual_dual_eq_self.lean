-- Prove2me | solution 1 for GroundTheory.Arith.Toric.dual_dual_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:31.322899+00:00
-- url     : https://prove2.me/submissions/48862381-5986-4f78-bff9-4850080d3775

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Theorems.Thm_GroundTheory_Arith_Toric_dual_dual_flip_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ : PointedCone ℝ V} (hσ : σ.FG) :
    dual (LinearMap.id : Dual ℝ V →ₗ[ℝ] Dual ℝ V) (dual (Dual.eval ℝ V) (σ : Set V)) = σ :=
  dual_dual_flip_of_fg _ Function.surjective_id hσ
end GroundTheory.Arith.Toric
