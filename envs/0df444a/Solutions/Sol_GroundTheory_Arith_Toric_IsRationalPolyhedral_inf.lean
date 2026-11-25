-- Prove2me | solution 1 for GroundTheory.Arith.Toric.IsRationalPolyhedral.inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:19.787469+00:00
-- url     : https://prove2.me/submissions/6e1574a0-9ca0-4320-826c-47b6708a1b23

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_fg
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_predual
import Theorems.Thm_GroundTheory_Arith_Toric_dual_dual_eq_self
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_sup

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
variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
namespace IsRationalPolyhedral
theorem _root_.solution {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (h : IsRationalPolyhedral (toRealSpan N) σ) (h' : IsRationalPolyhedral (toRealSpan N) σ') :
    IsRationalPolyhedral (toRealSpan N) (σ ⊓ σ') := by
  classical
  have key : σ ⊓ σ' = PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] _)
      ((PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set _) ⊔
        PointedCone.dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ' : Set _) : PointedCone ℝ _) : Set _) := by
    rw [dual_sup, dual_union, dual_dual_eq_self h.fg, dual_dual_eq_self h'.fg]
  rw [key]
  exact (h.dual.sup h'.dual).predual
end IsRationalPolyhedral
end GroundTheory.Arith.Toric
