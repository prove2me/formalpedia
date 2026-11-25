-- Prove2me | solution 1 for GroundTheory.Arith.Toric.IsRationalPolyhedral.predual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:08.15287+00:00
-- url     : https://prove2.me/submissions/ba7de0e5-c9ec-4476-badb-5fd51fb0f1fb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Theorems.Thm_GroundTheory_Arith_Toric_isRationalPolyhedral_top

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
variable (N : Type*) [AddCommGroup N]
variable {N}
variable [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
namespace IsRationalPolyhedral
theorem _root_.solution {τ : PointedCone ℝ (Dual ℝ (ℝ ⊗[ℤ] N))}
    (hτ : IsRationalPolyhedral (toRealDual N) τ) :
    IsRationalPolyhedral (toRealSpan N)
      (PointedCone.dual (LinearMap.id : Dual ℝ (ℝ ⊗[ℤ] N) →ₗ[ℝ] Dual ℝ (ℝ ⊗[ℤ] N)) (τ : Set _)) := by
  classical
  obtain ⟨T, rfl⟩ := hτ
  rw [dual_hull]
  induction T using Finset.induction_on with
  | empty => simpa using isRationalPolyhedral_top
  | insert m T _ ih =>
    obtain ⟨S, hS⟩ := ih
    rw [Finset.coe_insert, Set.image_insert_eq, dual_insert, dual_singleton, inf_comm, ← hS,
      hull_image_inf_halfspace_int (toRealSpan N) S _ m (fun n => by simp)]
    exact ⟨_, rfl⟩
end IsRationalPolyhedral
end GroundTheory.Arith.Toric
