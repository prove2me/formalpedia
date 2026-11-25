-- Prove2me | solution 1 for GroundTheory.Arith.Toric.isRationalPolyhedral_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:31.874815+00:00
-- url     : https://prove2.me/submissions/56dff848-9546-4065-a3cd-6458f4bb8924

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice

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
theorem _root_.solution :
    IsRationalPolyhedral (toRealSpan N) (⊤ : PointedCone ℝ (ℝ ⊗[ℤ] N)) := by
  classical
  let e := Module.Free.chooseBasis ℤ N
  refine ⟨Finset.univ.image e ∪ Finset.univ.image (fun j => -e j), ?_⟩
  have h1 : (toRealSpan N ∘ e) = e.baseChange ℝ :=
    funext fun j => by simp [Basis.baseChange_apply, toRealSpan_apply]
  have h2 : (toRealSpan N ∘ fun j => -e j) = fun j => -(e.baseChange ℝ) j :=
    funext fun j => by simp [Basis.baseChange_apply, toRealSpan_apply, TensorProduct.tmul_neg]
  rw [← hull_basis_neg_eq_top (e.baseChange ℝ), Finset.coe_union, Finset.coe_image,
    Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.image_univ, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, h1, h2]
end GroundTheory.Arith.Toric
