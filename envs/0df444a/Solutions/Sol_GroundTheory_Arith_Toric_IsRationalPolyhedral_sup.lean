-- Prove2me | solution 1 for GroundTheory.Arith.Toric.IsRationalPolyhedral.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:32.198828+00:00
-- url     : https://prove2.me/submissions/5431ab6e-5a0d-4d5c-9214-413f31ecd8a2

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
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
namespace GroundTheory.Arith.Toric
namespace IsRationalPolyhedral
theorem _root_.solution {L : Type*} [AddCommGroup L] [DecidableEq L] {ι : L →ₗ[ℤ] V}
    {σ σ' : PointedCone ℝ V} (h : IsRationalPolyhedral ι σ) (h' : IsRationalPolyhedral ι σ') :
    IsRationalPolyhedral ι (σ ⊔ σ') := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨S', rfl⟩ := h'
  exact ⟨S ∪ S', by rw [Finset.coe_union, Set.image_union]; exact Submodule.span_union _ _⟩
end IsRationalPolyhedral
end GroundTheory.Arith.Toric
