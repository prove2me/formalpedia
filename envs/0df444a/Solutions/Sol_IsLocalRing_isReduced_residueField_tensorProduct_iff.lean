-- Prove2me | solution 1 for IsLocalRing.isReduced_residueField_tensorProduct_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e1f39973-1e2f-5e2b-bd74-d53bbcc43622

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A]
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
  let e : ResidueField A ⊗[A] R ≃ₐ[A] R ⧸ (maximalIdeal A).map (algebraMap A R) :=
    (Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩

end S_IsLocalRing_isReduced_residueField_tensorProduct_iff
end P2MW
export P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff (solution)
