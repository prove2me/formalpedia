-- Prove2me | solution 1 for IsLocalRing.isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f594b52f-bd48-5c64-9d88-87a31edea0cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A) (ha : maximalIdeal A = Ideal.span {a})
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ Ideal.span {algebraMap A R a}) := by
  have hI : (maximalIdeal A).map (algebraMap A R) = Ideal.span {algebraMap A R a} := by
    rw [ha, Ideal.map_span, Set.image_singleton]
  let e : ResidueField A ⊗[A] R ≃+* R ⧸ Ideal.span {algebraMap A R a} :=
    ((Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)).toRingEquiv.trans (Ideal.quotEquivOfEq hI)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩

end S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span
end P2MW
export P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span (solution)
