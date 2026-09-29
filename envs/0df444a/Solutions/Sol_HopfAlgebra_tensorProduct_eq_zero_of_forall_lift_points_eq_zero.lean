-- Prove2me | solution 1 for HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6215a8cb-8d3f-5859-a862-62e58d79bf2b

import Mathlib
import Theorems.Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero

set_option autoImplicit false
open scoped TensorProduct

theorem solution
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (x : A ⊗[↥(IntermediateField.fixedField D)] A)
    (hx : ∀ ν ν' : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift ν ν' (fun _ _ => Commute.all _ _) x = 0) :
    x = 0 :=
  Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero
    (fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
      (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
    hev.1 x (fun p q =>
      hx (WithConv.ofConv p : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)
        (WithConv.ofConv q : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))

end S_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero
end P2MW
export P2MW.S_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero (solution)
