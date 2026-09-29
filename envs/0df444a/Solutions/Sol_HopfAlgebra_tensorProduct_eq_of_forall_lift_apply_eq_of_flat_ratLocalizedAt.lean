-- Prove2me | solution 1 for HopfAlgebra.tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ed43cd85-ff3d-5bd3-aac4-d95bd109ba5b

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt

set_option autoImplicit false
open scoped TensorProduct in

theorem solution
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H ⊗[GaloisRep.ratLocalizedAt p] H)
    (hab : ∀ f g : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) a =
        Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) b) :
    a = b := by
  apply HopfAlgebra.eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt p
    (H ⊗[GaloisRep.ratLocalizedAt p] H) a b
  intro F
  have hF : F = Algebra.TensorProduct.lift (F.comp Algebra.TensorProduct.includeLeft)
      ((F.restrictScalars (GaloisRep.ratLocalizedAt p)).comp Algebra.TensorProduct.includeRight)
      (fun _ _ => .all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hF]
  exact hab _ _

end S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
end P2MW
export P2MW.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt (solution)
