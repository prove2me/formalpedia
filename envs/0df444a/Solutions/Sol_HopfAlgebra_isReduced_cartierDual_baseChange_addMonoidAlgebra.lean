-- Prove2me | solution 1 for HopfAlgebra.isReduced_cartierDual_baseChange_addMonoidAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f22e1059-9ab3-5680-b984-b89450866eb0

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra

set_option autoImplicit false

open scoped TensorProduct

open HopfAlgebra in

theorem solution
    (R : Type) [CommRing R] (L : Type) [Field L] [Algebra R L]
    (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ] :
    IsReduced (CartierDual L (L ⊗[R] AddMonoidAlgebra R Γ)) := by
  classical
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro χ hχ

  have key : ∀ γ : Γ, χ ((1 : L) ⊗ₜ[R] AddMonoidAlgebra.single γ (1 : R)) = 0 := by
    intro γ
    have h := congrArg (fun φ : CartierDual L (L ⊗[R] AddMonoidAlgebra R Γ) =>
      φ ((1 : L) ⊗ₜ[R] AddMonoidAlgebra.single γ (1 : R))) hχ
    change (χ ^ 2) ((1 : L) ⊗ₜ[R] AddMonoidAlgebra.single γ (1 : R)) = (0 : Module.Dual L _) _ at h
    rw [LinearMap.zero_apply, pow_two, CartierDual.mul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply,
      AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.dualDistrib_apply,
      CartierDual.toDual_apply] at h
    exact mul_self_eq_zero.1 h
  apply CartierDual.ext
  intro x
  change χ x = (0 : Module.Dual L _) x
  rw [LinearMap.zero_apply]
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero χ
  | tmul l f =>
    induction f using AddMonoidAlgebra.induction_on generalizing l with
    | of g =>
      rw [AddMonoidAlgebra.of_apply, toAdd_ofAdd,
        show l ⊗ₜ[R] (AddMonoidAlgebra.single g (1 : R)) = l • ((1 : L) ⊗ₜ[R] AddMonoidAlgebra.single g (1 : R)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        map_smul, key, smul_zero]
    | add f g hf hg => rw [TensorProduct.tmul_add, map_add, hf, hg, add_zero]
    | smul r f hf => rw [← TensorProduct.smul_tmul]; exact hf (r • l)
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

end S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra
end P2MW
export P2MW.S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra (solution)
