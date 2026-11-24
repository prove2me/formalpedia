-- Prove2me | solution 1 for GlobalTheory.hochschild_homotopy_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:57.571849+00:00
-- url     : https://prove2.me/submissions/5f921311-f780-4bf2-b9dd-211d9e77dcfd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply


attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.hochschildD₀_trivialCoaction

set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {X : Type*} [AddMonoid X]
namespace GlobalTheory
theorem _root_.solution (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] (R[X] ⊗[R] R[X])) :
    hochschildD₁ ρ ((tensorCoeff R R[X] (0 : X)).lTensor M f) -
      ((tensorCoeff R R[X] (0 : X)).lTensor R[X]).lTensor M (hochschildD₂ ρ f) = f := by
  classical
  induction f with
  | zero => simp
  | add a b ha hb => simp only [map_add]; rw [add_sub_add_comm, ha, hb]
  | tmul m u =>
    have h : ∀ (t : M ⊗[R] R[X]) (u : R[X] ⊗[R] R[X]),
        ((tensorCoeff R R[X] (0 : X)).lTensor R[X]).lTensor M
        (TensorProduct.assoc R M R[X] (R[X] ⊗[R] R[X]) (t ⊗ₜ u)) =
        TensorProduct.assoc R M R[X] R[X] (t ⊗ₜ tensorCoeff R R[X] (0 : X) u) := by
      intro t u
      induction t with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
      | tmul m q => simp
    induction u with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
    | tmul p q =>
      induction p using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
      | single x c =>
        induction q using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
        | single y r =>
          simp only [hochschildD₁, hochschildD₂, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
            LinearMap.lTensor_tmul, map_add, map_sub, h]
          by_cases hy : y = 0
          · subst hy
            have e : (single x (r * c) : R[X]) ⊗ₜ[R] (single 0 1 : R[X]) =
                single x c ⊗ₜ[R] single 0 r := by
              rw [← smul_eq_mul, ← smul_single, smul_tmul, smul_single, smul_eq_mul, _root_.mul_one]
            simp [one_def, e]
          · simp [one_def, hy]
end GlobalTheory
