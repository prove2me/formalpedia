-- Prove2me | solution 1 for GlobalTheory.hochschild_homotopy_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:46.634369+00:00
-- url     : https://prove2.me/submissions/a3333925-56ee-421f-b20e-defa798eeb12

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
theorem _root_.solution (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] R[X]) :
    (tensorCoeff R R[X] (0 : X)).lTensor M (hochschildD₁ ρ f) -
      hochschildD₀ ρ (tensorCoeff R M 0 f) = f := by
  classical
  induction f with
  | zero => simp
  | add a b ha hb => simp only [map_add]; rw [add_sub_add_comm, ha, hb]
  | tmul m p =>
    have h : ∀ (t : M ⊗[R] R[X]) (p : R[X]), (tensorCoeff R R[X] (0 : X)).lTensor M
        (TensorProduct.assoc R M R[X] R[X] (t ⊗ₜ p)) = p.coeff 0 • t := by
      intro t p
      induction t with
      | zero => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb, smul_add]
      | tmul m q => simp
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add]; rw [add_sub_add_comm, ha, hb]
    | single y r =>
      simp only [hochschildD₁, hochschildD₀, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul, map_add, map_sub, h]
      by_cases hy : y = 0
      · subst hy; simp [one_def, ← tmul_smul]
      · simp [one_def, hy]
end GlobalTheory
