-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.contractRight_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:54.642863+00:00
-- url     : https://prove2.me/submissions/b991011a-948f-4263-9288-4530424756b3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractRight_tmul
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution {W' M' : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup M'] [Module ℂ M']
    (l : Dual ℂ M') (A : W →ₗ[ℂ] W') (B : M →ₗ[ℂ] M') (t : W ⊗[ℂ] M) :
    contractRight l (TensorProduct.map A B t) = A (contractRight (l ∘ₗ B) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [contractRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.BCT.DimFac
