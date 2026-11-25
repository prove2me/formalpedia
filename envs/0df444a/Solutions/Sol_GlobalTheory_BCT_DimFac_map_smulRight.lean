-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.map_smulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:41:44.710407+00:00
-- url     : https://prove2.me/submissions/c4c2c7cd-4859-4673-988c-2d64f4f4ee1e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_contractLeft_tmul
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
theorem _root_.solution (l : Dual ℂ W) (y : W) (t : W ⊗[ℂ] M) :
    TensorProduct.map (l.smulRight y) LinearMap.id t = y ⊗ₜ contractLeft l t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => simp [contractLeft_tmul, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]
end GlobalTheory.BCT.DimFac
