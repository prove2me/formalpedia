-- Prove2me | solution 1 for GroundTheory.Automorphic.sum_coords_smul_stdVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:20.821044+00:00
-- url     : https://prove2.me/submissions/7f039544-4f02-44f9-80ed-a1068eeb2c1a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply


attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable [DecidableEq ι] (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {R}
omit [Algebra.IsQuadraticExtension K E]
namespace GroundTheory.Automorphic
theorem _root_.solution (x : ι → R ⊗[K] E) :
    ∑ a : ι × κ, vecCoords R b x a • stdVec R b a = x := by
  funext i
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [stdVec, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr (x i)]
  simp [vecCoords, Algebra.TensorProduct.basis_apply]
end GroundTheory.Automorphic
