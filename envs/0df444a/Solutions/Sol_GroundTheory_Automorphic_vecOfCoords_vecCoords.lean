-- Prove2me | solution 1 for GroundTheory.Automorphic.vecOfCoords_vecCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:13.669449+00:00
-- url     : https://prove2.me/submissions/ca24b56d-1d82-43ec-907c-94e864d6e6a7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
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
attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (x : ι → R ⊗[K] E) : vecOfCoords b R (vecCoords R b x) = x := by
  funext i
  simp only [vecCoords, vecOfCoords]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (x i)]
  rfl
end GroundTheory.Automorphic
