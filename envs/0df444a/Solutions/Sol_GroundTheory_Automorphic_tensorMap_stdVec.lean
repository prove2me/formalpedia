-- Prove2me | solution 1 for GroundTheory.Automorphic.tensorMap_stdVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:23.881077+00:00
-- url     : https://prove2.me/submissions/10a08eef-33a3-4154-b18c-4b7cca721885

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
omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ]
namespace GroundTheory.Automorphic
theorem _root_.solution (a : ι × κ) :
    (fun i => tensorMap E (Algebra.ofId K R) (stdVec K b a i)) = stdVec R b a := by
  funext i
  simp only [stdVec, Pi.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp
end GroundTheory.Automorphic
