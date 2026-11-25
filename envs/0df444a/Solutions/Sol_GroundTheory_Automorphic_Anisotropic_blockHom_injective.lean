-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.blockHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:27.503983+00:00
-- url     : https://prove2.me/submissions/53e9c6d4-8858-49eb-9296-dfd4dcf34f4e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmat_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Anisotropic.rmatHom_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution : Function.Injective (blockHom (ι := ι) b R) := by
  intro M M' h
  ext i j : 2
  apply rmat_injective b R
  ext k l
  exact congrFun (congrFun h (i, k)) (j, l)
end GroundTheory.Automorphic.Anisotropic
