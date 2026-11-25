-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.lmat_eq_rmat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:56.611987+00:00
-- url     : https://prove2.me/submissions/b6a8ea51-6ff2-4d11-abe5-a73c9b3fa9e6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
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
theorem _root_.solution (a : R ⊗[K] E) : lmat b R a = rmat b R a := by
  ext k l
  simp only [lmat, rmat, mul_comm]
end GroundTheory.Automorphic.Anisotropic
