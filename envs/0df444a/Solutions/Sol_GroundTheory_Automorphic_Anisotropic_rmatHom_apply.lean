-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.rmatHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:18.235119+00:00
-- url     : https://prove2.me/submissions/77f0a8a3-a734-4cf0-b98f-c96ccad30ac7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (x : R ⊗[K] A) : rmatHom b R x = rmat b R x := rfl
end GroundTheory.Automorphic.Anisotropic
