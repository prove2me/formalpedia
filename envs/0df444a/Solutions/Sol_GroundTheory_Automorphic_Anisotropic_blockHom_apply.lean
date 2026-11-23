-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.blockHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:21.041127+00:00
-- url     : https://prove2.me/submissions/be4d5e7a-ed49-4bee-8384-0b106d790279

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
variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (M : Matrix ι ι (R ⊗[K] E)) (i j : ι) (k l : κ) :
    blockHom b R M (i, k) (j, l) = rmat b R (M i j) k l := rfl
end GroundTheory.Automorphic.Anisotropic
