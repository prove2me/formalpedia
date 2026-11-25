-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.blockHom_baseMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:26.660523+00:00
-- url     : https://prove2.me/submissions/35027ef7-1655-44bd-91ba-8701abdd764f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmat_baseMap
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_blockHom_apply
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
variable {R}
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (f : R →ₐ[K] R') (M : Matrix ι ι (R ⊗[K] E)) :
    blockHom b R' (M.map (baseMap f)) = (blockHom b R M).map f := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [blockHom_apply, Matrix.map_apply, rmat_baseMap]
end GroundTheory.Automorphic.Anisotropic
