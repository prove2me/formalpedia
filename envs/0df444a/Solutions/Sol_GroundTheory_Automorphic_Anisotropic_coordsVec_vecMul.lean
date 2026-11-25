-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.coordsVec_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:55.15037+00:00
-- url     : https://prove2.me/submissions/b80ffde4-3290-4996-a41a-7df3f5527992

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
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
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (x : ι → R ⊗[K] E) (M : Matrix ι ι (R ⊗[K] E)) :
    coordsVec b R (x ᵥ* M) = coordsVec b R x ᵥ* blockHom b R M := by
  funext ⟨j, l⟩
  simp only [coordsVec, vecMul, dotProduct, map_sum, Finset.sum_apply, coords_mul,
    Fintype.sum_prod_type, blockHom_apply]
end GroundTheory.Automorphic.Anisotropic
