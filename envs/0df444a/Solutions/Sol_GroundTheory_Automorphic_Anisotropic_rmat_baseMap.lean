-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.rmat_baseMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:57.267862+00:00
-- url     : https://prove2.me/submissions/4721bd24-03c2-484c-8ebe-eebe771639a9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_baseMap_baseBasis
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_coords_baseMap
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
variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {R} {R' : Type*} [CommRing R'] [Algebra K R']
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (f : R →ₐ[K] R') (x : R ⊗[K] A) :
    rmat b R' (baseMap f x) = (rmat b R x).map f := by
  ext k l
  simp only [rmat, Matrix.map_apply, ← baseMap_baseBasis b f k, ← map_mul, coords_baseMap,
    Function.comp_apply]
end GroundTheory.Automorphic.Anisotropic
