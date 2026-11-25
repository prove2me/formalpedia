-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.coords_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:55.877609+00:00
-- url     : https://prove2.me/submissions/3b1f882c-a2f5-4b26-8549-d919003d4026

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
theorem _root_.solution (a z : R ⊗[K] A) : coords b R (a * z) = coords b R z ᵥ* lmat b R a := by
  conv_lhs => rw [eq_sum_coords b R z]
  rw [Finset.mul_sum, map_sum]
  funext l
  simp only [mul_smul_comm, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, lmat]
end GroundTheory.Automorphic.Anisotropic
