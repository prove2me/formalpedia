-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.rmat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:57.896372+00:00
-- url     : https://prove2.me/submissions/91fbeef5-12df-488b-98cf-c3a887cc195a

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
theorem _root_.solution : Function.Injective (rmat b R) := by
  intro x y h
  have hx := coords_mul b R 1 x
  have hy := coords_mul b R 1 y
  rw [one_mul] at hx hy
  rw [h] at hx
  exact (coords b R).injective (hx.trans hy.symm)
end GroundTheory.Automorphic.Anisotropic
