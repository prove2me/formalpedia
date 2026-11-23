-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.baseMap_baseBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:27.69885+00:00
-- url     : https://prove2.me/submissions/01c6fb16-2a5c-4ce3-94a0-170d2922b649

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_baseBasis_apply

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
variable {R} {R' : Type*} [CommRing R'] [Algebra K R']
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (f : R →ₐ[K] R') (k : κ) :
    baseMap f (baseBasis b R k) = baseBasis b R' k := by
  rw [baseBasis_apply, baseBasis_apply, baseMap, Algebra.TensorProduct.map_tmul, map_one]
  rfl
end GroundTheory.Automorphic.Anisotropic
