-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.baseBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:43.819629+00:00
-- url     : https://prove2.me/submissions/6f916f86-4c86-4bad-b368-1742c9392146

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
theorem _root_.solution (k : κ) : baseBasis b R k = 1 ⊗ₜ b k :=
  Algebra.TensorProduct.basis_apply b k
end GroundTheory.Automorphic.Anisotropic
