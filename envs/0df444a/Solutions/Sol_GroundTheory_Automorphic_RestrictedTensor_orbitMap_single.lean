-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.orbitMap_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:01.58448+00:00
-- url     : https://prove2.me/submissions/8cff9c4f-ee1c-42ae-a0b4-464e2db51518

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ : Representation ℂ G V) (v : V) (g : G) (a : ℂ) :
    orbitMap ρ v (Finsupp.single g a) = a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_single]
end GroundTheory.Automorphic.RestrictedTensor
