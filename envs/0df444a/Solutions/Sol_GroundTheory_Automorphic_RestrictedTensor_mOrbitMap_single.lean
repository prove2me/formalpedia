-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mOrbitMap_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:54.97011+00:00
-- url     : https://prove2.me/submissions/c22342fa-f1d9-4eaf-b0d6-246c21354bae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ : Representation ℂ M V) (v : V) (m : M) (a : ℂ) :
    mOrbitMap ρ v (Finsupp.single m a) = a • ρ m v := by
  rw [mOrbitMap, Finsupp.linearCombination_single]
end GroundTheory.Automorphic.RestrictedTensor
