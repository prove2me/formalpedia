-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.orbitMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:29.087699+00:00
-- url     : https://prove2.me/submissions/f07a0083-a7e5-45a5-a6a8-2fb73b12ba0d

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
theorem _root_.solution (ρ : Representation ℂ G V) (v : V) (c : G →₀ ℂ) :
    orbitMap ρ v c = c.sum fun g a => a • ρ g v := by
  rw [orbitMap, Finsupp.linearCombination_apply]
end GroundTheory.Automorphic.RestrictedTensor
