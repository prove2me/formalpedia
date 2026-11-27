-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.winOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:22.704437+00:00
-- url     : https://prove2.me/submissions/c2d9eb01-6575-440a-9dbc-4ec53854c0dc

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
variable (ρ : Representation ℂ M V)
variable {ρ} {e : End ℂ V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (m : M) (x : LinearMap.range e) : (winOp ρ e m x : V) = e (ρ m x) :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
