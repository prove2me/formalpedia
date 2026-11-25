-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mGenQuotForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:25.339833+00:00
-- url     : https://prove2.me/submissions/b201f19a-97da-4cfc-9757-1fe1765fc60b

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
variable (e : End ℂ V) (N : Submodule ℂ V)
variable {ρ e N}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (l : Dual ℂ V) (g : M) (n : N) :
    mGenQuotForm ρ e N l (mGenQuotRep ρ e N g (mGenQuotMk ρ e N n)) = l (e (ρ g n)) :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
