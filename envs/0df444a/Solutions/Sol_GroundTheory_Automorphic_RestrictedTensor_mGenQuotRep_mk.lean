-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mGenQuotRep_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:41.064794+00:00
-- url     : https://prove2.me/submissions/5c7afa85-e754-478c-ba83-52df527e0002

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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (g : M) (u : (mGenSubrep ρ N).toSubmodule) :
    mGenQuotRep ρ e N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((mGenSubrep ρ N).toRepresentation g u) :=
  rfl
end GroundTheory.Automorphic.RestrictedTensor
