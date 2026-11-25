-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mem_mOrbitSpan_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:27.51706+00:00
-- url     : https://prove2.me/submissions/40e2eea2-6d80-4b6f-a0e6-cf5ad7d4bae1

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
theorem _root_.solution (ρ : Representation ℂ M V) (v : V) :
    v ∈ (mOrbitSpan ρ v).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩
end GroundTheory.Automorphic.RestrictedTensor
