-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mGenSubrep_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:57.518423+00:00
-- url     : https://prove2.me/submissions/6e599d8c-ab3a-4b33-8381-5c5ac078f4bb

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
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {N : Submodule ℂ V} {X : Subrepresentation ρ} (h : N ≤ X.toSubmodule) :
    (mGenSubrep ρ N).toSubmodule ≤ X.toSubmodule :=
  iSup_le fun g => by
    rintro _ ⟨n, hn, rfl⟩
    exact X.apply_mem_toSubmodule g (h hn)
end GroundTheory.Automorphic.RestrictedTensor
