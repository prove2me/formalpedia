-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.genSubrep_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:26.145218+00:00
-- url     : https://prove2.me/submissions/7fa7c490-c12c-4e70-9bda-14bfbc1d09dc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent

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
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {N : Submodule ℂ V} {X : Subrepresentation σ} (h : N ≤ X.toSubmodule) :
    (genSubrep σ N).toSubmodule ≤ X.toSubmodule :=
  iSup_le fun g => by
    rintro _ ⟨n, hn, rfl⟩
    exact X.apply_mem_toSubmodule g (h hn)
end GroundTheory.Automorphic.RestrictedTensor
