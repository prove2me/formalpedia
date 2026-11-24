-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isSmooth_genSubrep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:08.140833+00:00
-- url     : https://prove2.me/submissions/f559b1d9-7a7d-433d-97fd-ad28663dbdea

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
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
include hσ
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution : IsSmooth (genSubrep σ N).toRepresentation := by
  intro u
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf σ (u : V)) (fun g hg => ?_) (hσ u)
  exact Subtype.ext hg
end GroundTheory.Automorphic.RestrictedTensor
