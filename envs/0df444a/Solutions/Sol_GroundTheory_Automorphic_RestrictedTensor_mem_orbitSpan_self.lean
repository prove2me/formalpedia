-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mem_orbitSpan_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:34.965669+00:00
-- url     : https://prove2.me/submissions/e69d8801-a1f8-4285-ab0d-0679595f9e19

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
theorem _root_.solution (ρ : Representation ℂ G V) (v : V) : v ∈ (orbitSpan ρ v).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩
end GroundTheory.Automorphic.RestrictedTensor
