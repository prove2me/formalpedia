-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sub_mem_relSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:27.353353+00:00
-- url     : https://prove2.me/submissions/6fd67d6b-9426-4b4e-9f37-95ed35da06e8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] {H : Type*} [Group H] [TopologicalSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [TopologicalSpace H] [ContinuousSMul H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (χ : H →* ℂ) {U : Set X} (h : H) {f : X → ℂ} (hf : f ∈ supportedIn U) :
    transl h f - χ h • f ∈ relSpan χ U :=
  Submodule.subset_span ⟨h, f, hf, rfl⟩
end GroundTheory.Automorphic.Whittaker
