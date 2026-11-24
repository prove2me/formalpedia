-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.relSpan_le_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:50.480663+00:00
-- url     : https://prove2.me/submissions/ca379c24-4d70-43f3-b910-9f65ad305f06

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_supportedIn

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
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (χ : H →* ℂ) {U : Set X}
    (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) : relSpan χ U ≤ supportedIn U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, f, hf, rfl⟩
  exact (supportedIn U).sub_mem (transl_mem_supportedIn hUinv h hf)
    ((supportedIn U).smul_mem _ hf)
end GroundTheory.Automorphic.Whittaker
