-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_mem_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:32.817512+00:00
-- url     : https://prove2.me/submissions/3799a3d3-d43d-4fa1-94e1-8fc764e1543d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] {H : Type*} [Group H] [TopologicalSpace H]
  [MulAction H X] [ContinuousSMul H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U : Set X} (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) (h : H)
    {f : X → ℂ} (hf : f ∈ supportedIn U) : transl h f ∈ supportedIn U := by
  refine ⟨⟨hf.1.1.comp_continuous (continuous_const_smul h⁻¹), ?_⟩, ?_⟩
  · exact hf.1.2.comp_homeomorph (Homeomorph.smul h⁻¹)
  · intro x hx
    have := hUinv h _ (hf.2 hx)
    simpa using this
end GroundTheory.Automorphic.Whittaker
