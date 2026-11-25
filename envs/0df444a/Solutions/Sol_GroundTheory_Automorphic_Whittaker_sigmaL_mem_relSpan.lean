-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigmaL_mem_relSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:34:06.716334+00:00
-- url     : https://prove2.me/submissions/7cac7688-996f-4d41-8448-8c00e143604d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_chi_swapTheta
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_transl
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan


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
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {U : Set (GL (Fin n) F)} {r : GL (Fin n) F → ℂ}
    (hr : r ∈ relSpan (chi (n := n) ψ₀) U) : sigmaL r ∈ relSpan (chi (n := n) ψ₀) (sigma ⁻¹' U) := by
  have key : relSpan (chi (n := n) ψ₀) U ≤ (relSpan (chi (n := n) ψ₀) (sigma ⁻¹' U)).comap sigmaL := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, sigmaL_transl, ← chi_swapTheta ψ₀ h]
    exact sub_mem_relSpan _ _ (sigmaL_mem_supportedIn hf)
  exact key hr
end GroundTheory.Automorphic.Whittaker
