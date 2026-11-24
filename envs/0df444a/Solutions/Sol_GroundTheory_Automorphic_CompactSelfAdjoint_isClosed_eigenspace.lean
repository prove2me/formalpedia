-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.isClosed_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:05.153267+00:00
-- url     : https://prove2.me/submissions/8c55993b-00d9-499a-b6d1-64743dd61d11

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.CompactSelfAdjoint
open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
namespace GroundTheory.Automorphic.CompactSelfAdjoint
theorem _root_.solution (T : E →L[𝕜] E) (μ : 𝕜) :
    IsClosed (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) := by
  have : (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) =
      (T - μ • ContinuousLinearMap.id 𝕜 E) ⁻¹' {0} := by
    ext x
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage (map_continuous _)
end GroundTheory.Automorphic.CompactSelfAdjoint
