-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.exists_real_of_hasEigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:31.363557+00:00
-- url     : https://prove2.me/submissions/2b8786bc-1bad-46ff-a3a9-533377afca5a

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
variable {T : E →L[𝕜] E}
variable [CompleteSpace E]
namespace GroundTheory.Automorphic.CompactSelfAdjoint
theorem _root_.solution (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : HasEigenvalue (T : E →ₗ[𝕜] E) μ) : ∃ r : ℝ, μ = r :=
  RCLike.conj_eq_iff_real.1
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT').conj_eigenvalue_eq_self hμ)
end GroundTheory.Automorphic.CompactSelfAdjoint
