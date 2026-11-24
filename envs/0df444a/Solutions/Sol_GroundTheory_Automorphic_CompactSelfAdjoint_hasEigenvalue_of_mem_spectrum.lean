-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.hasEigenvalue_of_mem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:54.281805+00:00
-- url     : https://prove2.me/submissions/e31c4e9b-94ff-44e8-8b79-024c5adc0572

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
theorem _root_.solution (hT : IsCompactOperator T) {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 T) (h0 : μ ≠ 0) : HasEigenvalue (T : E →ₗ[𝕜] E) μ :=
  (hT.hasEigenvalue_iff_mem_spectrum h0).2 hμ
end GroundTheory.Automorphic.CompactSelfAdjoint
