-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.finite_spectrum_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:59.850329+00:00
-- url     : https://prove2.me/submissions/b218a57c-cbda-4838-9220-6e6dfbb0d9e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_finite_eigenvalues_norm_ge
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_hasEigenvalue_of_mem_spectrum

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
theorem _root_.solution (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ ∈ spectrum 𝕜 T | ε ≤ ‖μ‖}.Finite :=
  (finite_eigenvalues_norm_ge hT hT' hε).subset fun _ hμ =>
    ⟨hasEigenvalue_of_mem_spectrum hT hμ.1 (norm_pos_iff.1 (hε.trans_le hμ.2)), hμ.2⟩
end GroundTheory.Automorphic.CompactSelfAdjoint
