-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.countable_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:12.007454+00:00
-- url     : https://prove2.me/submissions/f8fc6a85-b69d-461f-9e54-33ff990e76ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_countable_eigenvalues
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
theorem _root_.solution (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    (spectrum 𝕜 T).Countable :=
  ((Set.countable_singleton 0).union (countable_eigenvalues hT hT')).mono fun μ hμ => by
    by_cases h0 : μ = 0
    · exact Or.inl h0
    · exact Or.inr (hasEigenvalue_of_mem_spectrum hT hμ h0)
end GroundTheory.Automorphic.CompactSelfAdjoint
