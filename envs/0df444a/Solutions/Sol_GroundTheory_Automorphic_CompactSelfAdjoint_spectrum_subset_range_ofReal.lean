-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.spectrum_subset_range_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:43.024041+00:00
-- url     : https://prove2.me/submissions/6f846a79-8d6d-48f3-a441-4f097c470841

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_real_of_hasEigenvalue
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
    spectrum 𝕜 T ⊆ Set.range ((↑) : ℝ → 𝕜) := by
  intro μ hμ
  by_cases h0 : μ = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue hT' (hasEigenvalue_of_mem_spectrum hT hμ h0)
    exact ⟨r, hr.symm⟩
end GroundTheory.Automorphic.CompactSelfAdjoint
