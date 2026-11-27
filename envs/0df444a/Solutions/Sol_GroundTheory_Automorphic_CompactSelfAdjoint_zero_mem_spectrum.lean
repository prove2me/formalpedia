-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.zero_mem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:46.712382+00:00
-- url     : https://prove2.me/submissions/528db1a4-065e-4892-995d-00f90533264d

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
namespace GroundTheory.Automorphic.CompactSelfAdjoint
theorem _root_.solution (hT : IsCompactOperator T) (hE : ¬ FiniteDimensional 𝕜 E) :
    (0 : 𝕜) ∈ spectrum 𝕜 T := by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  apply hE
  have h : (⇑(↑u⁻¹ : E →L[𝕜] E) ∘ ⇑T) = id := by
    funext x
    have := congrArg (fun g : E →L[𝕜] E => g x) u.inv_mul
    simpa [hu] using this
  have hc := hT.clm_comp (↑u⁻¹ : E →L[𝕜] E)
  rw [h] at hc
  exact isCompactOperator_id_iff_finiteDimensional.1 hc
end GroundTheory.Automorphic.CompactSelfAdjoint
