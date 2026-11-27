-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.eventually_notMem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:14.440621+00:00
-- url     : https://prove2.me/submissions/ee8522a8-92b3-4acd-b8de-5d51a6c15b10

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_finite_spectrum_norm_ge

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
theorem _root_.solution (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : μ ≠ 0) : ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum 𝕜 T := by
  have hμ' : 0 < ‖μ‖ / 2 := by have := norm_pos_iff.2 hμ; positivity
  set F := {ν ∈ spectrum 𝕜 T | ‖μ‖ / 2 ≤ ‖ν‖}
  have hF : (F \ {μ}).Finite := (finite_spectrum_norm_ge hT hT' hμ').sdiff
  have hopen : IsOpen ((F \ {μ})ᶜ ∩ Metric.ball μ (‖μ‖ / 2)) :=
    hF.isClosed.isOpen_compl.inter Metric.isOpen_ball
  have hmem : μ ∈ (F \ {μ})ᶜ ∩ Metric.ball μ (‖μ‖ / 2) :=
    ⟨fun h => h.2 rfl, Metric.mem_ball_self hμ'⟩
  filter_upwards [inter_mem_nhdsWithin {μ}ᶜ (hopen.mem_nhds hmem)] with ν hν hνs
  obtain ⟨hne, hF', hball⟩ := hν
  apply hF'
  refine ⟨⟨hνs, ?_⟩, hne⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hball
  have := norm_sub_norm_le μ ν
  linarith
end GroundTheory.Automorphic.CompactSelfAdjoint
