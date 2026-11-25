-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.countable_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:57.288785+00:00
-- url     : https://prove2.me/submissions/751b00a6-dbca-48de-abfb-e0047c55ca97

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_finite_eigenvalues_norm_ge

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
    {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ}.Countable := by
  have : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ} ⊆ {0} ∪
      ⋃ n : ℕ, {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ 1 / ((n : ℝ) + 1) ≤ ‖μ‖} := by
    intro μ hμ
    by_cases h0 : μ = 0
    · exact Or.inl h0
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 h0)
      exact Or.inr (Set.mem_iUnion.2 ⟨n, hμ, hn.le⟩)
  exact ((Set.countable_singleton 0).union (Set.countable_iUnion fun n =>
    (finite_eigenvalues_norm_ge hT hT' (by positivity)).countable)).mono this
end GroundTheory.Automorphic.CompactSelfAdjoint
