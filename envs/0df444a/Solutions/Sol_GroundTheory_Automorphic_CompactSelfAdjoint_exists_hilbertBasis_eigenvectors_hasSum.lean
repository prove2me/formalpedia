-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:16.104787+00:00
-- url     : https://prove2.me/submissions/23516608-4656-40b2-aa29-de8441b517ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_finite_setOf_mem_of_orthonormal
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_finite_eigenvalues_norm_ge
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_hilbertBasis_eigenvectors

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
variable [CompleteSpace E]
namespace GroundTheory.Automorphic.CompactSelfAdjoint
theorem _root_.solution {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : IsSelfAdjoint T) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (l : s → ℝ), ⇑b = ((↑) : s → E) ∧
      (∀ i, T (b i) = (l i : 𝕜) • b i) ∧
      (∀ x, HasSum (fun i => ((l i : 𝕜) * ⟪b i, x⟫) • b i) (T x)) ∧
      ∀ ε > 0, {i | ε ≤ |l i|}.Finite := by
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_eigenvectors hT hT'
  choose l hl using fun i : s => hs i i.2
  have hTb : ∀ i, T (b i) = (l i : 𝕜) • b i := fun i => by rw [hb]; exact hl i
  refine ⟨s, b, l, hb, hTb, fun x => ?_, fun ε hε => ?_⟩
  · have h := T.hasSum (b.hasSum_repr x)
    convert h using 1
    funext i
    simp only [map_smul, hTb, smul_smul, b.repr_apply_apply, mul_comm]
  · have hF := finite_eigenvalues_norm_ge hT hT' hε
    have hsub : {i | ε ≤ |l i|} ⊆ ⋃ μ ∈ {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖},
        {i | b i ∈ eigenspace (T : E →ₗ[𝕜] E) μ} := by
      intro i hi
      have hmem : b i ∈ eigenspace (T : E →ₗ[𝕜] E) (l i : 𝕜) := mem_eigenspace_iff.2 (hTb i)
      have hne : b i ≠ 0 := fun h => by simpa [h] using b.orthonormal.1 i
      refine Set.mem_biUnion (x := (l i : 𝕜))
        ⟨hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩, ?_⟩ hmem
      simpa [RCLike.norm_ofReal] using hi
    refine (hF.biUnion fun μ hμ => ?_).subset hsub
    have hμ0 : μ ≠ 0 := norm_pos_iff.1 (hε.trans_le hμ.2)
    have := ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ0
    exact finite_setOf_mem_of_orthonormal b.orthonormal _
end GroundTheory.Automorphic.CompactSelfAdjoint
