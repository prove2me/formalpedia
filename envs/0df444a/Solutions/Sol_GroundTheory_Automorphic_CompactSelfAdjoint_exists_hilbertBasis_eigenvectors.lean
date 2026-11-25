-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:58.214957+00:00
-- url     : https://prove2.me/submissions/a837a4a0-b07d-4c42-bd72-06702f2dd3e5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_isClosed_eigenspace
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_hilbertBasis_subset_iUnion
import Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_real_of_hasEigenvalue

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
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E), ⇑b = ((↑) : s → E) ∧
      ∀ v ∈ s, ∃ μ : ℝ, T v = (μ : 𝕜) • v := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  obtain ⟨s, b, hb, hs⟩ := exists_hilbertBasis_subset_iUnion
    (fun μ => eigenspace (T : E →ₗ[𝕜] E) μ) hS.orthogonalFamily_eigenspaces
    (isClosed_eigenspace T) (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hS)
  refine ⟨s, b, hb, fun v hv => ?_⟩
  obtain ⟨μ, hμ⟩ := Set.mem_iUnion.1 (hs hv)
  have hv0 : v ≠ 0 := by
    have h := b.orthonormal.1 ⟨v, hv⟩
    rw [hb] at h
    intro h0
    simp [h0] at h
  have hE : HasEigenvalue (T : E →ₗ[𝕜] E) μ := hasEigenvalue_of_hasEigenvector ⟨hμ, hv0⟩
  obtain ⟨r, hr⟩ := exists_real_of_hasEigenvalue hT' hE
  exact ⟨r, by rw [← hr]; exact mem_eigenspace_iff.1 hμ⟩
end GroundTheory.Automorphic.CompactSelfAdjoint
