-- Prove2me | solution 1 for GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:31.957078+00:00
-- url     : https://prove2.me/submissions/bcb8abef-bf89-4e61-9a6f-bf306be33453

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
theorem _root_.solution (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT'
  by_contra hinf
  set S := {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  let f : ℕ ↪ S := Infinite.natEmbedding S
  have hv : ∀ n, ∃ v : E, T v = ((f n : 𝕜)) • v ∧ ‖v‖ = 1 := by
    intro n
    obtain ⟨v, hv1, hv2⟩ := (f n).2.1.exists_hasEigenvector
    refine ⟨((‖v‖⁻¹ : ℝ) : 𝕜) • v, ?_, ?_⟩
    · rw [map_smul, show T v = (f n : 𝕜) • v from mem_eigenspace_iff.1 hv1, smul_comm]
    · rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv2)]
  choose v hvT hvn using hv
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, -, ψ, hψ, hψy⟩ :=
    hK.tendsto_subseq (fun n => hK' ⟨v n, by simp [hvn], rfl⟩)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hψy.cauchySeq ε hε
  have h1 : dist (T (v (ψ (N + 1)))) (T (v (ψ N))) < ε := hN (N + 1) (Nat.le_succ N)
  set a := ψ (N + 1)
  set b := ψ N
  have hne : (f a : 𝕜) ≠ f b := by
    intro h
    have := f.injective (Subtype.ext h)
    exact (hψ (Nat.lt_succ_self N)).ne this.symm
  have horth : ⟪v a, v b⟫ = 0 := by
    have := hS.orthogonalFamily_eigenspaces hne ⟨v a, mem_eigenspace_iff.2 (hvT a)⟩
      ⟨v b, mem_eigenspace_iff.2 (hvT b)⟩
    simpa using this
  have hx : ⟪T (v a), T (v b)⟫ = 0 := by
    rw [hvT, hvT, inner_smul_left, inner_smul_right, horth, mul_zero, mul_zero]
  have hnx : ε ≤ ‖T (v a)‖ := by
    rw [hvT, norm_smul, hvn, mul_one]
    exact (f a).2.2
  have hsq := norm_sub_sq (𝕜 := 𝕜) (T (v a)) (T (v b))
  rw [hx, map_zero, mul_zero, sub_zero] at hsq
  rw [dist_eq_norm] at h1
  have h2 : 0 ≤ ‖T (v a) - T (v b)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖T (v b)‖]
end GroundTheory.Automorphic.CompactSelfAdjoint
