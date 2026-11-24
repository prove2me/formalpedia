-- Prove2me | solution 1 for GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:47.574356+00:00
-- url     : https://prove2.me/submissions/cee009cc-2cdc-443a-8617-e3ccb5be10b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosOfPosMulInnerOnJointEigenvectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module.End
namespace GlobalTheory
theorem _root_.solution {E H I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsSymmetric) (hc : ∀ i j, Commute (T i) (T j))
    (j u : E →ₗ[ℂ] H)
    (hu : ∀ (m : I → ℝ) (y : E), (∀ i, T i y = (m i : ℂ) • y) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, inner ℂ (j x) (u y) = (c : ℂ) * inner ℂ x y)
    (x : E) (hx : x ≠ 0) : (inner ℂ (j x) (u x)).im = 0 ∧ 0 < (inner ℂ (j x) (u x)).re := by
  classical
  have htop : (⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i)) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT (fun a b _ => hc a b)
  have hO := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  have key : ∀ (χ : I → ℂ) (y : ↥(⨅ i, eigenspace (T i) (χ i))), ∃ c : ℝ, 0 < c ∧
      ∀ z, inner ℂ (j z) (u y) = (c : ℂ) * inner ℂ z (y : E) := by
    intro χ y
    apply hu (fun i => (χ i).re) (y : E)
    intro i
    have hmem : (y : E) ∈ eigenspace (T i) (χ i) := (Submodule.mem_iInf _).mp y.2 i
    have hy : T i y = χ i • (y : E) := mem_eigenspace_iff.mp hmem
    by_cases h0 : (y : E) = 0
    · simp [h0]
    · have hr := (hT i).conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hmem, h0⟩)
      have hre : ((χ i).re : ℂ) = χ i := Complex.conj_eq_iff_re.mp hr
      rw [hy, hre]
  have hx' : x ∈ ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hs
  choose c hc0 hcx using key
  have hself : ∀ χ ∈ s, inner ℂ x (μ χ : E) = ((‖(μ χ : E)‖ ^ 2 : ℝ) : ℂ) := by
    intro χ hχ
    rw [← hμ, sum_inner, Finset.sum_eq_single χ]
    · rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · intro ψ _ hψ
      simpa using hO hψ (μ ψ) (μ χ)
    · intro h; exact absurd hχ h
  have hux : u x = ∑ χ ∈ s, u (μ χ : E) := by rw [← hμ, map_sum]
  have hval : inner ℂ (j x) (u x) = ((∑ χ ∈ s, c χ (μ χ) * ‖(μ χ : E)‖ ^ 2 : ℝ) : ℂ) := by
    rw [hux, inner_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hcx, hself χ hχ, Complex.ofReal_mul]
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  obtain ⟨χ, hχ, hne⟩ : ∃ χ ∈ s, (μ χ : E) ≠ 0 := by
    by_contra hcon
    apply hx
    rw [← hμ]
    exact Finset.sum_eq_zero fun χ hχ => by_contra fun h => hcon ⟨χ, hχ, h⟩
  exact Finset.sum_pos' (fun ψ _ => mul_nonneg (hc0 _ _).le (sq_nonneg _))
    ⟨χ, hχ, mul_pos (hc0 _ _) (pow_pos (norm_pos_iff.mpr hne) 2)⟩
end GlobalTheory
