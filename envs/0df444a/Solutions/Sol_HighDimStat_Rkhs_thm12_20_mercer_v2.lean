-- Prove2me | solution 1 for HighDimStat.Rkhs.thm12_20_mercer_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T04:09:39.465007+00:00
-- url     : https://prove2.me/submissions/b884309e-bc5b-4d69-a9c5-085fb7b7ecbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core
import Theorems.Thm_HighDimStat_Rkhs_mercer_spectral_basis_and_continuous_reps

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace
open MeasureTheory

/-- Every positive semidefinite kernel is symmetric: $K(x, z) = K(z, x)$. -/
lemma isPSDKernel_symm {X : Type*} {K : X → X → ℝ} (hK : IsPSDKernel K) (x z : X) :
    K x z = K z x :=
  hK.1 x z

/-- Every positive semidefinite kernel has non-negative diagonal values: $0 \le K(x, x)$. -/
lemma isPSDKernel_diag_nonneg {X : Type*} {K : X → X → ℝ} (hK : IsPSDKernel K) (x : X) :
    0 ≤ K x x := by
  have h := hK.2 1 (fun _ => x) (fun _ => 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul] at h
  exact h

/-- A continuous kernel on a compact space $X$ is bounded on $X \times X$. -/
lemma exists_bound_of_continuous_kernel {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x z : X, |K x z| ≤ M := by
  have hcomp : IsCompact (Set.range (fun p : X × X => |Function.uncurry K p|)) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image (continuous_abs.comp hKcont)
  obtain ⟨M, hM⟩ := hcomp.bddAbove
  refine ⟨max M 0, le_max_right M 0, fun x z => ?_⟩
  exact le_trans (hM ⟨(x, z), rfl⟩) (le_max_left M 0)

/-- Theorem 12.20 (Mercer's theorem, p. 395). -/
theorem thm12_20_mercer_v2 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P) :
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ)
      (ψ : ι → X → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ j, (φ j : X → ℝ) =ᵐ[P] ψ j) ∧
      (∀ j, 0 < μ j → Continuous (ψ j)) ∧
      (∀ x z, HasSum (fun j => μ j * ψ j x * ψ j z) (K x z)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)
        (Function.uncurry K) Filter.atTop) := by
  obtain ⟨ι, hCount, φ, μ, ψ, hμ, hTKφ, hφψ, hcont, hunif, hsum⟩ :=
    mercer_spectral_basis_and_continuous_reps P K hKcont hKpsd hHS TK hTK
  exact ⟨ι, hCount, φ, μ, ψ, hμ, hTKφ, hφψ, hcont, hsum, hunif⟩

abbrev solution := @thm12_20_mercer_v2

end HighDimStat.Rkhs

abbrev solution := @HighDimStat.Rkhs.thm12_20_mercer_v2
