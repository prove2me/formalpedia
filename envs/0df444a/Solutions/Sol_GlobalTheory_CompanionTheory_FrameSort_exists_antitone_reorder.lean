-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:02.617625+00:00
-- url     : https://prove2.me/submissions/82da0d04-7d82-4693-9f6d-27ab337736b9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneDiagonalConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameSort
namespace GlobalTheory.CompanionTheory.FrameSort
theorem _root_.solution : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  intro n U₀ d hU
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ σ) := by
    refine ⟨Tuple.sort (fun i => - d i), ?_⟩
    intro a b hab
    have := Tuple.monotone_sort (fun i => - d i) hab
    simpa using this
  have hH : (U₀.submatrix id σ)ᴴ = U₀ᴴ.submatrix σ id := by
    ext i j; simp
  have hconj : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      (U₀.submatrix id σ)ᴴ * Z * U₀.submatrix id σ = (U₀ᴴ * Z * U₀).submatrix σ σ := by
    intro Z
    rw [hH]
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨U₀.submatrix id σ, ?_, d ∘ σ, hσ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h1 := hconj 1
    rw [Matrix.mul_one] at h1
    rw [h1, Matrix.mul_one]
    have h2 : U₀ᴴ * U₀ = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [h2]
    simp
  · rw [hH]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp σ (fun i => U₀ a i * (d i : ℂ) * U₀ᴴ i b)
  · intro Z hZ
    rw [hconj Z]
    intro i j hij
    simpa using hZ (fun e => hij (σ.injective e))
end GlobalTheory.CompanionTheory.FrameSort
