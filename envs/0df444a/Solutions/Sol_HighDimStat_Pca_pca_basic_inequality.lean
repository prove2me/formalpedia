-- Prove2me | solution 1 for HighDimStat.Pca.pca_basic_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:16:58.726896+00:00
-- url     : https://prove2.me/submissions/25764797-0abd-4857-bc94-2838e52fcdb9

import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_PsiPCA

open HighDimStat.Pca

/-- Counterexample: the perturbation `P` is not required to be symmetric. Its antisymmetric part
does not change any Rayleigh quotient, but it does change `Ψ`. Take `d = 2`, `M = diag(1, 0)`,
`θ* = e₁`, `ν = 1` and `P = [[0, 1/2], [-1/2, 1]]`, so that `⟨v, (M + P) v⟩ = ‖v‖²` and every unit
vector, in particular `θ̂ = e₂`, is a maximal unit eigenvector of `M + P`. Then
`ν (1 - ⟨θ̂, θ*⟩²) = 1` while `Ψ(θ̂ - θ*; P) = 1 + 2 · (-1/2) = 0`. -/
theorem solution : ¬ (∀ {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat),
    ν * (1 - (∑ j, θhat j * θstar j) ^ 2) ≤
      |psiPCA P θstar (fun j => θhat j - θstar j)|) := by
  intro H
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0] with hM
  set P : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1/2; -1/2, 1] with hP
  have h1 : IsMaximalUnitEigenvector M ![1, 0] := by
    refine ⟨by simp [Fin.sum_univ_two], fun v hv => ?_⟩
    simp only [Fin.sum_univ_two] at hv
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 1)]
  have h2 : HasEigengap M ![1, 0] 1 := by
    refine ⟨by norm_num, fun v hv hperp => ?_⟩
    simp only [Fin.sum_univ_two] at hv
    simp [Fin.sum_univ_two] at hperp
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hperp]
  have h3 : IsMaximalUnitEigenvector (M + P) ![0, 1] := by
    refine ⟨by simp [Fin.sum_univ_two], fun v hv => ?_⟩
    simp only [Fin.sum_univ_two] at hv
    simp [hM, hP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [hv]
  have h := H M P ![1, 0] ![0, 1] 1 h1 h2 h3
  simp [hP, psiPCA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  norm_num at h
