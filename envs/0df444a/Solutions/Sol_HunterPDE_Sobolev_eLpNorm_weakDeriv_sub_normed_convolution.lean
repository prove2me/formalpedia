-- Prove2me | solution 1 for HunterPDE.Sobolev.eLpNorm_weakDeriv_sub_normed_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T22:59:55.870805+00:00
-- url     : https://prove2.me/submissions/83c598fc-36bb-4a67-bfdd-4e6d9a8ea418

import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_convolution_testFunction
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_ae_eq
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

open MeasureTheory Filter ContinuousLinearMap HunterPDE.Sobolev
open scoped Convolution Topology

theorem solution {n k : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k)
    (d : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : HasWeakDeriv Set.univ α f d) (hdp : MemLp d p volume) :
    eLpNorm (weakDeriv Set.univ α (f - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f))) p volume =
      eLpNorm (d - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] d)) p volume := by
  classical
  have hρ : IsTestFunction Set.univ (φ.normed volume) :=
    ⟨φ.contDiff_normed, φ.hasCompactSupport_normed, Set.subset_univ _⟩
  have hconv := hd.convolution_testFunction (φ.normed volume) hρ
  have herr := hd.sub hconv
  have hchosen : HasWeakDeriv Set.univ α
      (f - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f))
      (weakDeriv Set.univ α (f - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f))) := by
    unfold weakDeriv
    rw [dif_pos (show ∃ g, HasWeakDeriv Set.univ α
      (f - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f)) g from ⟨_, herr⟩)]
    exact Exists.choose_spec _
  have hae := hchosen.ae_eq isOpen_univ herr
  rw [Measure.restrict_univ] at hae
  exact eLpNorm_congr_ae hae
