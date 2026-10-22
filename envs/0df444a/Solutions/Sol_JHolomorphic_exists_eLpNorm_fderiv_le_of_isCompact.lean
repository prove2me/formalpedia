-- Prove2me | solution 1 for JHolomorphic.exists_eLpNorm_fderiv_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:29:06.403136+00:00
-- url     : https://prove2.me/submissions/7c8dee59-f24e-486d-8a68-f7948897468f

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_le_of_contDiff
import Theorems.Thm_JHolomorphic_exists_eLpNorm_fderiv_le_of_norm_sub_lt



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem exists_eLpNorm_fderiv_le_of_isCompact_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (S : Set (E →L[ℝ] E))
    (hS : IsCompact S) (hSJ : ∀ J₀ ∈ S, J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ J₀ ∈ S, ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
  have hloc : ∀ A ∈ S, ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ B : E →L[ℝ] E, ‖B - A‖ < δ →
      ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + B (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
    intro A hA
    obtain ⟨δ, hδ, C, hC⟩ := exists_eLpNorm_fderiv_le_of_norm_sub_lt p hp A (hSJ A hA)
    exact ⟨δ, hδ, max C 0, le_max_right _ _, fun B hB g hg hgc =>
      (hC B hB g hg hgc).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)⟩
  choose! δ hδ C hC0 hC using hloc
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun A => ball A (δ A))
    (fun A hA => ball_mem_nhds A (hδ A hA))
  refine ⟨∑ A ∈ t, C A, fun J₀ hJ₀ g hg hgc => ?_⟩
  obtain ⟨A, hAt, hJA⟩ : ∃ A ∈ t, J₀ ∈ ball A (δ A) := by simpa using hcov hJ₀
  refine (hC A (htS A hAt) J₀ (by rwa [mem_ball, dist_eq_norm] at hJA) g hg hgc).trans ?_
  gcongr
  exact Finset.single_le_sum (fun B hB => hC0 B (htS B hB)) hAt

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (S : Set (E →L[ℝ] E))
    (hS : IsCompact S) (hSJ : ∀ J₀ ∈ S, J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ J₀ ∈ S, ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume :=
  exists_eLpNorm_fderiv_le_of_isCompact_aux p hp S hS hSJ
