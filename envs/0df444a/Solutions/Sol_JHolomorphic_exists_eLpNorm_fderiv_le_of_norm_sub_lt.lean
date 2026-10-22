-- Prove2me | solution 1 for JHolomorphic.exists_eLpNorm_fderiv_le_of_norm_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:26:15.677982+00:00
-- url     : https://prove2.me/submissions/3debcc55-52cc-4395-b9a5-75188a0267e9

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.Compactness.Compact
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_le_of_contDiff



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem exists_eLpNorm_fderiv_le_of_norm_sub_lt_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (A : E →L[ℝ] E)
    (hA : A.comp A = -ContinuousLinearMap.id ℝ E) :
    ∃ δ > 0, ∃ C : ℝ, ∀ B : E →L[ℝ] E, ‖B - A‖ < δ → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + B (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
  obtain ⟨C0, hC0⟩ := eLpNorm_fderiv_le_of_contDiff p hp A hA
  set C := max C0 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC : 0 < C := by linarith
  refine ⟨1 / (2 * C), by positivity, 2 * C, fun B hB g hg hgc => ?_⟩
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  set q := ENNReal.ofReal p with hqdef
  have hDg : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hs : Continuous fun z => fderiv ℝ g z 1 := hDg.clm_apply continuous_const
  have ht : Continuous fun z => fderiv ℝ g z Complex.I := hDg.clm_apply continuous_const
  set Xs := eLpNorm (fun z => fderiv ℝ g z 1) q volume with hXs
  set Xt := eLpNorm (fun z => fderiv ℝ g z Complex.I) q volume with hXt
  set YB := eLpNorm (fun z => fderiv ℝ g z 1 + B (fderiv ℝ g z Complex.I)) q volume with hYB
  have hXs_top : Xs ≠ ⊤ := (hs.memLp_of_hasCompactSupport
    (hgc.fderiv_apply (𝕜 := ℝ) 1)).eLpNorm_lt_top.ne
  have hXt_top : Xt ≠ ⊤ := (ht.memLp_of_hasCompactSupport
    (hgc.fderiv_apply (𝕜 := ℝ) Complex.I)).eLpNorm_lt_top.ne
  -- the frozen estimate for `A`, rewritten around `B`
  have hYA : eLpNorm (fun z => fderiv ℝ g z 1 + A (fderiv ℝ g z Complex.I)) q volume ≤
      YB + ENNReal.ofReal (1 / (2 * C)) * (Xs + Xt) := by
    have hsplit : (fun z => fderiv ℝ g z 1 + A (fderiv ℝ g z Complex.I)) =
        (fun z => fderiv ℝ g z 1 + B (fderiv ℝ g z Complex.I)) +
          fun z => (A - B) (fderiv ℝ g z Complex.I) := by
      funext z; simp
    rw [hsplit]
    refine (eLpNorm_add_le (hs.add (B.continuous.comp ht)).aestronglyMeasurable
      ((A - B).continuous.comp ht).aestronglyMeasurable hq1).trans ?_
    refine add_le_add le_rfl ?_
    calc eLpNorm (fun z => (A - B) (fderiv ℝ g z Complex.I)) q volume
        ≤ ENNReal.ofReal ‖A - B‖ * Xt :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            (Eventually.of_forall fun z => (A - B).le_opNorm _) q
      _ ≤ ENNReal.ofReal (1 / (2 * C)) * (Xs + Xt) := by
          gcongr
          · rw [← norm_neg, neg_sub]; exact hB.le
          · exact le_add_self
  have hmain : Xs + Xt ≤ ENNReal.ofReal C * (YB + ENNReal.ofReal (1 / (2 * C)) * (Xs + Xt)) :=
    (hC0 g hg hgc).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hYA)
  by_cases hYt : YB = ⊤
  · rw [hYt, ENNReal.mul_top (by simp; linarith)]; exact le_top
  -- pass to real numbers
  set Xr := (Xs + Xt).toReal with hXr
  set Yr := YB.toReal with hYr
  have hX : Xs + Xt = ENNReal.ofReal Xr := (ENNReal.ofReal_toReal (by finiteness)).symm
  have hY : YB = ENNReal.ofReal Yr := (ENNReal.ofReal_toReal hYt).symm
  have hXr0 : 0 ≤ Xr := ENNReal.toReal_nonneg
  have hYr0 : 0 ≤ Yr := ENNReal.toReal_nonneg
  rw [hX, hY, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hYr0 (by positivity),
    ← ENNReal.ofReal_mul hC.le, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  rw [hX, hY, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : C * (Yr + 1 / (2 * C) * Xr) = C * Yr + Xr / 2 := by field_simp
  rw [e] at hmain
  linarith


end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (A : E →L[ℝ] E)
    (hA : A.comp A = -ContinuousLinearMap.id ℝ E) :
    ∃ δ > 0, ∃ C : ℝ, ∀ B : E →L[ℝ] E, ‖B - A‖ < δ → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + B (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume :=
  exists_eLpNorm_fderiv_le_of_norm_sub_lt_aux p hp A hA
