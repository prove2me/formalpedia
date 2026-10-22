-- Prove2me | solution 1 for JHolomorphic.exists_norm_le_of_eLpNorm_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T23:03:43.530688+00:00
-- url     : https://prove2.me/submissions/49d074f2-6618-4246-803c-5d8d23308cff

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_enorm_le_of_contDiff_tsupport_ball
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem exists_norm_le_of_eLpNorm_fderiv_le_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : ℝ) (hp : 2 < p) (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → F)
    (hf : ∀ ν, ContDiffOn ℝ 1 (f ν) U)
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (f ν) (ENNReal.ofReal p) (volume.restrict K) ≤ C ∧
        eLpNorm (fderiv ℝ (f ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C) :
    ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖f ν z‖ ≤ M := by
  intro K hKU hK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  set L := cthickening δ K with hLdef
  have hLc : IsCompact L := hK.cthickening
  have hLm : MeasurableSet L := isClosed_cthickening.measurableSet
  obtain ⟨C, hC⟩ := hbd L hδU hLc
  obtain ⟨C0, hC0⟩ := enorm_le_of_contDiff_tsupport_ball (E := F) p hp
  let χ : ContDiffBump (0 : ℂ) := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hχ : ContDiff ℝ 1 (⇑χ) := χ.contDiff
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖fderiv ℝ χ x‖ ≤ B :=
    (hχ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      (χ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the bound
  set A : ℝ≥0∞ := ENNReal.ofReal (C0 * δ ^ (1 - 2 / p)) *
    (2 * ((C : ℝ≥0∞) + ‖B‖ₑ * C)) with hAdef
  have hAtop : A ≠ ⊤ := by
    rw [hAdef]
    finiteness
  refine ⟨A.toReal, fun ν z₀ hz₀ => ?_⟩
  set φ : ℂ → ℝ := fun y => χ (y - z₀) with hφdef
  set g : ℂ → F := fun y => φ y • f ν y with hgdef
  have hφc : ContDiff ℝ 1 φ := hχ.comp (contDiff_id.sub contDiff_const)
  have hφt : tsupport φ ⊆ closedBall z₀ (δ / 2) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    have : y - z₀ ∈ tsupport χ := subset_tsupport _ hy
    rw [χ.tsupport_eq] at this
    simpa [mem_closedBall, dist_eq_norm] using this
  have hgt : tsupport g ⊆ closedBall z₀ (δ / 2) :=
    (tsupport_smul_subset_left _ _).trans hφt
  have hball_L : closedBall z₀ (δ / 2) ⊆ L := by
    intro y hy
    refine mem_cthickening_of_dist_le y z₀ δ K hz₀ ?_
    have := mem_closedBall.1 hy; linarith
  have hgL : tsupport g ⊆ L := hgt.trans hball_L
  have hfat : ∀ y ∈ U, ContDiffAt ℝ 1 (f ν) y := fun y hy =>
    (hf ν).contDiffAt (hU.mem_nhds hy)
  have hgc : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact hφc.contDiffAt.smul (hfat y hy)
    · have hyg : y ∉ tsupport g := fun h => hy (hδU (hgL h))
      rw [notMem_tsupport_iff_eventuallyEq] at hyg
      exact contDiffAt_const.congr_of_eventuallyEq hyg
  -- value at the centre
  have hgz : g z₀ = f ν z₀ := by
    simp only [hgdef, hφdef, sub_self]
    rw [χ.one_of_mem_closedBall (by simp; positivity), one_smul]
  -- pointwise derivative bound
  set h : ℂ → ℝ := fun y => ‖fderiv ℝ (f ν) y‖ + B * ‖f ν y‖ with hhdef
  have hpt : ∀ y, ‖fderiv ℝ g y‖ ≤ L.indicator h y := by
    intro y
    by_cases hyL : y ∈ L
    · rw [indicator_of_mem hyL]
      have hyU : y ∈ U := hδU hyL
      have hfd : DifferentiableAt ℝ (f ν) y := (hfat y hyU).differentiableAt (by simp)
      have hφd : DifferentiableAt ℝ φ y := hφc.differentiable (by simp) y
      rw [show fderiv ℝ g y = φ y • fderiv ℝ (f ν) y + (fderiv ℝ φ y).smulRight (f ν y) from
        (hφd.hasFDerivAt.smul hfd.hasFDerivAt).fderiv]
      have hφy : |φ y| ≤ 1 := by
        rw [abs_of_nonneg (χ.nonneg)]; exact χ.le_one
      have hDφ : ‖fderiv ℝ φ y‖ ≤ B := by
        rw [hφdef, fderiv_comp_sub (f := fun x => χ x)]; exact hB _
      calc ‖φ y • fderiv ℝ (f ν) y + (fderiv ℝ φ y).smulRight (f ν y)‖
          ≤ ‖φ y • fderiv ℝ (f ν) y‖ + ‖(fderiv ℝ φ y).smulRight (f ν y)‖ := norm_add_le _ _
        _ ≤ ‖fderiv ℝ (f ν) y‖ + B * ‖f ν y‖ := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_of_le_one_left (norm_nonneg _) hφy
          · rw [ContinuousLinearMap.norm_smulRight_apply]
            exact mul_le_mul_of_nonneg_right hDφ (norm_nonneg _)
    · rw [indicator_of_notMem hyL]
      have : y ∉ tsupport (fderiv ℝ g) := fun hh => hyL (hgL (tsupport_fderiv_subset (𝕜 := ℝ) (f := g) hh))
      rw [image_eq_zero_of_notMem_tsupport this, norm_zero]
  -- L^p bound of h on L
  have hmf : AEStronglyMeasurable (fun y => ‖f ν y‖) (volume.restrict L) :=
    ((hf ν).continuousOn.mono hδU).norm.aestronglyMeasurable hLm
  have hmDf : AEStronglyMeasurable (fun y => ‖fderiv ℝ (f ν) y‖) (volume.restrict L) :=
    (((hf ν).continuousOn_fderiv_of_isOpen hU le_rfl).mono hδU).norm.aestronglyMeasurable hLm
  have hhL : eLpNorm h (ENNReal.ofReal p) (volume.restrict L) ≤ (C : ℝ≥0∞) + ‖B‖ₑ * C := by
    calc eLpNorm h (ENNReal.ofReal p) (volume.restrict L)
        ≤ eLpNorm (fun y => ‖fderiv ℝ (f ν) y‖) (ENNReal.ofReal p) (volume.restrict L) +
          eLpNorm (B • fun y => ‖f ν y‖) (ENNReal.ofReal p) (volume.restrict L) :=
          eLpNorm_add_le hmDf (hmf.const_smul B) hp1
      _ ≤ (C : ℝ≥0∞) + ‖B‖ₑ * C := by
          gcongr
          · rw [eLpNorm_norm (fun y => fderiv ℝ (f ν) y)]; exact (hC ν).2
          · refine (eLpNorm_const_smul_le).trans ?_
            gcongr
            rw [eLpNorm_norm (fun y => f ν y)]; exact (hC ν).1
  have hdir : ∀ e : ℂ, ‖e‖ ≤ 1 →
      eLpNorm (fun y => fderiv ℝ g y e) (ENNReal.ofReal p) volume ≤ (C : ℝ≥0∞) + ‖B‖ₑ * C := by
    intro e he
    calc eLpNorm (fun y => fderiv ℝ g y e) (ENNReal.ofReal p) volume
        ≤ eLpNorm (L.indicator h) (ENNReal.ofReal p) volume := by
          refine eLpNorm_mono fun y => ?_
          refine ((fderiv ℝ g y).le_opNorm e).trans ?_
          refine (mul_le_of_le_one_right (norm_nonneg _) he).trans ?_
          refine (hpt y).trans (le_of_eq ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact indicator_nonneg (fun y _ => by positivity) y
      _ = eLpNorm h (ENNReal.ofReal p) (volume.restrict L) :=
          eLpNorm_indicator_eq_eLpNorm_restrict hLm
      _ ≤ _ := hhL
  have hmain := hC0 z₀ δ hδ g hgc (hgt.trans (closedBall_subset_ball (by linarith))) z₀
  rw [hgz] at hmain
  have hle : ‖f ν z₀‖ₑ ≤ A := by
    refine hmain.trans ?_
    rw [hAdef, two_mul]
    gcongr
    · exact hdir 1 (by simp)
    · exact hdir Complex.I (by simp)
  rw [← ENNReal.ofReal_le_iff_le_toReal hAtop, ofReal_norm_eq_enorm]
  exact hle

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : ℝ) (hp : 2 < p) (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → F)
    (hf : ∀ ν, ContDiffOn ℝ 1 (f ν) U)
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (f ν) (ENNReal.ofReal p) (volume.restrict K) ≤ C ∧
        eLpNorm (fderiv ℝ (f ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C) :
    ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖f ν z‖ ≤ M :=
  exists_norm_le_of_eLpNorm_fderiv_le_aux p hp U hU f hf hbd
