-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.integral_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:16:28.098934+00:00
-- url     : https://prove2.me/submissions/b5018d10-7409-416c-98f5-4cd5def6f6a1

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_fderiv_normed_convolution_apply
import Theorems.Thm_JHolomorphic_norm_normed_convolution_le
import Theorems.Thm_JHolomorphic_tsupport_normed_convolution_subset
import Theorems.Thm_JHolomorphic_tendsto_integral_smul_of_bounded
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

theorem HasWeakPartialsOn.integral_contDiff_one_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn U u us ut)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, fderiv ℝ φ z 1 • u z = -∫ z, φ z • us z) ∧
      (∫ z, fderiv ℝ φ z Complex.I • u z = -∫ z, φ z • ut z) := by
  -- a sequence of bumps shrinking to `0`
  let ρ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      have : (0 : ℝ) < n + 2 := by positivity
      exact div_lt_div_of_pos_right (by norm_num) this⟩
  have hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := by
    show Tendsto (fun n : ℕ => (2 : ℝ) / (n + 2)) atTop (𝓝 0)
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    simpa using this.const_div_atTop (2 : ℝ)
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open hU hφU
  set K := cthickening δ (tsupport φ)
  have hK : IsCompact K := hφc.isCompact.cthickening
  obtain ⟨hu, hus, hut⟩ := hint K hδU hK
  have hev : ∀ᶠ n in atTop, (ρ n).rOut < δ := hρ (gt_mem_nhds hδ)
  let ψ : ℕ → ℂ → ℝ := fun n => (ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] φ
  have hψs : ∀ n, ContDiff ℝ ∞ (ψ n) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (n := ⊤)
      (ρ n).contDiff_normed hφ.continuous.locallyIntegrable
  have hψK : ∀ᶠ n in atTop, tsupport (ψ n) ⊆ K := hev.mono fun n hn =>
    (tsupport_normed_convolution_subset _ _).trans (cthickening_mono hn.le _)
  have hψc : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (hφc.isCompact.cthickening (r := (ρ n).rOut)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_normed_convolution_subset _ _)
  obtain ⟨M0, hM0⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hR : ∀ w : ℂ → E, IntegrableOn w K →
      Tendsto (fun n => ∫ z, ψ n z • w z) atTop (𝓝 (∫ z, φ z • w z)) := fun w hw =>
    tendsto_integral_smul_of_bounded hK.measurableSet hw ψ φ (fun n => (hψs n).continuous)
      (hψK.mono fun n hn z hz => Function.notMem_support.mp fun h' => hz (hn (subset_tsupport _ h')))
      (fun n z => norm_normed_convolution_le _ hφ.continuous hM0 z)
      (fun z => ContDiffBump.convolution_tendsto_right_of_continuous hρ hφ.continuous z)
  have hLt : ∀ v : ℂ,
      Tendsto (fun n => ∫ z, fderiv ℝ (ψ n) z v • u z) atTop (𝓝 (∫ z, fderiv ℝ φ z v • u z)) := by
    intro v
    have hgc : Continuous fun x => fderiv ℝ φ x v :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support
      ((hφc.fderiv (𝕜 := ℝ)).mono fun x hx h0 => hx (by simp [h0]))
    refine tendsto_integral_smul_of_bounded hK.measurableSet hu (fun n z => fderiv ℝ (ψ n) z v)
      (fun z => fderiv ℝ φ z v)
      (fun n => ((hψs n).continuous_fderiv (by simp)).clm_apply continuous_const)
      (hψK.mono fun n hn z hz => by
        rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h' => hz (hn h'))]; simp)
      (C := 3 * M) (fun n z => ?_) (fun z => ?_)
    · simp only [ψ]
      rw [fderiv_normed_convolution_apply _ φ hφ hφc]
      exact norm_normed_convolution_le _ hgc hM z
    · simp only [ψ]
      simp_rw [fderiv_normed_convolution_apply _ φ hφ hφc]
      exact ContDiffBump.convolution_tendsto_right_of_continuous hρ hgc z
  have hU' : ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U := hψK.mono fun n hn => hn.trans hδU
  refine ⟨tendsto_nhds_unique (hLt 1) ?_, tendsto_nhds_unique (hLt Complex.I) ?_⟩
  · refine ((hR us hus).neg).congr' (hU'.mono fun n hn => ?_)
    exact ((h (ψ n) (hψs n) (hψc n) hn).1).symm
  · refine ((hR ut hut).neg).congr' (hU'.mono fun n hn => ?_)
    exact ((h (ψ n) (hψs n) (hψc n) hn).2).symm

end JHolomorphic

open JHolomorphic

open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn U u us ut)
    (hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ z, fderiv ℝ φ z 1 • u z = -∫ z, φ z • us z) ∧
      (∫ z, fderiv ℝ φ z Complex.I • u z = -∫ z, φ z • ut z) :=
  JHolomorphic.HasWeakPartialsOn.integral_contDiff_one_aux hU h hint φ hφ hφc hφU
