-- Prove2me | solution 1 for HunterPDE.Sobolev.tendsto_weakDeriv_cutoff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:14:55.370313+00:00
-- url     : https://prove2.me/submissions/f964c4a1-a91b-4e7c-a725-75334bfd120f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HunterPDE_Sobolev_eLpNorm_weakDeriv_mul_le_tail
import Theorems.Thm_HunterPDE_Sobolev_uniform_cutoff_jet_bound
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Finiteness

open MeasureTheory Filter HunterPDE.Sobolev
open scoped Topology

theorem solution {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f χ : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (hχ : IsTestFunction Set.univ χ) (hχone : χ =ᶠ[𝓝 0] 1)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    Tendsto (fun j : ℕ => eLpNorm
      (weakDeriv Set.univ α (f - fun x => χ (((j : ℝ) + 1)⁻¹ • x) * f x))
      p volume) atTop (𝓝 0) := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  let d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ := fun β =>
    if hβ : ∑ i, β i ≤ k then (hf.2 β hβ).choose else 0
  have hd (β : Fin n → ℕ) (hβ : ∑ i, β i ≤ k) :
      HasWeakDeriv Set.univ β f (d β) ∧ MemLp (d β) p volume := by
    simpa only [d, dif_pos hβ, Measure.restrict_univ] using (hf.2 β hβ).choose_spec
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hχone
  let R : ℕ → ℝ := fun j => r * ((j : ℝ) + 1)
  have hR : Tendsto R atTop atTop := by
    exact Tendsto.const_mul_atTop hr
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  let η : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j x => 1 - χ (((j : ℝ) + 1)⁻¹ • x)
  obtain ⟨C, hC, hjet⟩ := uniform_cutoff_jet_bound k χ hχ
  have hsmooth (j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (η j) :=
    contDiff_const.sub (hχ.1.comp (contDiff_id.const_smul _))
  have hzero (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < R j) : η j x = 0 := by
    have hj : 0 < (j : ℝ) + 1 := by positivity
    have hnorm : ‖((j : ℝ) + 1)⁻¹ • x‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hj), inv_mul_eq_div]
      exact (div_lt_iff₀ hj).mpr hx
    have heq : χ (((j : ℝ) + 1)⁻¹ • x) = 1 := hball
      (show ((j : ℝ) + 1)⁻¹ • x ∈ Metric.ball 0 r by
      simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    simp [η, heq]
  have tail (β : Fin n → ℕ) (hβ : β ∈ multiIndices n k) :
      Tendsto (fun j => eLpNorm (d β) p (volume.restrict {x | R j ≤ ‖x‖})) atTop (𝓝 0) := by
    have hdp := (hd β (Finset.mem_filter.mp hβ).2).2
    let F : ℕ → EuclideanSpace ℝ (Fin n) → ENNReal := fun j =>
      {x | R j ≤ ‖x‖}.indicator (fun x => ‖d β x‖ₑ ^ p.toReal)
    have hmeas (j : ℕ) : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | R j ≤ ‖x‖} :=
      measurableSet_le measurable_const continuous_norm.measurable
    have hlim (x : EuclideanSpace ℝ (Fin n)) : Tendsto (fun j => F j x) atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hR.eventually (eventually_gt_atTop ‖x‖)] with j hj
      simp [F, not_le.mpr hj]
    have hint := tendsto_lintegral_of_dominated_convergence'
      (fun x => ‖d β x‖ₑ ^ p.toReal)
      (fun j => (hdp.1.enorm.pow_const p.toReal).indicator (hmeas j))
      (fun j => ae_of_all _ (fun x => Set.indicator_le_self' (fun _ _ => bot_le) x))
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hdp.2).ne
      (ae_of_all _ hlim)
    have hint0 : Tendsto (fun j => ∫⁻ x, F j x) atTop (𝓝 0) := by simpa using hint
    have hpow := hint0.ennrpow_const (1 / p.toReal)
    simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
      ← lintegral_indicator (hmeas _), F, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)] using hpow
  have hsum : Tendsto (fun j => ∑ β ∈ multiIndices n k,
      eLpNorm (d β) p (volume.restrict {x | R j ≤ ‖x‖})) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (multiIndices n k) tail
  have hboundlim : Tendsto (fun j => (2 : ENNReal) ^ k * ENNReal.ofReal C *
      ∑ β ∈ multiIndices n k, eLpNorm (d β) p (volume.restrict {x | R j ≤ ‖x‖})) atTop (𝓝 0) := by
    have hfinite : (2 : ENNReal) ^ k * ENNReal.ofReal C ≠ ⊤ := by finiteness
    simpa using ENNReal.Tendsto.const_mul hsum (Or.inr hfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim
  · intro j; exact bot_le
  · intro j
    change eLpNorm (weakDeriv Set.univ α
      (f - fun x => χ (((j : ℝ) + 1)⁻¹ • x) * f x)) p volume ≤ _
    have heq : (f - fun x => χ (((j : ℝ) + 1)⁻¹ • x) * f x) =
        (fun x => η j x * f x) := by ext x; simp [η]; ring
    rw [heq]
    exact eLpNorm_weakDeriv_mul_le_tail hp f (η j) d hd (hsmooth j) (R j) C hC
      (hzero j) (hjet j) α hα
