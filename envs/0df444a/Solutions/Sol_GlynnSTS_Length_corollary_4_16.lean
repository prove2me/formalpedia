-- Prove2me | solution 1 for GlynnSTS.Length.corollary_4_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:34:14.755101+00:00
-- url     : https://prove2.me/submissions/c2f2379a-5d9e-487b-a81d-6ae83ebc1bb9

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting
import Theorems.Thm_GlynnSTS_Length_display_2_9
import Theorems.Thm_GlynnSTS_Length_proposition_4_3
import Theorems.Thm_GlynnSTS_Length_theorem_4_8
import Theorems.Thm_GlynnSTS_Length_proposition_4_1_a

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The standard normal distribution function is continuous (no atoms). -/
theorem glynnSTS_cor416_continuous_Phi : Continuous (cdf (gaussianReal 0 1)) := by
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [continuous_iff_continuousAt]
  intro a
  have hmono := (cdf (gaussianReal 0 1)).mono
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 : (cdf (gaussianReal 0 1)).measure {a} = 0 := by
    rw [measure_cdf]; exact measure_singleton a
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm (hmono.leftLim_le le_rfl) (by linarith)

/-- Existence of the upper quantile `z` with `H(z) = 1 - δ/2`, via (2.9) and continuity. -/
theorem glynnSTS_cor416_exists_z {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ z, GlynnSTS.Length.H P B g z = 1 - δ / 2 := by
  have h29 := GlynnSTS.Length.display_2_9 P B hB g hg
  set ν := P.map (fun ω => g (B ω)) with hν
  have hmeas : AEMeasurable (fun ω => g (B ω)) P := (hg.1.comp hB.1).aemeasurable
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hmeas
  have hpos : ∀ᵐ y ∂ν, y ∈ Set.Ioi (0 : ℝ) :=
    (ae_map_iff hmeas measurableSet_Ioi).2 hg.2.2.2.1
  have hres : ν.restrict (Set.Ioi 0) = ν := Measure.restrict_eq_self_of_ae_mem hpos
  set Φ := cdf (gaussianReal 0 1)
  have hΦ : Continuous Φ := glynnSTS_cor416_continuous_Phi
  let F : ℝ → ℝ := fun x => ∫ y, Φ (x * y) ∂ν
  have hHF : ∀ x, GlynnSTS.Length.H P B g x = F x := by
    intro x; rw [h29 x, hres]
  have hbound : ∀ x, ∀ᵐ y ∂ν, ‖Φ (x * y)‖ ≤ 1 := by
    intro x; refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [cdf_nonneg (gaussianReal 0 1) (x*y)],
      cdf_le_one _ _⟩
  have hmeasx : ∀ x, AEStronglyMeasurable (fun y => Φ (x * y)) ν := fun x =>
    (hΦ.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hFc : Continuous F := by
    refine continuous_of_dominated (bound := fun _ => (1:ℝ)) hmeasx hbound
      (integrable_const _) ?_
    exact Filter.Eventually.of_forall (fun y => hΦ.comp (continuous_id.mul continuous_const))
  have htop : Tendsto F atTop (𝓝 (∫ _y, (1:ℝ) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := fun _ => (1:ℝ))
      (Filter.Eventually.of_forall hmeasx) (Filter.Eventually.of_forall hbound)
      (integrable_const _) ?_
    filter_upwards [hpos] with y hy
    exact (tendsto_cdf_atTop (μ := gaussianReal 0 1)).comp
      (tendsto_id.atTop_mul_const hy)
  have hbot : Tendsto F atBot (𝓝 (∫ _y, (0:ℝ) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := fun _ => (1:ℝ))
      (Filter.Eventually.of_forall hmeasx) (Filter.Eventually.of_forall hbound)
      (integrable_const _) ?_
    filter_upwards [hpos] with y hy
    exact (tendsto_cdf_atBot (μ := gaussianReal 0 1)).comp
      (tendsto_id.atBot_mul_const hy)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero] at htop hbot
  obtain ⟨b, hb⟩ := (htop.eventually (lt_mem_nhds (show 1 - δ / 2 < (1:ℝ) by linarith))).exists
  obtain ⟨a, ha⟩ := (hbot.eventually (gt_mem_nhds (show (0:ℝ) < 1 - δ / 2 by linarith))).exists
  obtain ⟨z, hz⟩ := intermediate_value_univ a b hFc ⟨ha.le, hb.le⟩
  exact ⟨z, by rw [hHF]; exact hz⟩

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (hg0 : ∀ x, 0 ≤ g x)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (h21 : GlynnSTS.Length.Assumption21 P Y Ybar μ σ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (α β : ℝ) (hαβ : GlynnSTS.Length.H P B g β - GlynnSTS.Length.H P B g α = 1 - δ)
    (p : ℝ) (hp : cdf (gaussianReal 0 1) p = 1 - δ / 2) :
    ENNReal.ofReal (2 * σ * p) ≤
      liminf (fun n : ℕ => ENNReal.ofReal (Real.sqrt n) *
        ∫⁻ ω, ENNReal.ofReal (GlynnSTS.Length.Ln g Ybar α β n ω) ∂P) atTop := by
  have hσ : 0 < σ := h21.sigma_pos
  obtain ⟨z, hz⟩ := glynnSTS_cor416_exists_z P B hB g hg δ hδ0 hδ1
  have h41 := GlynnSTS.Length.proposition_4_1_a P B hB g hg hg0 Y Ybar μ σ h21 δ hδ0 hδ1 α β hαβ
  have h43 := (GlynnSTS.Length.proposition_4_3 P B hB g hg δ hδ0 hδ1 z hz).2 α β hαβ
  have h48 := GlynnSTS.Length.theorem_4_8 P B hB g hg δ hδ0 hδ1 z hz p hp
  refine le_trans ?_ h41
  set E := ∫⁻ ω, ENNReal.ofReal (g (B ω)) ∂P
  calc ENNReal.ofReal (2 * σ * p) = ENNReal.ofReal (2 * σ) * ENNReal.ofReal p :=
        ENNReal.ofReal_mul (by linarith)
    _ ≤ ENNReal.ofReal (2 * σ) * (E * ENNReal.ofReal z) := by gcongr
    _ = ENNReal.ofReal (2 * σ * z) * E := by
        rw [ENNReal.ofReal_mul (p := 2 * σ) (q := z) (by linarith)]; ring
    _ ≤ ENNReal.ofReal (σ * (β - α)) * E := by
        gcongr ?_ * E; exact ENNReal.ofReal_le_ofReal (by nlinarith)
