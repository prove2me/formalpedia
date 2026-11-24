-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_killed_density_bounded_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:46:57.496981+00:00
-- url     : https://prove2.me/submissions/643dfcef-d99c-4ef6-8328-96938c8cdfa2

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_killed_density_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_scale_discount_sequence_limit
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_scale_discount_unit_bound
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal
/-- Zero-discount convergence. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ), HasSourceScaleFamily ψ W →
      ∀ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n ≤ 1) → Tendsto r atTop (nhds 0) →
      Tendsto (fun n => Phi ψ (r n)) atTop (nhds (Phi ψ 0)) →
      ∀ x : ℝ, 0 ≤ x → ∀ B : ℝ, 0 ≤ B → ∀ A : Set ℝ, MeasurableSet A →
      A ⊆ Iic B →
      Tendsto (fun n => ((volume.restrict (Ici (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal (killedHalflineDensity ψ (r n) (W (r n)) x y))) A)
        atTop (nhds (((volume.restrict (Ici (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y))) A)) := by
  intro ψ W hW r hr hlim hφ x hx B hB A hA hsub
  let μ := volume.restrict (A ∩ Ici (0 : ℝ))
  let g : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ENNReal.ofReal (killedHalflineDensity ψ (r n) (W (r n)) x y)
  let f : ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (killedHalflineDensity ψ 0 (W 0) x y)
  have hmeas (n : ℕ) : Measurable (g n) :=
    p2m88_source_killed_density_measurable ψ W hW (r n) (hr n).1.le x
  have hfin : μ univ ≠ ∞ := by
    change volume.restrict (A ∩ Ici (0 : ℝ)) univ ≠ ∞
    rw [Measure.restrict_apply_univ]
    have hle : volume (A ∩ Ici (0 : ℝ)) ≤ volume (Icc 0 B) :=
      measure_mono (fun y hy => ⟨hy.2, hsub hy.1⟩)
    rw [Real.volume_Icc] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hWlim := p2m88_scale_discount_sequence_limit ψ W hW r hr hlim
  have ht : Tendsto (fun n => ∫⁻ y, g n y ∂μ) atTop (nhds (∫⁻ y, f y ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (W 1 x)) hmeas
    · intro n
      filter_upwards [ae_restrict_mem (hA.inter measurableSet_Ici)] with y hy
      have hy0 : 0 ≤ y := hy.2
      have hp : 0 ≤ Phi ψ (r n) := ((hW (r n) (hr n).1.le).1.2.1).1
      have hWn := (hW (r n) (hr n).1.le).2.2.1
      have he : Real.exp (-(Phi ψ (r n))*y) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      apply ENNReal.ofReal_le_ofReal
      unfold killedHalflineDensity
      calc
        _ ≤ W (r n) x := by
          linarith [mul_le_mul_of_nonneg_right he (hWn x), hWn (x-y)]
        _ ≤ W 1 x := p2m88_scale_discount_unit_bound ψ W hW x (r n) (hr n).1.le (hr n).2
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    · filter_upwards with y
      have hexp := Real.continuous_exp.continuousAt.tendsto.comp
        (hφ.neg.mul (tendsto_const_nhds (x := y)))
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((hexp.mul (hWlim x)).sub (hWlim (x-y)))
  simpa only [withDensity_apply _ hA, Measure.restrict_restrict hA, g, f, μ] using ht
