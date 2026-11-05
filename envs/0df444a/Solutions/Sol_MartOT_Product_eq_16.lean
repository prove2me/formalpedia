-- Prove2me | solution 1 for MartOT.Product.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:22:18.677652+00:00
-- url     : https://prove2.me/submissions/6f9bc5ac-446e-40a2-9056-0a74043f44d0

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsPlan μ ν π)
    (ψ ϕ : ℝ → ℝ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ : Measurable ψ) (hϕ0 : ∀ x, 0 ≤ ϕ x)
    (hϕ : Antitone ϕ) :
    ∫⁻ p, ENNReal.ofReal (ϕ p.1 * ψ p.2) ∂π =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ∫⁻ y, ENNReal.ofReal (ψ y) ∂((π.restrict ({x | t ≤ ϕ x} ×ˢ Set.univ)).map Prod.snd) := by
  have hπf : IsFiniteMeasure π := by
    refine ⟨?_⟩
    have : π Set.univ = μ Set.univ := by
      rw [← hπ.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [this]; exact measure_lt_top μ _
  have hϕm : Measurable ϕ := hϕ.measurable
  have hA : ∀ t, MeasurableSet {x | t ≤ ϕ x} := fun t => measurableSet_le measurable_const hϕm
  have inner : ∀ t, ∫⁻ y, ENNReal.ofReal (ψ y) ∂((π.restrict ({x | t ≤ ϕ x} ×ˢ Set.univ)).map Prod.snd)
      = ∫⁻ p, ({x | t ≤ ϕ x} ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => ENNReal.ofReal (ψ p.2)) p ∂π := by
    intro t
    rw [lintegral_map (f := fun y => ENNReal.ofReal (ψ y)) hψ.ennreal_ofReal measurable_snd,
      lintegral_indicator ((hA t).prod MeasurableSet.univ)]
  simp_rw [inner]
  rw [lintegral_lintegral_swap ?_]
  · apply lintegral_congr; intro p
    have h1 : ∀ t, ({x | t ≤ ϕ x} ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => ENNReal.ofReal (ψ p.2)) p
        = (Set.Iic (ϕ p.1)).indicator (fun _ => ENNReal.ofReal (ψ p.2)) t := by
      intro t; by_cases h : t ≤ ϕ p.1 <;> simp [Set.indicator, h]
    simp_rw [h1]
    rw [lintegral_indicator measurableSet_Iic, setLIntegral_const,
      Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi, Real.volume_Ioc, sub_zero,
      ENNReal.ofReal_mul (hϕ0 _), mul_comm]
  · have : (Function.uncurry fun t (p : ℝ × ℝ) =>
        ({x | t ≤ ϕ x} ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => ENNReal.ofReal (ψ p.2)) p) =
        {q : ℝ × (ℝ × ℝ) | q.1 ≤ ϕ q.2.1}.indicator (fun q => ENNReal.ofReal (ψ q.2.2)) := by
      funext q; by_cases h : q.1 ≤ ϕ q.2.1 <;> simp [Set.indicator, h, Function.uncurry]
    rw [this]
    exact ((ENNReal.measurable_ofReal.comp (hψ.comp (measurable_snd.comp measurable_snd))).indicator
      (measurableSet_le measurable_fst (hϕm.comp (measurable_fst.comp measurable_snd)))).aemeasurable
