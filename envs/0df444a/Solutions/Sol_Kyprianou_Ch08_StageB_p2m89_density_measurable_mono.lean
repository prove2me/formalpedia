-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_density_measurable_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T09:43:34.100201+00:00
-- url     : https://prove2.me/submissions/1bbbe5ce-6a89-4e7d-90bc-48f9afa0154a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q x : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hW : IsQScale ψ q (W q))
    (hm : Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r))
    (hl : Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q))):
    let f : ℕ → ℝ → ℝ≥0∞ := fun n y => if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0
    (∀ n, Measurable (f n)) ∧ Monotone f := by
  classical
  intro f
  have hc := hW.2.2.2.1
  have hz := hW.2.1
  have hwm : Measurable (W q) := by
    have h : Measurable ((Ici (0 : ℝ)).piecewise (W q) (fun _ => 0)) :=
      hc.measurable_piecewise continuousOn_const measurableSet_Ici
    have he : (Ici (0 : ℝ)).piecewise (W q) (fun _ => 0) = W q := by
      funext z
      by_cases h : 0 ≤ z
      · simp [Set.piecewise, h]
      · simp [Set.piecewise, h, hz z (lt_of_not_ge h)]
    rwa [he] at h
  have hf (n : ℕ) : Measurable (f n) := by
    have hsub := hwm.comp (measurable_const.sub measurable_id : Measurable (fun y : ℝ => x-y))
    have he : Measurable (fun y : ℝ => Real.exp (-(Phi ψ q) * (y-x))) := by fun_prop
    exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
      ((he.mul measurable_const).sub hsub).ennreal_ofReal measurable_const
  have hm' : Monotone f := by
    intro n m hnm y
    have hn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    by_cases h : 0 ≤ y + (n : ℝ) - x
    · have h' : 0 ≤ y + (m : ℝ) - x := by linarith
      simp only [f, if_pos h, if_pos h']
      exact ENNReal.ofReal_le_ofReal (sub_le_sub_right
        (mul_le_mul_of_nonneg_left (hm hn) (Real.exp_nonneg _)) _)
    · simp only [f, if_neg h, zero_le]
  exact ⟨hf, hm'⟩
