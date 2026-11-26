-- Prove2me | solution 1 for Kyprianou.Ch04.discountedStateResidualData
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:55:06.532799+00:00
-- url     : https://prove2.me/submissions/59e6e284-1f07-4b1b-89d5-ef05b47d9a48

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_stateExitPreLimitBound
import Theorems.Thm_Kyprianou_Ch04_stateExitExhaustsCompactClock
open MeasureTheory Filter Set Topology ProbabilityTheory Kyprianou.Ch04
open scoped NNReal
set_option autoImplicit false

/-- Discounted continuous spatial residuals have bounded right-continuous stopped densities. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (H : ℝ → ℝ) (hH : Continuous H)
    (l : ℝ) (hl : 0 ≤ l)
    (hX : ∀ᵐ w ∂P, IsCadlag (fun t => X t w))
    (hm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w)) :
    let g := fun (r : ℝ) w => Real.exp (-l*r)*H (X r.toNNReal w)
    let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
      ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ᵐ w ∂P, Measurable (fun r => g r w) ∧
        (∀ s : ℝ, 0 ≤ s → ContinuousWithinAt (fun r => g r w) (Ici s) s) ∧
        (∀ t : NNReal, ∃ n, (t : WithTop NNReal) < tau n w) ∧
        ∀ n : ℕ, ∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)),
          ‖if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0‖ ≤ C n := by
  let g := fun (r : ℝ) w => Real.exp (-l*r)*H (X r.toNNReal w)
  let tau : ℕ → Ω → WithTop NNReal := fun n w => sInf {v : WithTop NNReal |
    ∃ u : NNReal, v = ↑u ∧ (n:ℝ) < |X u w|}
  have hb (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc (-(n:ℝ)) (n:ℝ), ‖H y‖ ≤ B := by
    obtain ⟨B,hB⟩ := (isCompact_Icc (a := -(n:ℝ)) (b := (n:ℝ))).bddAbove_image
      hH.norm.continuousOn
    exact ⟨max B 0,le_max_right _ _,fun y hy => (hB (mem_image_of_mem _ hy)).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨C,hC,?_⟩
  filter_upwards [hX,hm] with w hw hmw
  refine ⟨Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id) |>.mul
    (hH.measurable.comp hmw),?_,?_,?_⟩
  · intro s hs
    have hmap : Tendsto Real.toNNReal (nhdsWithin s (Ici s))
        (nhdsWithin s.toNNReal (Ici s.toNNReal)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact continuous_real_toNNReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin (a := s) (s := Ici s)] with r hr
        exact Real.toNNReal_le_toNNReal hr
    have hpath := (hw s.toNNReal).1.tendsto.comp hmap
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds).mul (hH.continuousAt.tendsto.comp hpath)
  · exact stateExitExhaustsCompactClock (fun t => X t w) hw
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    change ‖if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0‖ ≤ C n
    by_cases hh : (r.toNNReal : WithTop NNReal) < tau n w
    · have hpre : |X r.toNNReal w| ≤ (n:ℝ) := by
        by_contra hn
        exact (not_le_of_gt hh) (sInf_le ⟨r.toNNReal,rfl,lt_of_not_ge hn⟩)
      have hex : Real.exp (-l*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [show 0 ≤ r from hr])
      simp only [if_pos hh,g,norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_of_le_one_left (abs_nonneg _) hex).trans
        (by simpa only [Real.norm_eq_abs] using hbound n _ (abs_le.mp hpre))
    · simp only [if_neg hh,norm_zero]
      exact hC n
