-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_zero_root_inverse_at_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:03:52.076732+00:00
-- url     : https://prove2.me/submissions/b3ca1401-f209-481f-8f4b-cdc62ec41b5d

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_laplace_gap_pos
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (hc : ConvexOn ℝ (Ici 0) ψ) (hz : ψ 0 = 0) (hφ : Phi ψ 0 = 0) (s : ℝ) (hs : 0 < s) :
    Phi ψ (ψ s) = s := by
  have hp : 0 < ψ s :=
    source_scale_laplace_gap_pos ψ W hW 0 s le_rfl hs.le (by rw [hφ]; exact hs)
  have hr := (hW (ψ s) hp.le).1
  have hsle : s ≤ Phi ψ (ψ s) := hr.2.2 _ ⟨hs.le, rfl⟩
  apply le_antisymm _ hsle
  by_contra! hh
  have hv := hc.secant_mono (a := (0 : ℝ)) (x := s) (y := Phi ψ (ψ s))
    (by simp) hs.le hr.2.1.1 hs.ne' (lt_trans hs hh).ne' hh.le
  simp only [hz, sub_zero, hr.2.1.2] at hv
  have h := (div_le_div_iff₀ hs (lt_trans hs hh)).mp hv
  nlinarith [mul_pos hp (sub_pos.mpr hh)]
