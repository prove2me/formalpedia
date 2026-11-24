-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_last_exit_restart_ae_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:02:50.003186+00:00
-- url     : https://prove2.me/submissions/5d068eed-02d4-4790-8ecd-bc89a2865273

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ) (q y : ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω)
    (h : (∫ ω, discountedPositiveLastExit X q y ω ∂P) = (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted X (y + X t ω) η) ∂P))
      (tauMinus (shifted X y) 0 ω) ∂P)) :
    (∫ ω, discountedPositiveLastExit Y q y ω ∂P) = (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted Y (y + Y t ω) η) ∂P))
      (tauMinus (shifted Y y) 0 ω) ∂P) := by
  have hl : (∫ ω, discountedPositiveLastExit X q y ω ∂P) = (∫ ω, discountedPositiveLastExit Y q y ω ∂P) := by
    apply integral_congr_ae
    filter_upwards [hEq] with ω hw
    have he : lastExitShifted X y ω = lastExitShifted Y y ω := by
      simp only [lastExitShifted,lastNegativeVisit,shifted,hw]
    unfold discountedPositiveLastExit
    rw [he]
  have hr : (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted X (y + X t ω) η) ∂P))
      (tauMinus (shifted X y) 0 ω) ∂P) = (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted Y (y + Y t ω) η) ∂P))
      (tauMinus (shifted Y y) 0 ω) ∂P) := by
    apply integral_congr_ae
    filter_upwards [hEq] with ω hw
    have ht : tauMinus (shifted X y) 0 ω = tauMinus (shifted Y y) 0 ω := by
      simp only [tauMinus,shifted,hw]
    rw [ht]
    apply congrArg (fun k : ℝ≥0 → ℝ => WithTop.recTopCoe (C := fun _ => ℝ) 0 k
      (tauMinus (shifted Y y) 0 ω))
    funext t
    rw [hw t]
    congr 1
    apply integral_congr_ae
    filter_upwards [hEq] with η he
    simp only [lastExitShifted,lastNegativeVisit,shifted,he]
  rwa [hl,hr] at h
