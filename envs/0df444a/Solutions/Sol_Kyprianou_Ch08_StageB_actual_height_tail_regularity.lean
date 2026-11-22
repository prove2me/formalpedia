-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_tail_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:26:27.019831+00:00
-- url     : https://prove2.me/submissions/2dd60b6f-b767-4827-9481-9ea35703696a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_integral_core
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    AntitoneOn (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ioi 0) ∧
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Ici h₀) h₀) ∧
    Tendsto (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 0) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun s => -(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 s ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) (nhdsWithin y (Set.Iio y)) (nhds (-(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))))) := by
  have hCore := actual_height_tail_integral_core P D ψ W hψ hW q hq
  rcases hCore with ⟨hPos, hMono, hRight, hLim, hLeft⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hle := hMono hx hy hxy
    have hlog := Real.log_le_log (hPos x hx0) hle
    exact neg_le_neg hlog
  · intro h0 hh0
    have hE := hRight h0 hh0
    have hne : (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h0 ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≠ 0 :=
      ne_of_gt (hPos h0 hh0)
    have hcomp := ContinuousAt.comp_continuousWithinAt
      (f := fun h => ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)
      (s := Set.Ici h0) (x := h0)
      (g := fun x : ℝ => -Real.log x)
      ((Real.continuousAt_log hne).neg) hE
    simpa [Function.comp_def] using hcomp
  · have hcont : ContinuousAt (fun x : ℝ => -Real.log x) 1 :=
      (Real.continuousAt_log one_ne_zero).neg
    have hcomp := hcont.tendsto.comp hLim
    simpa [Function.comp_def] using hcomp
  · intro y hy0
    have hL := hLeft y hy0
    have hne : (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≠ 0 :=
      ne_of_gt (hPos y hy0)
    have hcont : ContinuousAt (fun x : ℝ => -(-Real.log x))
        (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) :=
      (Real.continuousAt_log hne).neg.neg
    have hcomp := hcont.tendsto.comp hL
    simpa [Function.comp_def] using hcomp
