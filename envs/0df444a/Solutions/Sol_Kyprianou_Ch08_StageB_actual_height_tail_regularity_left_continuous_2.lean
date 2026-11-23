-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.actual_height_tail_regularity_left_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:21:20.304139+00:00
-- url     : https://prove2.me/submissions/b39046fe-10f7-4564-9a62-13e845e4565c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_integral_core_left_continuous
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
    (∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (Set.Iic h₀) h₀) ∧
    Tendsto (fun h => -Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) atTop (nhds 0) ∧
    (∀ y : ℝ, 0 < y → Tendsto (fun s => -(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 s ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) (nhdsWithin y (Set.Iio y)) (nhds (-(-Real.log (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))))) := by
  let I : ℝ → ℝ := fun h => ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P
  have hcore := Kyprianou.Ch08.StageB.actual_height_tail_integral_core_left_continuous P D ψ W hψ hW q hq
  have hpos : ∀ h : ℝ, 0 < h → 0 < I h := by
    intro h hh
    simpa [I] using hcore.1 h hh
  have hne : ∀ h : ℝ, 0 < h → I h ≠ 0 := fun h hh => ne_of_gt (hpos h hh)
  have hmono : MonotoneOn I (Set.Ioi 0) := by
    simpa [I] using hcore.2.1
  have hcont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt I (Set.Iic h₀) h₀ := by
    intro h₀ hh₀
    simpa [I] using hcore.2.2.1 h₀ hh₀
  have htop : Tendsto I atTop (nhds 1) := by
    simpa [I] using hcore.2.2.2.1
  have hleft : ∀ y : ℝ, 0 < y → Tendsto I (nhdsWithin y (Set.Iio y)) (nhds (I y)) := by
    intro y hy
    simpa [I] using hcore.2.2.2.2 y hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxpos : 0 < I x := hpos x (Set.mem_Ioi.mp hx)
    have hypos : 0 < I y := hpos y (Set.mem_Ioi.mp hy)
    have hle : I x ≤ I y := hmono hx hy hxy
    have hlog : Real.log (I x) ≤ Real.log (I y) := Real.log_le_log hxpos hle
    exact neg_le_neg hlog
  · intro h₀ hh₀
    have hpos0 : 0 < I h₀ := hpos h₀ hh₀
    have hcontI : ContinuousWithinAt I (Set.Iic h₀) h₀ := hcont h₀ hh₀
    have hneg : ContinuousAt (fun t : ℝ => -Real.log t) (I h₀) := (Real.continuousAt_log (hne h₀ hh₀)).neg
    exact hneg.comp_continuousWithinAt hcontI
  · have hlogI : Tendsto (fun h => Real.log (I h)) atTop (nhds (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp htop
    have hlogI0 : Tendsto (fun h => Real.log (I h)) atTop (nhds 0) := by
      simpa [Real.log_one] using hlogI
    simpa [I] using hlogI0.neg
  · intro y hy
    have hypos : 0 < I y := hpos y hy
    have hIleft : Tendsto I (nhdsWithin y (Set.Iio y)) (nhds (I y)) := hleft y hy
    have hlogleft : Tendsto (fun s => Real.log (I s)) (nhdsWithin y (Set.Iio y)) (nhds (Real.log (I y))) :=
      (Real.continuousAt_log (hne y hy)).tendsto.comp hIleft
    simpa [I] using hlogleft
