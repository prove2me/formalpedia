-- Prove2me | solution 3 for Kyprianou.Ch08.StageB.actual_height_tail_regularity_left_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:11:10.955972+00:00
-- url     : https://prove2.me/submissions/1fa1fecc-aea8-47ad-b7d3-7ee235bf5ee4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Topology.Order.LeftRight
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_bounds
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralMonotoneAndLimits
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem core_hy4
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    let E := fun h : ℝ => ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P
    (∀ h, 0 < h → 0 < E h) ∧ MonotoneOn E (Ioi 0) ∧
    (∀ h₀, 0 < h₀ → ContinuousWithinAt E (Iic h₀) h₀) ∧
    Tendsto E atTop (𝓝 1) ∧ ∀ y, 0 < y → Tendsto E (𝓝[<] y) (𝓝 (E y)) := by
  dsimp only
  set E := (fun h : ℝ => ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) with hEdef
  obtain ⟨hmono, htop, hleft⟩ := Kyprianou.Ch08.StageB.actualHeightIntegralMonotoneAndLimits P D ψ W hψ hW q hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    simpa [hEdef] using (Kyprianou.Ch08.StageB.actual_height_tail_bounds P D ψ W hψ hW q hq h hh).1
  · simpa [hEdef] using hmono
  · intro h hh
    simpa [hEdef] using (continuousWithinAt_Iio_iff_Iic).mp (hleft h hh)
  · simpa [hEdef] using htop
  · intro y hy
    simpa [hEdef] using hleft y hy

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
  have hcore := core_hy4 P D ψ W hψ hW q hq
  have hpos : ∀ h : ℝ, 0 < h → 0 < I h := by intro h hh; simpa [I] using hcore.1 h hh
  have hne : ∀ h : ℝ, 0 < h → I h ≠ 0 := fun h hh => ne_of_gt (hpos h hh)
  have hmono : MonotoneOn I (Set.Ioi 0) := by simpa [I] using hcore.2.1
  have hcont : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt I (Set.Iic h₀) h₀ := by intro h₀ hh₀; simpa [I] using hcore.2.2.1 h₀ hh₀
  have htop : Tendsto I atTop (nhds 1) := by simpa [I] using hcore.2.2.2.1
  have hleft : ∀ y : ℝ, 0 < y → Tendsto I (nhdsWithin y (Set.Iio y)) (nhds (I y)) := by intro y hy; simpa [I] using hcore.2.2.2.2 y hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hle : I x ≤ I y := hmono hx hy hxy
    exact neg_le_neg (Real.log_le_log (hpos x (Set.mem_Ioi.mp hx)) hle)
  · intro h₀ hh₀
    have hneg : ContinuousAt (fun t : ℝ => -Real.log t) (I h₀) := (Real.continuousAt_log (hne h₀ hh₀)).neg
    exact hneg.comp_continuousWithinAt (hcont h₀ hh₀)
  · have hlogI : Tendsto (fun h => Real.log (I h)) atTop (nhds (Real.log 1)) := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp htop
    have hlogI0 : Tendsto (fun h => Real.log (I h)) atTop (nhds 0) := by simpa [Real.log_one] using hlogI
    simpa [I] using hlogI0.neg
  · intro y hy
    have hlogleft : Tendsto (fun s => Real.log (I s)) (nhdsWithin y (Set.Iio y)) (nhds (Real.log (I y))) := (Real.continuousAt_log (hne y hy)).tendsto.comp (hleft y hy)
    simpa [I] using hlogleft
