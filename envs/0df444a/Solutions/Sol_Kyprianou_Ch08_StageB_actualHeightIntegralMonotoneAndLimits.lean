-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightIntegralMonotoneAndLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:50:28.400072+00:00
-- url     : https://prove2.me/submissions/41928036-9544-44f3-92ce-aeae1f181d48

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralUnitLimit
import Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralStrictLeftLimit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    MonotoneOn
      (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      (Set.Ioi 0) ∧
    Tendsto
      (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      atTop (nhds 1) ∧
    (∀ y : ℝ, 0 < y →
      Tendsto
        (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  have htop :=
    Kyprianou.Ch08.StageB.actualHeightIntegralUnitLimit
      P D ψ W hψ hW q hq
  have hleft :=
    Kyprianou.Ch08.StageB.actualHeightIntegralStrictLeftLimit
      P D ψ W hψ hW q hq
  let c : ℝ := Real.exp (Phi ψ q * 1)
  let f : Ω → ℝ := fun ω => discountedAt q (tauPlus D.X 1 ω)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hf (ω : Ω) : 0 ≤ f ω := by
    cases ht : tauPlus D.X 1 ω using WithTop.recTopCoe with
    | top => simp [f, discountedAt, ht]
    | coe t => simp [f, discountedAt, ht, Real.exp_nonneg]
  have hint : Integrable (fun ω => c * f ω) P := by
    exact (Kyprianou.Ch08.StageB.original_unrestricted_upcrossing_discount_bound_zero_included
      P D ψ W hψ hW q hq).1.const_mul c
  refine ⟨?_, htop, hleft⟩
  intro a ha b hb hab
  have hsubset :
      {ω | NoDrawdownBeforeUpcrossing D.X 1 a ω} ⊆
      {ω | NoDrawdownBeforeUpcrossing D.X 1 b ω} := by
    intro ω hω
    intro t ht
    exact lt_of_lt_of_le (hω t ht) hab
  change (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 a ω}, c * f ω ∂P) ≤
    (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 b ω}, c * f ω ∂P)
  exact integral_mono_measure
    (Measure.restrict_mono hsubset le_rfl)
    (Eventually.of_forall (fun ω => mul_nonneg hc (hf ω)))
    (hint.mono_measure Measure.restrict_le_self)