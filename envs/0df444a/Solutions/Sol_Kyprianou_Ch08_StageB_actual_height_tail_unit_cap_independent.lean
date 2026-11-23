-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_tail_unit_cap_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:21:19.015458+00:00
-- url     : https://prove2.me/submissions/a898c7ab-5a32-4c9f-ace3-1a77834c8aaf

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_original_unrestricted_upcrossing_discount_bound_zero_included
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
    ∀ h : ℝ, 0 < h →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) ≤ 1 := by
  intro h hh
  obtain ⟨hInt, hBound⟩ :=
    Kyprianou.Ch08.StageB.original_unrestricted_upcrossing_discount_bound_zero_included
      P D ψ W hψ hW q hq
  let c : ℝ := Real.exp (Phi ψ q * 1)
  let f : Ω → ℝ := fun ω => discountedAt q (tauPlus D.X 1 ω)
  have hcpos : 0 ≤ c := (Real.exp_pos _).le
  have hNonneg (ω : Ω) : 0 ≤ f ω := by
    cases ht : tauPlus D.X 1 ω using WithTop.recTopCoe with
    | top => simp [f, discountedAt, ht]
    | coe t => simp [f, discountedAt, ht, Real.exp_nonneg]
  have hCint : Integrable (fun ω => c * f ω) P := hInt.const_mul c
  have hMono :
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, c * f ω ∂P) ≤
        ∫ ω, c * f ω ∂P := by
    apply integral_mono_measure Measure.restrict_le_self ?_ hCint
    exact Eventually.of_forall (fun ω => mul_nonneg hcpos (hNonneg ω))
  change (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, c * f ω ∂P) ≤ 1
  calc
    (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, c * f ω ∂P)
        ≤ ∫ ω, c * f ω ∂P := hMono
    _ = c * ∫ ω, f ω ∂P := integral_const_mul c f
    _ ≤ c * Real.exp (-(Phi ψ q * 1)) :=
      mul_le_mul_of_nonneg_left hBound hcpos
    _ = 1 := by simp [c, ← Real.exp_add]
