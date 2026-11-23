-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_slice_lower_hy4_height_law_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:44:06.292874+00:00
-- url     : https://prove2.me/submissions/93eaf282-660c-4515-9662-4825412569ba

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (n : Measure ℝ) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d l ω}, discountedAt q (tauPlus D.X d ω) ∂P) =
        Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) := by
  intro l d hl hd
  have hLawInst := (hLaw.2 d l hd hl).2
  rw [MeasureTheory.integral_const_mul] at hLawInst
  have hpos : 0 < Real.exp (Phi ψ q * d) := Real.exp_pos _
  have hDiv : (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d l ω}, discountedAt q (tauPlus D.X d ω) ∂P) =
      Real.exp (-d * (n (Set.Ici l)).toReal) / Real.exp (Phi ψ q * d) := by
    rw [eq_div_iff (ne_of_gt hpos), mul_comm]
    exact hLawInst
  rw [hDiv, ← Real.exp_sub]
  congr 1
  ring
