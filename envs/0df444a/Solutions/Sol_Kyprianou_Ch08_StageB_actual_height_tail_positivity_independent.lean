-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actual_height_tail_positivity_independent
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:35:07.911835+00:00
-- url     : https://prove2.me/submissions/f70f5acd-4d2a-45a0-bd8d-cad6e3985713
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_semigroup
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_small_step_positive
import Theorems.Thm_Kyprianou_Ch08_StageB_nonnegative_multiplicative_survival_positive_one_of_small_step
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
      0 < (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) := by
  intro h hh
  let S : ℝ → ℝ := fun a =>
    ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω},
      Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P
  have hsemi : ∀ a b : ℝ, 0 < a → 0 < b → S (a + b) = S a * S b := by
    intro a b ha hb
    simpa only [S] using actual_height_semigroup P D ψ W hψ hW q hq a b h ha hb hh
  have hnon : ∀ a : ℝ, 0 < a → 0 ≤ S a := by
    intro a ha
    change 0 ≤ ∫ ω,
      Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω)
        ∂(P.restrict {ω | NoDrawdownBeforeUpcrossing D.X a h ω})
    apply integral_nonneg
    intro ω
    have hd : 0 ≤ discountedAt q (tauPlus D.X a ω) := by
      cases ht : tauPlus D.X a ω using WithTop.recTopCoe with
      | top => simp [discountedAt, ht]
      | coe t => simp [discountedAt, ht, Real.exp_nonneg]
    exact mul_nonneg (Real.exp_pos _).le hd
  obtain ⟨d, hd, hdh, hSd⟩ :=
    actual_height_small_step_positive P D ψ W hψ hW q hq h hh
  exact nonnegative_multiplicative_survival_positive_one_of_small_step
    S hsemi hnon d hd hSd
