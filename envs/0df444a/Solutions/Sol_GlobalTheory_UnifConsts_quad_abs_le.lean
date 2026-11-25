-- Prove2me | solution 1 for GlobalTheory.UnifConsts.quad_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:37.076309+00:00
-- url     : https://prove2.me/submissions/f0d81f51-83da-4b5f-9afc-9e097b1d0b0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.UnifConsts
namespace GlobalTheory.UnifConsts
theorem _root_.solution {m : Type} [Fintype m] (A : Matrix m m ℝ) (E : ℝ)
    (hE : ∀ j k, |A j k| ≤ E) (x : m → ℝ) :
    |x ⬝ᵥ A *ᵥ x| ≤ E * Fintype.card m * (x ⬝ᵥ x) := by
  have h1 : x ⬝ᵥ A *ᵥ x = ∑ j, ∑ k, x j * A j k * x k := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [h1]
  calc |∑ j, ∑ k, x j * A j k * x k| ≤ ∑ j, ∑ k, |x j * A j k * x k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : m, ∑ k : m, (E / 2 * (x j) ^ 2 + E / 2 * (x k) ^ 2) := by
        gcongr with j _ k _
        rw [abs_mul, abs_mul]
        have h2 := hE j k
        have h3 : |x j| * |x k| ≤ ((x j) ^ 2 + (x k) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|x j| - |x k|), sq_abs (x j), sq_abs (x k)]
        have h4 : 0 ≤ |A j k| := abs_nonneg _
        nlinarith [mul_nonneg (abs_nonneg (x j)) (abs_nonneg (x k))]
    _ = E * Fintype.card m * (x ⬝ᵥ x) := by
        have h5 : ∀ j, ∑ k : m, (E / 2 * (x j) ^ 2 + E / 2 * (x k) ^ 2) =
            Fintype.card m * (E / 2 * (x j) ^ 2) + E / 2 * ∑ k, (x k) ^ 2 := by
          intro j
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.mul_sum]
        simp only [h5, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum, dotProduct, sq]
        ring
end GlobalTheory.UnifConsts
