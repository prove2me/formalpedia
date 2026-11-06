-- Prove2me | solution 1 for OAI.FourierBridge.coupled_cutoff_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:22.478477+00:00
-- url     : https://prove2.me/submissions/17ea01c0-f05e-4c55-88c2-79ef5412d58f

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (V : ℝ → ℂ) (a y M : ι → ℝ)
    (hwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hVone : ∀ s,
      |s| ≤ ∑ j : ι, |a j| * M j → V s = 1)
    (hprod : (∏ j : ι, W j (y j)) ≠ 0) :
    V (∑ j : ι, a j * y j) = 1 := by
  classical
  apply hVone
  calc
    |∑ j : ι, a j * y j| ≤ ∑ j : ι, |a j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : ι, |a j| * M j := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonzero : W j (y j) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwindow j (y j) hnonzero) (abs_nonneg _)
end OAI.FourierBridge
