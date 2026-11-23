-- Prove2me | solution 1 for GlobalTheory.DirichletTail.hasSum_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:24.888688+00:00
-- url     : https://prove2.me/submissions/e19e451e-5c2f-4910-a54b-db7ae3942d79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_tendsto_rpow_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    HasSum (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ (-δ) - ((n + N + 1 + 1 : ℕ) : ℝ) ^ (-δ))
      (((N + 1 : ℕ) : ℝ) ^ (-δ)) := by
  set g : ℕ → ℝ := fun n ↦ ((n + N + 1 : ℕ) : ℝ) ^ (-δ) with hg
  have hstep : ∀ n, ((n + N + 1 : ℕ) : ℝ) ^ (-δ) - ((n + N + 1 + 1 : ℕ) : ℝ) ^ (-δ) = g n - g (n + 1) := by
    intro n
    simp only [hg]
    rw [show n + 1 + N + 1 = n + N + 1 + 1 by omega]
  have hmono : ∀ n, 0 ≤ g n - g (n + 1) := by
    intro n
    refine sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith))
    exact_mod_cast (show n + N + 1 ≤ n + 1 + N + 1 by omega)
  simp_rw [hstep]
  rw [hasSum_iff_tendsto_nat_of_nonneg hmono]
  simp_rw [Finset.sum_range_sub']
  have h0 : g 0 = ((N + 1 : ℕ) : ℝ) ^ (-δ) := by
    simp only [hg, zero_add]
  rw [← h0]
  have h := (tendsto_const_nhds (x := g 0)).sub (tendsto_rpow_neg hδ N)
  rw [sub_zero] at h
  exact h
end GlobalTheory.DirichletTail
