-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LatticeCount.summable_inv_one_add_sq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:32.101384+00:00
-- url     : https://prove2.me/submissions/4eb8bfa1-9700-44cc-905b-8ea6cd715abc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticeCount
namespace GlobalTheory.CompanionTheory.LatticeCount
theorem _root_.solution :
    Summable (fun m : ℤ => ((1 : ℝ) + (m : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have hfin : ({0} : Set ℤ).Finite := Set.finite_singleton 0
  refine Filter.mem_cofinite.2 (hfin.subset ?_)
  intro m hm
  by_contra h0
  have h0' : m ≠ 0 := by simpa using h0
  apply hm
  have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (m : ℝ) ≠ 0 := by exact_mod_cast h0'
    positivity
  have hpos : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  show ‖((1 : ℝ) + (m : ℝ) ^ 2)⁻¹‖ ≤ 1 / (m : ℝ) ^ 2
  rw [Real.norm_of_nonneg (inv_nonneg.2 hpos.le), one_div]
  exact inv_anti₀ hm0 (by linarith)
end GlobalTheory.CompanionTheory.LatticeCount
