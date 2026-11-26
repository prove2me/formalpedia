-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteAffineSumAbsBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:25:25.708905+00:00
-- url     : https://prove2.me/submissions/344524d9-8fcf-40f4-9f71-b7440cc02790

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem _root_.solution
    {I : Type} (g : I → ℝ) (hg : Summable (fun i => |g i|))
    (a c u T : ℝ) (hu : 0 ≤ u) (ht : u ≤ T)
    (p : I → Prop) [DecidablePred p] (S : Finset I) :
    |a + c * u + ∑ i ∈ S, if p i then g i else 0| ≤
      |a| + |c| * T + ∑' i, |g i| := by
  have hs : |∑ i ∈ S, if p i then g i else 0| ≤ ∑' i, |g i| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun i _ => ?_) (hg.sum_le_tsum S fun i _ => abs_nonneg _))
    split <;> simp
  have hc : |c * u| ≤ |c| * T := by
    rw [abs_mul, abs_of_nonneg hu]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  calc |a + c * u + ∑ i ∈ S, if p i then g i else 0|
      ≤ |a + c * u| + |∑ i ∈ S, if p i then g i else 0| := abs_add_le _ _
    _ ≤ (|a| + |c * u|) + ∑' i, |g i| := add_le_add (abs_add_le _ _) hs
    _ ≤ |a| + |c| * T + ∑' i, |g i| := by linarith

