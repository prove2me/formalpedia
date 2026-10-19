-- Prove2me | solution 1 for MetricCodes.Hamming.terminalVector_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/dd8e914e-22d1-4bf5-8410-d74d399c4421

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tridiagonal_quadratic_sum
import Theorems.Thm_MetricCodes_Hamming_terminal_indicator_edge_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    @inner ℝ (Space k L) _
        (operator n k L (terminalVector k L m))
        (terminalVector k L m) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ p : Fin (L - k + 1),
      (∑ q : Fin (L - k + 1),
        (if p.val + 1 = q.val then
          MetricCodes.hammingJacobiEntry n k (k + p.val)
        else if q.val + 1 = p.val then
          MetricCodes.hammingJacobiEntry n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val) *
        terminalIndicator (L - k) m p.val) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun p =>
    ∑ q : Fin (L - k + 1),
      (if p + 1 = q.val then
        MetricCodes.hammingJacobiEntry n k (k + p)
      else if q.val + 1 = p then
        MetricCodes.hammingJacobiEntry n k (k + q.val)
      else 0) * terminalIndicator (L - k) m q.val *
        terminalIndicator (L - k) m p
  change
    (∑ p : Fin (L - k + 1), f p.val) =
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)
  rw [Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (p : ℕ) :
      (∑ q : Fin (L - k + 1),
        (if p + 1 = q.val then
          MetricCodes.hammingJacobiEntry n k (k + p)
        else if q.val + 1 = p then
          MetricCodes.hammingJacobiEntry n k (k + q.val)
        else 0) * terminalIndicator (L - k) m q.val *
          terminalIndicator (L - k) m p) =
        ∑ q ∈ Finset.range (L - k + 1),
          (if p + 1 = q then
            MetricCodes.hammingJacobiEntry n k (k + p)
          else if q + 1 = p then
            MetricCodes.hammingJacobiEntry n k (k + q)
          else 0) * terminalIndicator (L - k) m q *
            terminalIndicator (L - k) m p := by
    let g : ℕ → ℝ := fun q =>
      (if p + 1 = q then
        MetricCodes.hammingJacobiEntry n k (k + p)
      else if q + 1 = p then
        MetricCodes.hammingJacobiEntry n k (k + q)
      else 0) * terminalIndicator (L - k) m q *
        terminalIndicator (L - k) m p
    change (∑ q : Fin (L - k + 1), g q.val) =
      ∑ q ∈ Finset.range (L - k + 1), g q
    exact Fin.sum_univ_eq_sum_range g (L - k + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_edge_sum (L - k) m hm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  omega
end MetricCodes.Hamming
