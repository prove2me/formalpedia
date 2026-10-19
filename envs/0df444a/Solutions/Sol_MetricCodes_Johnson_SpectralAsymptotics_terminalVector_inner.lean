-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.terminalVector_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/d1e4acbd-14e1-4ad3-a876-eff5acdec750

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tridiagonal_quadratic_sum
import Theorems.Thm_MetricCodes_Hamming_terminal_indicator_edge_sum
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tridiagonal_quadratic_sum
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_terminal_indicator_diagonal_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    @inner ℝ (MetricCodes.Johnson.Space p q L) _
      (MetricCodes.Johnson.operator n w p q L (terminalVector p q L m))
      (terminalVector p q L m) =
      (∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n w p q (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Fin (L - (p + q) + 1),
      (∑ j : Fin (L - (p + q) + 1),
        (if i = j then
          MetricCodes.johnsonHattedDiagonal n w p q (p + q + i.val)
        else if i.val + 1 = j.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + i.val)
        else if j.val + 1 = i.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
        else 0) *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i.val) = _
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun i =>
    ∑ j : Fin (L - (p + q) + 1),
      (if i = j.val then
        MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
      else if i + 1 = j.val then
        MetricCodes.johnsonHattedEdge n w p q (p + q + i)
      else if j.val + 1 = i then
        MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
      else 0) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i
  have hreplace :
      (∑ i : Fin (L - (p + q) + 1),
        ∑ j : Fin (L - (p + q) + 1),
          (if i = j then
            MetricCodes.johnsonHattedDiagonal n w p q (p + q + i.val)
          else if i.val + 1 = j.val then
            MetricCodes.johnsonHattedEdge n w p q (p + q + i.val)
          else if j.val + 1 = i.val then
            MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
          else 0) *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i.val) =
        ∑ i : Fin (L - (p + q) + 1), f i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      simp
    · have hval : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
      simp [hij, hval]
  rw [hreplace, Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (i : ℕ) :
      (∑ j : Fin (L - (p + q) + 1),
        (if i = j.val then
          MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
        else if i + 1 = j.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + i)
        else if j.val + 1 = i then
          MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
        else 0) *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i) =
        ∑ j ∈ Finset.range (L - (p + q) + 1),
          (if i = j then
            MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
          else if i + 1 = j then
            MetricCodes.johnsonHattedEdge n w p q (p + q + i)
          else if j + 1 = i then
            MetricCodes.johnsonHattedEdge n w p q (p + q + j)
          else 0) *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i := by
    let g : ℕ → ℝ := fun j =>
      (if i = j then
        MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
      else if i + 1 = j then
        MetricCodes.johnsonHattedEdge n w p q (p + q + i)
      else if j + 1 = i then
        MetricCodes.johnsonHattedEdge n w p q (p + q + j)
      else 0) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i
    change (∑ j : Fin (L - (p + q) + 1), g j.val) =
      ∑ j ∈ Finset.range (L - (p + q) + 1), g j
    exact Fin.sum_univ_eq_sum_range g (L - (p + q) + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_diagonal_sum (L - (p + q)) m hm]
  rw [MetricCodes.Hamming.terminal_indicator_edge_sum (L - (p + q)) m hm]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega
end MetricCodes.Johnson.SpectralAsymptotics
