-- Prove2me | solution 1 for MarkovProcess.unitDyadicGrid_edist_adjacent_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:07:21.171781+00:00
-- url     : https://prove2.me/submissions/b17f2a0b-2066-4dd1-9101-5a59ecfc1737

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov
import Definitions.Def_MarkovProcess_FiniteGridFoundations
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem solution (n : ℕ) (i : Fin (2 ^ n)) :
    edist (unitDyadicGrid n i.castSucc) (unitDyadicGrid n i.succ) ≤
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have h : dist (unitDyadicGrid n i.castSucc) (unitDyadicGrid n i.succ) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [NNRat.dist_eq]
    simp only [unitDyadicGrid, Fin.coe_castSucc, Fin.val_succ]
    push_cast
    rw [Rat.dist_eq]
    push_cast
    have e : ((i : ℝ) + 1) / 2 ^ n - (i : ℝ) / 2 ^ n = ((2 : ℝ) ^ n)⁻¹ := by
      field_simp; ring
    rw [abs_sub_comm, e, abs_of_pos (by positivity)]
  rw [edist_dist, h, ENNReal.ofReal_inv_of_pos (by positivity)]
  simp
