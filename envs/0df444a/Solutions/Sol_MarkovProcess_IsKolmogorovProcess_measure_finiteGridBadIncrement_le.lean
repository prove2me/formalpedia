-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.measure_finiteGridBadIncrement_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:06:37.607747+00:00
-- url     : https://prove2.me/submissions/68955944-0c08-4efb-b45b-d8caace1584a

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov
import Definitions.Def_MarkovProcess_FiniteGridFoundations
open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem solution
    {T : Type*} [PseudoEMetricSpace T] {N : ℕ} {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M)
    (grid : Fin (N + 1) → T) (δ ε : ℝ≥0∞)
    (hgrid : ∀ i : Fin N, edist (grid i.castSucc) (grid i.succ) ≤ δ)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X grid p ε) ≤ N * (M * δ ^ q / ε ^ p) := by
  have hp := hX.p_pos
  have hq := hX.q_pos
  have hεp0 : ε ^ p ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hε0, hp.le, not_lt.2 hp.le]
  have hεpt : ε ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp.le hεtop
  have hone : ∀ i : Fin N,
      P {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p} ≤
        M * δ ^ q / ε ^ p := by
    intro i
    refine (meas_ge_le_lintegral_div
      ((hX.measurable_edist).pow_const p).aemeasurable hεp0 hεpt).trans ?_
    gcongr
    refine (hX.kolmogorovCondition _ _).trans ?_
    gcongr
    exact hgrid i
  calc P (finiteGridBadIncrement X grid p ε)
      ≤ ∑ i : Fin N, P {ω | ε ^ p ≤ edist (X (grid i.castSucc) ω) (X (grid i.succ) ω) ^ p} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, M * δ ^ q / ε ^ p := Finset.sum_le_sum fun i _ => hone i
    _ = N * (M * δ ^ q / ε ^ p) := by simp
