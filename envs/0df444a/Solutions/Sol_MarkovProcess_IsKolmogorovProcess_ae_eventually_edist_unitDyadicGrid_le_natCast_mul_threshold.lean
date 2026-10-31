-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_le_natCast_mul_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:37:04.434757+00:00
-- url     : https://prove2.me/submissions/cb05a5c1-2603-4220-bb55-9bf227cfc480

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicIncrements_eff99a2c
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MarkovProcess MarkovProcess.IsKolmogorovProcess

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem solution
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i j : Fin (2 ^ n + 1),
      (i : ℕ) ≤ j →
        edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) ≤
          (j.val - i.val : ℕ) * dyadicIncrementThreshold γ n := by
  filter_upwards
    [IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_adjacent_lt_threshold
      hX hγ hγq] with ω hω
  filter_upwards [hω] with n hn
  intro i j hij
  exact p2m_embedded_f8faf916638e569b
    (fun k ↦ (hn k).le) i j hij
