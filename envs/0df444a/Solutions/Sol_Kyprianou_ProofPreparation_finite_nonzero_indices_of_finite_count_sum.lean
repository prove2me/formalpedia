-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:09.904803+00:00
-- url     : https://prove2.me/submissions/47bea992-5373-49b6-a969-7a9666a71e31

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem finite_nonzero_indices_of_finite_count_sum
    (N : ℕ → ℕ)
    (hfin : (∑' k, (N k : ENNReal)) < ⊤) :
    Set.Finite {k : ℕ | N k ≠ 0} := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hfin.ne one_ne_zero).subset
  intro k hk
  simp only [Set.mem_setOf_eq] at hk ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.2 hk

end Kyprianou.ProofPreparation

theorem solution
    (N : ℕ → ℕ)
    (hfin : (∑' k, (N k : ENNReal)) < ⊤) :
    Set.Finite {k : ℕ | N k ≠ 0} := by
  first
  | exact Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum
  | exact Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum ..
  | (apply Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum <;> assumption)
