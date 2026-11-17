-- Prove2me | solution 1 for LevyStochCalc.Poisson.measure_eq_sum_partitionAtom_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T00:11:28.887345+00:00
-- url     : https://prove2.me/submissions/1e8c40ee-ff27-4767-935c-c646d3e0aafa

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
import Theorems.Thm_LevyStochCalc_Poisson_eq_biUnion_partitionAtom_ch02
import Theorems.Thm_LevyStochCalc_Poisson_pairwise_disjoint_partitionAtom_ch02
import Theorems.Thm_LevyStochCalc_Poisson_measurableSet_partitionAtom_ch02
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u

open LevyStochCalc.Poisson
theorem solution
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ}
    {C : Fin n → Set 𝓨}
    (μ : Measure 𝓨) (hC : ∀ i, MeasurableSet (C i))
    (i : Fin n) :
    μ (C i) = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      μ (partitionAtom C S) := by
  rw [eq_biUnion_partitionAtom_ch02 (C := C) i]
  exact measure_biUnion_finset
    (fun S _ T _ hST => pairwise_disjoint_partitionAtom_ch02 (by simpa using hST))
    (fun S _ => measurableSet_partitionAtom_ch02 hC S)
