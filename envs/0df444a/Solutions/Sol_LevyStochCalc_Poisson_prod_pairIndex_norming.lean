-- Prove2me | solution 1 for LevyStochCalc.Poisson.prod_pairIndex_norming
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T13:51:31.729882+00:00
-- url     : https://prove2.me/submissions/6d8050de-5fae-48d0-b02e-66fee4aa519d

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F000

open LevyStochCalc.Poisson in
theorem solution {p : ℕ} (lam : Fin p → ℝ) (k l : Fin p) :
    (∏ j, ((pairIndex k l j).factorial : ℝ) * lam j ^ (pairIndex k l j))
      = if k = l then 2 * lam k * lam l else lam k * lam l := by
  classical
  have hsub : ({k, l} : Finset (Fin p)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.prod_subset hsub]
  · split_ifs with hkl
    · subst hkl
      simp [pairIndex]; ring
    · rw [Finset.prod_pair hkl]
      simp [pairIndex, hkl, Ne.symm hkl]
  · intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [pairIndex, hj.1, hj.2]
