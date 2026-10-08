-- Prove2me | solution 1 for LocalSearchFL.UFL.ufl_locality_gap
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T11:42:11.854965+00:00
-- url     : https://prove2.me/submissions/f1895e45-4d35-4c33-916d-10174a7de66c

import Theorems.Thm_LocalSearchFL_UFL_service_cost_lemma_4_1
import Theorems.Thm_LocalSearchFL_UFL_facility_cost_lemma_4_2

open LocalSearchFL.UFL

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (S : Finset Fa) (hS : S.Nonempty) (hloc : IsUFLLocalOpt I f S hS)
    (O : Finset Fa) (hO : O.Nonempty) :
    uflCost I f S hS ≤ 3 * uflCost I f O hO := by
  have hservice := service_cost_lemma_4_1 I f hf S hS hloc O hO
  have hfacility := facility_cost_lemma_4_2 I f hf S hS hloc O hO
  have hnonneg : 0 ≤ costF f O := Finset.sum_nonneg (fun i _ => hf i)
  unfold uflCost
  linarith

#print axioms solution
