-- Prove2me | solution 1 for McFadden1974.RandomUtility.lemma1_integrand
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:07:01.712574+00:00
-- url     : https://prove2.me/submissions/3ec8ccdb-d71e-4f95-bfba-43211ba226ea

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset in
theorem solution {J : ℕ} (V : Fin J → ℝ) (i : Fin J) (ε : ℝ) :
    (Real.exp (-ε) * Real.exp (-Real.exp (-ε))) *
        ∏ j ∈ univ.erase i, Real.exp (-Real.exp (-(ε + V i - V j)))
      = Real.exp (-ε) * ∏ j, Real.exp (-Real.exp (-ε - V i + V j)) ∧
    Real.exp (-ε) * ∏ j, Real.exp (-Real.exp (-ε - V i + V j))
      = Real.exp (-ε) * Real.exp (-(Real.exp (-ε)) * ∑ j, Real.exp (V j - V i)) := by
  constructor
  · rw [← Finset.mul_prod_erase (univ : Finset (Fin J))
      (fun j => Real.exp (-Real.exp (-ε - V i + V j))) (Finset.mem_univ i)]
    have h1 : -ε - V i + V i = -ε := by ring
    have h2 : ∏ j ∈ univ.erase i, Real.exp (-Real.exp (-(ε + V i - V j)))
        = ∏ j ∈ univ.erase i, Real.exp (-Real.exp (-ε - V i + V j)) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      congr 3; ring
    simp only [h1, h2]
    ring
  · congr 1
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [neg_mul, ← Real.exp_add]
    congr 2
    ring
