-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BinaryCadlagFiniteV15
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:10:06.952228+00:00
-- url     : https://prove2.me/submissions/47b776a8-6df9-496d-bc8a-5802c8e16e64

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open AvramDividend.Classical
theorem solution
    (f : NNReal → ℝ)
    (hVal : ∀ u, f u = 0 ∨ f u = -1)
    (hLVal : ∀ u, 0 < u → Function.leftLim f u = 0 ∨ Function.leftLim f u = -1)
    (hR : ∀ u, ContinuousWithinAt f (Ici u) u)
    (hL : ∀ u, 0 < u → Tendsto f (nhdsWithin u (Iio u)) (nhds (Function.leftLim f u)))
    (T : NNReal) :
    Set.Finite {u : NNReal | 0 < u ∧ u ≤ T ∧ f u - Function.leftLim f u ≠ 0} := by
  apply (avram_p2_h_cadlag_generic_finite_large_jumps_on_horizon f hR hL T 1
    (by norm_num)).subset
  intro u hu
  refine ⟨hu.1,hu.2.1,?_⟩
  rcases hVal u with hf | hf <;> rcases hLVal u hu.1 with hl | hl <;>
    simp_all [Real.dist_eq, Set.mem_setOf_eq]
