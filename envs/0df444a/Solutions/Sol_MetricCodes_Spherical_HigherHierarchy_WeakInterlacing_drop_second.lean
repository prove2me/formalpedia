-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.WeakInterlacing.drop_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/71f58a0c-ce55-4abe-87a8-a77f55549eea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
namespace WeakInterlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (h : WeakInterlacing a b)
    (hcollision : b 0 = a (1 : Fin (r + 2))) :
    WeakInterlacing
      (Fin.cons (a 0) (Fin.tail (Fin.tail a))) (Fin.tail b) := by
  cases r with
  | zero =>
      constructor
      · simpa using h.ambient_nonneg 0
      · intro i
        exact Fin.elim0 i
  | succ r =>
      constructor
      · simpa [Fin.tail] using h.1
      · intro i
        induction i using Fin.cases with
        | zero =>
            constructor
            · change b (1 : Fin (r + 2)) ≤ a 0
              exact ((h.2 (1 : Fin (r + 2))).1).trans
                (h.antitone_ambient (Fin.zero_le _))
            · change a (2 : Fin (r + 3)) ≤ b (1 : Fin (r + 2))
              exact (h.2 (1 : Fin (r + 2))).2
        | succ i =>
            simpa [Fin.tail] using h.2 i.succ.succ
end WeakInterlacing
end MetricCodes.Spherical.HigherHierarchy
