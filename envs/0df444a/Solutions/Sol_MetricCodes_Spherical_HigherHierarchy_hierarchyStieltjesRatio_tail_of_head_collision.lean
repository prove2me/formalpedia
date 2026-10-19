-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyStieltjesRatio_tail_of_head_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/1d56c5e9-ee73-41db-9478-f1f5f836568e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyStieltjesRatio_prepend

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
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (h : WeakInterlacing a b) (hcollision : a 0 = b 0)
    {t : ℝ} (ht : 0 < t) :
    hierarchyStieltjesRatio a b t =
      hierarchyStieltjesRatio (Fin.tail a) (Fin.tail b) t := by
  conv_lhs =>
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
  change hierarchyStieltjesRatio
    (prependAmbient (a 0) (Fin.tail a))
    (prependStabilizer (b 0) (Fin.tail b)) t = _
  rw [hierarchyStieltjesRatio_prepend]
  have hfactor : t + quadraticCoordinate (a 0) ≠ 0 := by
    have ha := h.ambient_nonneg 0
    unfold quadraticCoordinate
    nlinarith [mul_nonneg ha (by linarith : 0 ≤ 1 + a 0)]
  rw [← hcollision]
  simp [hfactor]
end MetricCodes.Spherical.HigherHierarchy
