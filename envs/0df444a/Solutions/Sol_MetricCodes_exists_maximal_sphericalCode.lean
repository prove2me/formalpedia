-- Prove2me | solution 1 for MetricCodes.exists_maximal_sphericalCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/96aab416-564c-46bb-9375-0cf21915a24f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sphericalCodeNumber_lt_top

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
noncomputable section
open scoped BigOperators InnerProductSpace
open MetricCodes
namespace MetricCodes
theorem _root_.solution {n : ℕ} {s : ℝ}
    (hs : s < 1) :
    ∃ C : SphericalCode n s,
      (C.points.card : ℕ∞) = sphericalCodeNumber n s := by
  let emptyCode : SphericalCode n s :=
    { points := ∅, inner_le := by simp [IsSphericalCode] }
  letI : Nonempty (SphericalCode n s) := ⟨emptyCode⟩
  apply ENat.exists_eq_iSup_of_lt_top
  exact sphericalCodeNumber_lt_top hs
end MetricCodes
