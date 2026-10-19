-- Prove2me | solution 1 for MetricCodes.Spherical.HigherProjectionInstantiation.mem_codePoints_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/7740c1cc-0046-4321-9647-ca8906197df2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherProjectionInstantiation
theorem _root_.solution {n : ℕ} {s : ℝ}
    (C : SpherePacking.SphericalCode n s) (x : SpherePoint n) :
    x ∈ codePoints C ↔ x.val ∈ C.points := by
  classical
  constructor
  · intro hx
    change x ∈ C.points.attach.map _ at hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    have hval : y.val = x.val := congrArg Subtype.val hy
    exact hval ▸ y.property
  · intro hx
    change x ∈ C.points.attach.map _
    refine Finset.mem_map.mpr ⟨⟨x.val, hx⟩, ?_, ?_⟩
    · simp
    · apply Subtype.ext
      rfl
end MetricCodes.Spherical.HigherProjectionInstantiation
