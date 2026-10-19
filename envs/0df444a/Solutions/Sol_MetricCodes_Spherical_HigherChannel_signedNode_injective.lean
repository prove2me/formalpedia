-- Prove2me | solution 1 for MetricCodes.Spherical.HigherChannel.signedNode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/3c74f738-5be2-4beb-a4b0-98f5a1f84e47

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
open scoped BigOperators
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherChannel
theorem _root_.solution {r : ℕ}
    {L : Fin (r + 1) → ℝ}
    (hpos : ∀ ℓ, 0 < L ℓ) (hinj : Function.Injective L) :
    Function.Injective (signedNode L) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ heq
  cases a <;> cases b <;>
    simp only [signedNode, Bool.false_eq_true, if_false, if_true] at heq
  · exact Prod.ext (hinj (neg_injective heq)) rfl
  · exfalso
    linarith [hpos i, hpos j]
  · exfalso
    linarith [hpos i, hpos j]
  · exact Prod.ext (hinj heq) rfl
end MetricCodes.Spherical.HigherChannel
