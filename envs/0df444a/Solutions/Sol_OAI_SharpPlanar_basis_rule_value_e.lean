-- Prove2me | solution 1 for OAI.SharpPlanar.basis_rule_value_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T16:44:04.97126+00:00
-- url     : https://prove2.me/submissions/558e151b-2575-4abe-a14a-6a1c3e1bd120

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_complexBasisMoment_ofReal_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quadrature enclosures for cardinal moments

The certified quadrature grid and cardinal basis enclosures bound the finite moment rule.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid

lemma basis_rule_value_e_oai (n m : ℕ) (d e : Bool) :
    (∑ j : Fin 6, pieceRule (complexBasisMoment d e n j.val m) j.val) =
      momentRuleValue quadraturePoint fejerWeight n m d e := by
  unfold pieceRule momentRuleValue
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have ht : diskAffine j.val (fejerNode v.val) = (quadraturePoint j.val v.val:ℂ) := by
    unfold diskAffine diskCenter quadraturePoint
    push_cast
    ring
  rw [ht,complexBasisMoment_ofReal_e]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.basis_rule_value_e_oai := @OAI.SharpPlanar.basis_rule_value_e_oai
