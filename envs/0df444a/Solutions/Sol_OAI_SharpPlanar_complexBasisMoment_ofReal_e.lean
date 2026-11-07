-- Prove2me | solution 1 for OAI.SharpPlanar.complexBasisMoment_ofReal_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T16:44:06.167664+00:00
-- url     : https://prove2.me/submissions/12d3ef01-bbf8-44f7-9a73-d01bb9650543

import Mathlib
import Definitions.Def_OAIQ098E018

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis

lemma complexU_ofReal (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_ofReal (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl
lemma complexLambda_ofReal (t : ℝ) : complexLambda t = lambda t := rfl
lemma complexZ_ofReal (t : ℝ) : complexZ t = z t := rfl
lemma complexBasisMoment_ofReal_e_oai (d e : Bool) (n j m : ℕ) (t : ℝ) :
    complexBasisMoment d e n j m t = basisMoment d e n j m t := by
  unfold complexBasisMoment complexBasis basisMoment basisFunction complexTransformedFactor
  rw [complexU_ofReal,complexV_ofReal,complexLambda_ofReal,complexZ_ofReal]
  cases d <;> cases e <;> simp <;> ring


end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.complexBasisMoment_ofReal_e_oai := @OAI.SharpPlanar.complexBasisMoment_ofReal_e_oai
