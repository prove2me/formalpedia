-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.constantAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:57.292636+00:00
-- url     : https://prove2.me/submissions/f88c3016-7e3b-4dc3-964c-decc0a1988ca

import Mathlib
import Definitions.Def_OAIQ039C067

section
-- module Solutions.OAIQ039_CM.Commutator_TracialGeneratedAlgebra
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialSequence

lemma constantAction_apply_oai {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (value : A) :
    constantAction τ ω value = leftRestricted τ ω (constantSequence value) := rfl

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.constantAction_apply_oai := @OAI.Kadison.TracialSequence.constantAction_apply_oai
