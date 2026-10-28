-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.generatedFreeAlgebra_constants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:25:54.132879+00:00
-- url     : https://prove2.me/submissions/14953ebb-3d27-4753-85d4-1100fa138b06

import Mathlib
import Definitions.Def_OAIQ039C072
import Theorems.Thm_OAI_Kadison_TracialSequence_constantAction_apply

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

lemma generatedFreeAlgebra_constants_oai
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω)) (a : A) :
    leftRestricted τ ω (constantSequence a)∈generatedFreeAlgebra τ ω D := by
  rw [← constantAction_apply]
  with_reducible
    exact GeneratedFreePair.right_mem (H := boundedSubspace τ ω) (A := A)
      D (constantAction τ ω) a

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.generatedFreeAlgebra_constants_oai := @OAI.Kadison.TracialSequence.generatedFreeAlgebra_constants_oai
