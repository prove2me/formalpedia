-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.factorTrace_inclusion_normal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:20:02.530878+00:00
-- url     : https://prove2.me/submissions/f5e00d71-610c-45b0-85fe-25b073248de5

import Mathlib
import Definitions.Def_OAIQ039C065
import Definitions.Def_OAIQ039C070

section
-- module Solutions.OAIQ039_CM.Commutator_TracialVectorSubalgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma subalgebraTrace_normal (M : VonNeumannAlgebra H) (ξ : H) :
    NormalGNS.BoundedWOTContinuous M (subalgebraTrace M ξ) := by
  intro C
  exact (VectorFunctional.continuous_functional_wot ξ).comp continuous_subtype_val

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VectorFreeGeneration
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

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

lemma factorTrace_inclusion (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
      (inclusion_injective M D hDM)=subalgebraTrace D ξ := by
  ext a
  rfl

lemma factorTrace_inclusion_normal_oai (D : VonNeumannAlgebra H)
    (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    NormalGNS.BoundedWOTContinuous D
      (factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
        (inclusion_injective M D hDM)) := by
  rw [factorTrace_inclusion]
  exact subalgebraTrace_normal D ξ

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.VectorGNS.factorTrace_inclusion_normal_oai := @OAI.Kadison.VectorGNS.factorTrace_inclusion_normal_oai
