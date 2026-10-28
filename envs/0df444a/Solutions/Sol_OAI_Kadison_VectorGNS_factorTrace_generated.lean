-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.factorTrace_generated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:20:01.318827+00:00
-- url     : https://prove2.me/submissions/4e98072e-e21f-4bed-843c-59bef77c451c

import Mathlib
import Definitions.Def_OAIQ039C064
import Definitions.Def_OAIQ039C065
import Definitions.Def_OAIQ039C070

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

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VectorStageGeneration
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

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.VectorGNS

open FreeWordTensor FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (D : VonNeumannAlgebra H) (ξ : H)
  (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (M : VonNeumannAlgebra H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)
  (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)

lemma factorTrace_generated_oai (hgen : GeneratedByStages D ξ I φ) :
    ∀ a : D,(factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
      (inclusion_injective M D hDM)).gnsStarAlgHom a∈Set.centralizer (Set.centralizer
        (TracialGNS.stageAlgebra (factorTrace (vectorState M ξ hfaith hone) (inclusion M D hDM)
          (inclusion_injective M D hDM)) I φ : Set _)) := by
  rw [factorTrace_inclusion]
  exact hgen

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.VectorGNS.factorTrace_generated_oai.{u_1} := @OAI.Kadison.VectorGNS.factorTrace_generated_oai.{u_1}
