-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.generatedByStages_of_represented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:54:02.267146+00:00
-- url     : https://prove2.me/submissions/5bcf7459-f040-4b4f-a613-baaae110fe48

import Mathlib
import Definitions.Def_OAIQ039C061
import Definitions.Def_OAIQ039C064
import Theorems.Thm_OAI_Kadison_NormalGNS_matrix_stages_gns

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

lemma generatedByStages_of_represented_oai
    (hgen : ∀ a : D,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (NormalGNS.representedStages D I φ : Set (H →L[ℂ] H)))) :
    GeneratedByStages D ξ I φ := fun a =>
  NormalGNS.matrix_stages_gns D (subalgebraTrace D ξ) (subalgebraTrace_normal D ξ) I φ a (hgen a)

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.VectorGNS.generatedByStages_of_represented_oai.{u_1} := @OAI.Kadison.VectorGNS.generatedByStages_of_represented_oai.{u_1}
