-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.ambient_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:52:32.212273+00:00
-- url     : https://prove2.me/submissions/638d306f-cffe-4967-908f-cc1175e9d6fe

import Mathlib
import Definitions.Def_OAIQ039C065

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
-- module Solutions.OAIQ039_CM.Commutator_GNSCornerTransport
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

open ContinuousLinearMap

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)

variable (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

include htr in
lemma ambient_range_oai (R : Bool → StarSubalgebra ℂ M)
    {X : (subalgebraTrace M ξ).GNS →L[ℂ] (subalgebraTrace M ξ).GNS}
    (hX : X∈ambientOperators (vectorState M ξ hfaith hone) R) :
    ∃ a : M,(subalgebraTrace M ξ).gnsStarAlgHom a=X := by
  have hb : X∈Set.centralizer (Set.centralizer (Set.range (subalgebraTrace M ξ).gnsStarAlgHom)) := by
    intro Y hY
    apply (mem_ambientOperators _ _).mp hX Y
    rintro Z ⟨a,_,rfl⟩
    exact hY _ ⟨a,rfl⟩
  rw [NormalGNS.range_bicommutant M (subalgebraTrace M ξ) htr
    (subalgebraTrace_normal M ξ)] at hb
  exact hb

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.VectorGNS.ambient_range_oai := @OAI.Kadison.VectorGNS.ambient_range_oai
