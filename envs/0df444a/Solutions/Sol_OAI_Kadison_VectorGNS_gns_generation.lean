-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.gns_generation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:54:25.471991+00:00
-- url     : https://prove2.me/submissions/9683256f-67ac-43f3-bed8-64dd337b06f7

import Mathlib
import Definitions.Def_OAIQ039C059
import Definitions.Def_OAIQ039C065
import Theorems.Thm_OAI_Kadison_NormalGNS_image_bicommutant

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hnormal : BoundedWOTContinuous M τ)
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
  (hSM : S≤M.toStarSubalgebra)
  (N : VonNeumannAlgebra τ.GNS)
  (hSN : ∀ a : M,(a:H →L[ℂ] H)∈S → τ.gnsStarAlgHom a∈N)

include hnormal hSM hSN in
lemma image_bicommutant_general (a : M)
    (ha : (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    τ.gnsStarAlgHom a∈N := by
  let C : Set M := {a | τ.gnsStarAlgHom a∈N}
  have hC : IsClosed C := (VonNeumannCStar.isClosed N).preimage (map_continuous τ.gnsStarAlgHom)
  have hvalC : IsClosed ((Subtype.val : M → (H →L[ℂ] H)) '' C) :=
    (VonNeumannCStar.isClosed M).isClosedMap_subtype_val C hC
  have hSC : (S : Set (H →L[ℂ] H)) ⊆ (Subtype.val : M → (H →L[ℂ] H)) '' C := by
    intro a ha
    exact ⟨⟨a,hSM ha⟩,hSN ⟨a,hSM ha⟩ ha,rfl⟩
  have hcl := closure_minimal hSC hvalC
  have hSM' : S.topologicalClosure≤M.toStarSubalgebra :=
    S.topologicalClosure_minimal hSM (VonNeumannCStar.isClosed M)
  have hSN' (b : M) (hb : (b:H →L[ℂ] H)∈S.topologicalClosure) : τ.gnsStarAlgHom b∈N := by
    have hbcl : (b:H →L[ℂ] H)∈closure (S : Set (H →L[ℂ] H)) := hb
    obtain ⟨c,hc,hcb⟩ := hcl hbcl
    have he : c=b := Subtype.ext hcb
    change τ.gnsStarAlgHom c∈N at hc
    simpa only [he] using hc
  apply image_bicommutant M τ hnormal S.topologicalClosure S.isClosed_topologicalClosure hSM' N hSN' a
  intro T hT
  apply ha T
  intro b hb
  exact hT b (S.le_topologicalClosure hb)

end Kadison.NormalGNS

end

end
end

end OAI
end

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

theorem gns_generation_oai (R : Bool → StarSubalgebra ℂ M)
    (hgen : ∀ a : M,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (((iSup R).map M.toStarSubalgebra.subtype) : Set (H →L[ℂ] H)))) (a : M) :
    (subalgebraTrace M ξ).gnsStarAlgHom a∈Set.centralizer (Set.centralizer
      (generatedOperators (vectorState M ξ hfaith hone) R : Set _)) := by
  let t := vectorState M ξ hfaith hone
  let S := (iSup R).map M.toStarSubalgebra.subtype
  let N := ambientVonNeumann t R
  have hSM : S≤M.toStarSubalgebra := by
    rintro x ⟨b,_,rfl⟩
    exact b.property
  have hSN (b : M) (hb : (b:H →L[ℂ] H)∈S) :
      (subalgebraTrace M ξ).gnsStarAlgHom b∈N := by
    obtain ⟨c,hc,hcb⟩ := hb
    have he : c=b := Subtype.ext hcb
    subst c
    exact (mem_ambientOperators t R).mpr (Set.subset_centralizer_centralizer ⟨b,hc,rfl⟩)
  exact (mem_ambientOperators t R).mp
    (NormalGNS.image_bicommutant_general M (subalgebraTrace M ξ)
      (subalgebraTrace_normal M ξ) S hSM N hSN a (hgen a))

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.VectorGNS.gns_generation_oai := @OAI.Kadison.VectorGNS.gns_generation_oai
