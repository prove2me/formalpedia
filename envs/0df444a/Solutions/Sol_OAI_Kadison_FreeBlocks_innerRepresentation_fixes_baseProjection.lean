-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.innerRepresentation_fixes_baseProjection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:04:19.865444+00:00
-- url     : https://prove2.me/submissions/a1e6d04f-b194-4512-90bb-254c2ec6fd48

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_commutes_other

section
-- module Solutions.OAIQ039_CM.Commutator_FreeNormalizer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_vacuum (u : unitary D) :
    innerRepresentation t ht f S i hS hfree hgen u (TracialGNS.vacuum t.functional)=
      TracialGNS.vacuum t.functional := by
  exact action_word t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen [] reduced_nil

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_fixes_base (hji : j≠i) (u : unitary D)
    {x : t.functional.GNS} (hx : x∈baseSpace t S j) :
    innerRepresentation t ht f S i hS hfree hgen u x=x := by
  let W := innerRepresentation t ht f S i hS hfree hgen u
  apply closure_minimal (t := {x | W x=x}) ?_ (isClosed_eq W.continuous continuous_id) hx
  rintro y ⟨a,⟨b,hb,rfl⟩,rfl⟩
  have h := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS =>
    T (TracialGNS.vacuum t.functional))
    (innerRepresentation_commutes_other t ht f S i j hS hfree hgen hji u b hb)
  change W (t.functional.gnsStarAlgHom b (TracialGNS.vacuum t.functional))=
    t.functional.gnsStarAlgHom b (W (TracialGNS.vacuum t.functional)) at h
  rw [innerRepresentation_vacuum t ht f S i hS hfree hgen u] at h
  exact h

lemma innerRepresentation_fixes_baseProjection_oai (hji : j≠i) (u : unitary D) :
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)*
      (baseSpace t S j).starProjection=(baseSpace t S j).starProjection := by
  ext x
  exact innerRepresentation_fixes_base t ht f S i j hS hfree hgen hji u
    ((baseSpace t S j).starProjection_apply_mem x)

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.innerRepresentation_fixes_baseProjection_oai.{u_1} := @OAI.Kadison.FreeBlocks.innerRepresentation_fixes_baseProjection_oai.{u_1}
