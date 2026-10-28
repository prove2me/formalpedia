-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:01:10.670336+00:00
-- url     : https://prove2.me/submissions/9f59b823-bd4f-4bff-9070-529d112b3d08

import Mathlib
import Definitions.Def_OAIQ039C067

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

lemma intertwines (a : A) :
    (embedding τ φ ξ hτ).toContinuousLinearMap.comp (τ.gnsStarAlgHom a)=
      (φ a).comp (embedding τ φ ξ hτ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have hl : τ.gnsStarAlgHom a (TracialGNS.algebraVector τ b)=
      TracialGNS.algebraVector τ (a*b) := TracialGNS.left_coe τ a b
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,hl,embedding_coe,
    map_mul,mul_apply_eq_comp]

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ)) (hcyc : DenseRange (fun a : A => φ a ξ))

lemma equivalence_intertwines (a : A) (v : τ.GNS) :
    equivalence τ φ ξ hτ hcyc (τ.gnsStarAlgHom a v)=φ a (equivalence τ φ ξ hτ hcyc v) :=
  congrArg (fun T : τ.GNS →L[ℂ] H => T v) (intertwines τ φ ξ hτ a)

lemma equivalence_conjugates (a : A) :
    (equivalence τ φ ξ hτ hcyc).conjStarAlgEquiv (τ.gnsStarAlgHom a)=φ a := by
  ext v
  change equivalence τ φ ξ hτ hcyc
    (τ.gnsStarAlgHom a ((equivalence τ φ ξ hτ hcyc).symm v))=φ a v
  rw [equivalence_intertwines,LinearIsometryEquiv.apply_symm_apply]

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixGNSUnitaryDecidableEq
variable (τ : A →ₚ[ℂ] ℂ)

lemma unitary_conjugates [Nonempty ι] (X : CStarMatrix ι ι A) :
    (unitary (ι:=ι) τ).conjStarAlgEquiv ((trace (ι:=ι) τ).gnsStarAlgHom X)=representation τ X :=
  VectorGNS.equivalence_conjugates _ _ _ _ _ _

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryCommuteNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

lemma conjugate_inverse (T : K →L[ℂ] K) :
    U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv T)=T := by
  ext v
  simp

lemma conjugate_commutator (T : K →L[ℂ] K) (a : H →L[ℂ] H) :
    U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv T*a-a*U.symm.conjStarAlgEquiv T)=
      T*U.conjStarAlgEquiv a-U.conjStarAlgEquiv a*T := by
  rw [map_sub,map_mul,map_mul,conjugate_inverse]

lemma commutator_norm (T : K →L[ℂ] K) (a : H →L[ℂ] H) :
    ‖U.symm.conjStarAlgEquiv T*a-a*U.symm.conjStarAlgEquiv T‖=
      ‖T*U.conjStarAlgEquiv a-U.conjStarAlgEquiv a*T‖ := by
  have : StarHomClass ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K))
      (H →L[ℂ] H) (K →L[ℂ] K) :=
    ⟨fun equivalence => equivalence.map_star'⟩
  rw [←conjugate_commutator,
    StarAlgEquiv.norm_map (A := H →L[ℂ] H) (B := K →L[ℂ] K) U.conjStarAlgEquiv]

lemma commutator_norm_of_conjugates (T b : K →L[ℂ] K) (a : H →L[ℂ] H)
    (h : U.conjStarAlgEquiv a=b) :
    ‖U.symm.conjStarAlgEquiv T*a-a*U.symm.conjStarAlgEquiv T‖=‖T*b-b*T‖ := by
  rw [commutator_norm,h]

end Kadison.UnitaryTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSCornerBound
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

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_3
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixGNSOperator_commutator_norm_oai
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : CStarMatrix ι ι M) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖=
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ X-
      MatrixGNS.representation τ X*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖ := by
  exact UnitaryTransport.commutator_norm_of_conjugates (MatrixGNS.unitary (ι:=ι) τ)
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T) (MatrixGNS.representation τ X)
    ((MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X) (MatrixGNS.unitary_conjugates τ X)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm_oai := @OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm_oai
