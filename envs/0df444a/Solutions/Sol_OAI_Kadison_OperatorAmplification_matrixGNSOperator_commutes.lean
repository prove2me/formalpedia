-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:01:37.561519+00:00
-- url     : https://prove2.me/submissions/b581a0cf-3580-457f-9699-8b7f0cca43e4

import Mathlib
import Definitions.Def_OAIQ039C063
import Definitions.Def_OAIQ039C067
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixInclusion_commutes

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

lemma commutes_iff (T : K →L[ℂ] K) (a : H →L[ℂ] H) :
    U.symm.conjStarAlgEquiv T*a=a*U.symm.conjStarAlgEquiv T ↔
      T*U.conjStarAlgEquiv a=U.conjStarAlgEquiv a*T := by
  constructor
  · intro h
    simpa only [map_mul,conjugate_inverse] using congrArg U.conjStarAlgEquiv h
  · intro h
    apply U.conjStarAlgEquiv.injective
    change U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv T*a)=
      U.conjStarAlgEquiv (a*U.symm.conjStarAlgEquiv T)
    simpa only [map_mul,conjugate_inverse] using h

lemma commutes_of_conjugates (T b : K →L[ℂ] K) (a : H →L[ℂ] H)
    (h : U.conjStarAlgEquiv a=b) (hc : T*b=b*T) :
    U.symm.conjStarAlgEquiv T*a=a*U.symm.conjStarAlgEquiv T := by
  rw [commutes_iff,h]
  exact hc

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

lemma matrixGNSOperator_commutes_oai
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (hT : ∀ q : Q,T*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))=
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom (NormalSubalgebra.inclusion M Q hQM q))*T)
    (X : matrixVonNeumann ι i₀ Q) :
    matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom (matrixInclusion ι i₀ M Q hQM X)=
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom (matrixInclusion ι i₀ M Q hQM X)*matrixGNSOperator ι M τ T := by
  apply UnitaryTransport.commutes_of_conjugates (MatrixGNS.unitary (ι:=ι) τ)
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T)
    (MatrixGNS.representation τ (matrixInclusion ι i₀ M Q hQM X))
    ((MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom (matrixInclusion ι i₀ M Q hQM X))
    (MatrixGNS.unitary_conjugates τ (matrixInclusion ι i₀ M Q hQM X))
  exact matrixInclusion_commutes ι i₀ M Q hQM
    ((diagonal (H:=τ.GNS) ι).comp τ.gnsStarAlgHom) T hT X

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes_oai := @OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutes_oai
