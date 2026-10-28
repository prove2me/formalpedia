-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixTrace_faithful
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:05:17.382715+00:00
-- url     : https://prove2.me/submissions/cf07d5af-b903-4f49-b438-2a424dc46dad

import Mathlib
import Definitions.Def_OAIQ039C068

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma coe_preGNS_eq_zero_iff
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    (τ.toPreGNS a : τ.GNS) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply hfaith a
    have hn : ‖τ.toPreGNS a‖ = 0 := by
      rw [← Completion.norm_coe, h, norm_zero]
    have := τ.preGNS_norm_sq (τ.toPreGNS a)
    simpa [hn] using this.symm
  · rintro rfl
    simp [Completion.coe_zero]

end TracialGNS

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTraceFaithful
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

attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEq_solutions
variable (τ : A →ₚ[ℂ] ℂ)

omit [Fintype ι] in
lemma algebraArray_eq_zero_iff
    (hfaith : ∀ a : A, τ (star a*a)=0 → a=0) (X : CStarMatrix ι ι A) :
    algebraArray τ X=0 ↔ X=0 := by
  constructor
  · intro h
    apply CStarMatrix.ext
    intro i j
    have hv := congrArg (fun v : ArraySpace (ι:=ι) τ => v i j) h
    exact (TracialGNS.coe_preGNS_eq_zero_iff τ hfaith (X i j)).mp hv
  · rintro rfl
    ext i j
    change (τ.toPreGNS 0 : τ.GNS)=0
    exact (TracialGNS.coe_preGNS_eq_zero_iff τ hfaith 0).mpr rfl

lemma trace_faithful [Nonempty ι]
    (hfaith : ∀ a : A, τ (star a*a)=0 → a=0) (X : CStarMatrix ι ι A)
    (hz : trace (ι:=ι) τ (star X*X)=0) : X=0 := by
  have hv : representation τ X (vacuum (ι:=ι) τ)=0 := by
    change VectorFunctional.functional (vacuum (ι:=ι) τ)
      (representation τ (star X*X))=0 at hz
    rw [map_mul,map_star,VectorFunctional.functional_star_mul] at hz
    exact inner_self_eq_zero.mp hz
  rw [representation_vacuum] at hv
  apply (algebraArray_eq_zero_iff τ hfaith X).mp
  exact (smul_eq_zero.mp hv).resolve_left (scale_ne_zero (ι:=ι))

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixNormalTrace
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

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

lemma equiv_star_mul {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (e : B ≃⋆ₐ[ℂ] C) (x : B) : e (star x*x)=star (e x)*e x := by
  rw [map_mul,map_star]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixTrace_faithful_oai (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (X : matrixVonNeumann ι i₀ M) (hX : matrixTrace ι i₀ M τ (star X*X)=0) : X=0 := by
  let : Nonempty ι := ⟨i₀⟩
  apply (matrixEquiv ι i₀ M).symm.injective
  rw [map_zero]
  apply MatrixGNS.trace_faithful (ι:=ι) τ hfaith
  change MatrixGNS.trace (ι:=ι) τ ((matrixEquiv ι i₀ M).symm (star X*X))=0 at hX
  rw [equiv_star_mul] at hX
  exact hX

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixTrace_faithful_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixTrace_faithful_oai.{u_1, u_2}
