-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:39:48.878975+00:00
-- url     : https://prove2.me/submissions/9786a434-923d-482c-86e7-3e62e421b17a

import Mathlib
import Definitions.Def_OAIQ039C061

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVectorTrace
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

open ContinuousLinearMap

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

attribute [local instance] OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq
variable (τ : A →ₚ[ℂ] ℂ)

lemma diagonal_inner (X : CStarMatrix ι ι A) :
    inner ℂ (algebraArray τ (1:CStarMatrix ι ι A)) (algebraArray τ X)=∑ i,τ (X i i) := by
  simp only [PiLp.inner_apply,algebraArray_apply,TracialGNS.inner_algebraVector,CStarMatrix.one_apply]
  simp [apply_ite]

lemma trace_apply (X : CStarMatrix ι ι A) :
    trace (ι:=ι) τ X=(Fintype.card ι : ℂ)⁻¹ * ∑ i,τ (X i i) := by
  rw [trace_vector,representation_vacuum,vacuum,inner_smul_left,inner_smul_right,diagonal_inner]
  have hs : starRingEnd ℂ (scale ι)*scale ι=(Fintype.card ι : ℂ)⁻¹ := by
    change star (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ)=_
    rw [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,←mul_inv_rev,
      Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [←mul_assoc,hs]

lemma trace_mul_oai (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (X Y : CStarMatrix ι ι A) :
    trace (ι:=ι) τ (X*Y)=trace (ι:=ι) τ (Y*X) := by
  simp only [trace_apply,CStarMatrix.mul_apply,map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hτ _ _

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixGNS.trace_mul_oai.{u_1, u_2} := @OAI.Kadison.MatrixGNS.trace_mul_oai.{u_1, u_2}
