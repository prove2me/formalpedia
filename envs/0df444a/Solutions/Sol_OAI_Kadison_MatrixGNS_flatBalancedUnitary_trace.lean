-- Prove2me | solution 1 for OAI.Kadison.MatrixGNS.flatBalancedUnitary_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:38:39.541987+00:00
-- url     : https://prove2.me/submissions/2b192b70-d744-422b-9454-600db83ea9b6

import Mathlib
import Definitions.Def_OAIQ039C061
import Theorems.Thm_OAI_Kadison_MatrixGNS_trace_mul

section
-- module Solutions.OAIQ039_CM.Commutator_CFCTraceMoments
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder ContinuousFunctionalCalculus

namespace Kadison.CFCTraceMoments

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance instContinuousFunctionalCalculusComplexProdIsStarNormal_solutions : ContinuousFunctionalCalculus ℂ (A × A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance instContinuousFunctionalCalculusRealProdIsSelfAdjoint_solutions : ContinuousFunctionalCalculus ℝ (A × A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

lemma trace_cfc_of_powers (τ : A →ₚ[ℂ] ℂ) (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hpow : ∀ n : ℕ,τ (a^n)=τ (b^n)) (f : ℝ → ℝ) (hf : Continuous f) :
    τ (cfc f a)=τ (cfc f b) := by
  have hab : IsSelfAdjoint (a,b) := Prod.ext ha hb
  have hpoly (p : Polynomial ℝ) : τ (Polynomial.aeval a p)=τ (Polynomial.aeval b p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial n r =>
      simp only [Polynomial.aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
      change τ.toLinearMap (r • a^n)=τ.toLinearMap (r • b^n)
      rw [LinearMap.map_smul_of_tower,LinearMap.map_smul_of_tower]
      exact congrArg (fun z : ℂ => r • z) (hpow n)
  let S : Set C(spectrum ℝ (a,b),ℝ) :=
    {g | τ (cfcHom hab g).1=τ (cfcHom hab g).2}
  have hS : IsClosed S := isClosed_eq
    ((map_continuous τ).comp (cfcHom_continuous hab).fst)
    ((map_continuous τ).comp (cfcHom_continuous hab).snd)
  have hsub : (polynomialFunctions (spectrum ℝ (a,b)) : Set C(spectrum ℝ (a,b),ℝ))⊆S := by
    rw [polynomialFunctions_coe]
    rintro g ⟨p,rfl⟩
    change τ (cfcHom hab (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ (a,b)) p)).1=
      τ (cfcHom hab (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ (a,b)) p)).2
    have he : cfcHom hab (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ (a,b)) p)=
        Polynomial.aeval (a,b) p := by
      rw [← cfc_polynomial p (a,b) hab,cfc_apply p.eval (a,b) hab p.continuous.continuousOn]
      rfl
    rw [he,Polynomial.aeval_prod_apply]
    exact hpoly p
  have hd : closure (polynomialFunctions (spectrum ℝ (a,b)) : Set C(spectrum ℝ (a,b),ℝ))=Set.univ := by
    rw [←Subalgebra.topologicalClosure_coe,polynomialFunctions.topologicalClosure]
    rfl
  have all : ∀ g : C(spectrum ℝ (a,b),ℝ),g∈S :=
    fun g => closure_minimal hsub hS (hd.symm ▸ Set.mem_univ g)
  have hm : τ (cfc f (a,b)).1=τ (cfc f (a,b)).2 := by
    rw [cfc_apply f (a,b) hab hf.continuousOn]
    exact all _
  rw [cfc_map_prod (S := ℂ) f a b hf.continuousOn hab ha hb] at hm
  exact hm

omit [StarOrderedRing A] in
lemma trace_cyclic_powers (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (a b : A) (n : ℕ) : τ ((a*b)^n)=τ ((b*a)^n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h : SemiconjBy a (b*a) (a*b) := (mul_assoc a b a).symm
    have hn := h.pow_right n
    change a*(b*a)^n=(a*b)^n*a at hn
    calc
      τ ((a*b)^(n+1))=τ (((a*b)^n*a)*b) := by rw [pow_succ,mul_assoc]
      _=τ ((a*(b*a)^n)*b) := by rw [hn]
      _=τ ((b*a)^n*(b*a)) := by rw [mul_assoc,hτ a ((b*a)^n*b),mul_assoc]
      _=τ ((b*a)^(n+1)) := by rw [pow_succ]

end Kadison.CFCTraceMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BalancedDefect
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.BalancedDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma sqrt_sub_one_cfc (a : A) (ha : IsSelfAdjoint a) (hpos : 0≤1-a) :
    CFC.sqrt (1-a)=cfc (fun r : ℝ => Real.sqrt (1-r)) a := by
  have he : cfc (fun r : ℝ => 1-r) a=1-a := by
    simpa only [cfc_const (1 : ℝ) a ha,map_one,cfc_id' ℝ a ha] using
      cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => r) a
  rw [sqrt_eq_real_cfc _ hpos,←he,←cfc_comp Real.sqrt (fun r : ℝ => 1-r) a]
  rfl

lemma defect_trace (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (x : A) (hx : ‖x‖≤1) : τ (CFC.sqrt (1-x*star x))=τ (CFC.sqrt (1-star x*x)) := by
  have h₁ := defect_nonneg x hx
  have h₂ : 0≤1-star x*x := by simpa only [star_star] using defect_nonneg (star x) (by simpa using hx)
  rw [sqrt_sub_one_cfc _ (by cfc_tac) h₁,sqrt_sub_one_cfc _ (by cfc_tac) h₂]
  apply CFCTraceMoments.trace_cfc_of_powers τ (x*star x) (star x*x)
    (by cfc_tac) (by cfc_tac)
    (fun n => CFCTraceMoments.trace_cyclic_powers τ hτ x (star x) n)
  fun_prop

end Kadison.BalancedDilation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BalancedSymmetry
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix

namespace Kadison.BalancedDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma symmetry_diagonal_trace (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (x : A) (hx : ‖x‖≤1) :
    ∑ i : Fin 2,τ (symmetry x i i)=0 := by
  simp [Fin.sum_univ_two,symmetry,defect_trace τ hτ x hx]

end Kadison.BalancedDilation

end

end
end

end OAI
end

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

end Kadison.MatrixGNS

end

end
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
lemma balanced_symmetry_trace_zero
    (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (x : A) (hx : ‖x‖≤1) :
    trace (ι:=Fin 2) τ (BalancedDilation.symmetry x)=0 := by
  rw [trace_apply]
  rw [BalancedDilation.symmetry_diagonal_trace τ hτ x hx,mul_zero]

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlatten
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance instDecidableEq_solutions_1_rb35be8_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEq_solutions_2
attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEqProd_solutions
lemma trace_flatten (τ : A →ₚ[ℂ] ℂ) (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    trace (ι:=κ×ι) τ (flatten ι κ X)=trace (ι:=κ) (trace (ι:=ι) τ) X := by
  simp only [trace_apply,flatten_apply,Fintype.sum_prod_type,Fintype.card_prod,
    Nat.cast_mul,mul_inv_rev]
  rw [←Finset.mul_sum]
  ring

lemma flatBalancedUnitary_trace_oai (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    trace (ι:=(Fin 2)×ι) τ (flatBalancedUnitary ι X hX:
      CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)=0 := by
  change trace (ι:=(Fin 2)×ι) τ (flatten ι (Fin 2) (BalancedDilation.symmetry X))=0
  rw [trace_flatten]
  exact balanced_symmetry_trace_zero (trace (ι:=ι) τ) (trace_mul τ hτ) X hX

end Kadison.MatrixGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixGNS.flatBalancedUnitary_trace_oai.{u_1, u_2} := @OAI.Kadison.MatrixGNS.flatBalancedUnitary_trace_oai.{u_1, u_2}
