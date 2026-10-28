-- Prove2me | solution 1 for OAI.Kadison.NormalGNS.commutant_range_eq_of_commutative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:26:52.034788+00:00
-- url     : https://prove2.me/submissions/8e6f0560-5560-480e-9fb7-5dc7c570b606

import Mathlib
import Definitions.Def_OAIQ039C042
import Definitions.Def_OAIQ039C058

section
-- module Solutions.OAIQ039_CM.Commutator_TracialCommutation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma starMap_norm (x : τ.GNS) : ‖starMap τ hτ x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a =>
    change ‖starMap τ hτ (algebraVector τ (τ.ofPreGNS a))‖ = ‖(a : τ.GNS)‖
    rw [starMap_algebra]
    simp only [algebraVector_apply, Completion.norm_coe, norm_star_preGNS τ hτ,
      PositiveLinearMap.toPreGNS_ofPreGNS]

lemma starMap_involutive : Function.Involutive (starMap τ hτ) := by
  intro x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a =>
    change starMap τ hτ (starMap τ hτ (algebraVector τ (τ.ofPreGNS a))) = _
    rw [starMap_algebra, starMap_algebra, star_star]
    rfl

lemma starMap_inner (x y : τ.GNS) :
    inner ℂ (starMap τ hτ x) (starMap τ hτ y) = inner ℂ y x := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a b =>
    change inner ℂ (starMap τ hτ (algebraVector τ (τ.ofPreGNS a)))
      (starMap τ hτ (algebraVector τ (τ.ofPreGNS b))) = _
    rw [starMap_algebra, starMap_algebra, inner_algebraVector, star_star, hτ]
    simp only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] lemma starMap_starMap (x : τ.GNS) : starMap τ hτ (starMap τ hτ x)=x :=
  starMap_involutive τ hτ x

lemma operatorConjugate_involutive : Function.Involutive (operatorConjugate τ hτ) := by
  intro T
  ext x
  simp only [operatorConjugate_apply,starMap_starMap]

lemma commutant_star {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    star T∈Set.centralizer (Set.range τ.gnsStarAlgHom) := by
  rintro _ ⟨a,rfl⟩
  have h := congrArg star (hT _ ⟨star a,rfl⟩)
  simpa only [star_mul,map_star,star_star] using h.symm

lemma starMap_commutant_vacuum {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    starMap τ hτ (T (vacuum τ))=star T (vacuum τ) := by
  apply (algebraVector_dense τ).eq_of_inner_right ℂ
  intro a
  have hc : τ.gnsStarAlgHom a (T (vacuum τ))=T (algebraVector τ a) := by
    have he := congrArg (fun V : τ.GNS →L[ℂ] τ.GNS => V (vacuum τ)) (hT _ ⟨a,rfl⟩)
    simpa only [mul_apply_eq_comp,left_vacuum,algebraVector_apply] using he
  calc
    _ = inner ℂ (T (vacuum τ)) (starMap τ hτ (algebraVector τ a)) := by
      simpa only [starMap_starMap] using
        (starMap_inner τ hτ (starMap τ hτ (algebraVector τ a)) (T (vacuum τ)))
    _ = inner ℂ (T (vacuum τ)) (τ.gnsStarAlgHom (star a) (vacuum τ)) := by
      rw [starMap_algebra,left_vacuum]; rfl
    _ = inner ℂ (τ.gnsStarAlgHom a (T (vacuum τ))) (vacuum τ) := by
      rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (T (algebraVector τ a)) (vacuum τ) := by rw [hc]
    _ = inner ℂ (algebraVector τ a) (star T (vacuum τ)) := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

lemma operatorConjugate_commutant_orbit {T R : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom))
    (hR : R∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    operatorConjugate τ hτ T (R (vacuum τ))=R (star T (vacuum τ)) := by
  rw [operatorConjugate_apply,starMap_commutant_vacuum τ hτ hR]
  change starMap τ hτ ((T*star R) (vacuum τ))=_
  rw [starMap_commutant_vacuum τ hτ (Set.mul_mem_centralizer hT (commutant_star τ hR)),star_mul,star_star]
  rfl

theorem operatorConjugate_commutant_mem_bicommutant {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    operatorConjugate τ hτ T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) := by
  intro R hR
  apply ContinuousLinearMap.ext
  have he : ∀ a : A, (R*operatorConjugate τ hτ T) (algebraVector τ a)=
      (operatorConjugate τ hτ T*R) (algebraVector τ a) := by
    intro a
    rw [←show rightMul τ hτ a (vacuum τ)=algebraVector τ a from right_vacuum τ hτ a]
    have ha := rightMul_mem_commutant τ hτ a
    change R (operatorConjugate τ hτ T (rightMul τ hτ a (vacuum τ)))=
      operatorConjugate τ hτ T ((R*rightMul τ hτ a) (vacuum τ))
    rw [operatorConjugate_commutant_orbit τ hτ hT ha,
      operatorConjugate_commutant_orbit τ hτ hT (Set.mul_mem_centralizer hR ha)]
    rfl
  exact fun x => congrFun ((algebraVector_dense τ).equalizer
    (R*operatorConjugate τ hτ T).continuous (operatorConjugate τ hτ T*R).continuous (funext he)) x

end Kadison.TracialGNS

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialRightClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

noncomputable section

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma operatorConjugate_norm_le (T : τ.GNS →L[ℂ] τ.GNS) :
    ‖operatorConjugate τ hτ T‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [operatorConjugate_apply,starMap_norm]
  exact (T.le_opNorm _).trans_eq (by rw [starMap_norm])

lemma operatorConjugate_norm (T : τ.GNS →L[ℂ] τ.GNS) :
    ‖operatorConjugate τ hτ T‖=‖T‖ := by
  apply le_antisymm (operatorConjugate_norm_le τ hτ T)
  have h := operatorConjugate_norm_le τ hτ (operatorConjugate τ hτ T)
  rw [operatorConjugate_involutive τ hτ T] at h
  exact h

lemma operatorConjugate_left (a : A) :
    operatorConjugate τ hτ (τ.gnsStarAlgHom a)=rightMul τ hτ (star a) := by
  apply ContinuousLinearMap.ext
  have he : ∀ b : A, operatorConjugate τ hτ (τ.gnsStarAlgHom a) (algebraVector τ b)=
      rightMul τ hτ (star a) (algebraVector τ b) := by
    intro b
    rw [operatorConjugate_apply,starMap_algebra]
    change starMap τ hτ (τ.gnsStarAlgHom a (τ.toPreGNS (star b) : τ.GNS))=_
    rw [left_coe]
    change starMap τ hτ (algebraVector τ (a*star b))=rightMul τ hτ (star a) (τ.toPreGNS b : τ.GNS)
    rw [starMap_algebra,rightMul_coe]
    simp only [star_mul,star_star,PositiveLinearMap.ofPreGNS_toPreGNS,algebraVector_apply]
  exact fun x => congrFun ((algebraVector_dense τ).equalizer
    (operatorConjugate τ hτ (τ.gnsStarAlgHom a)).continuous
    (rightMul τ hτ (star a)).continuous (funext he)) x

lemma bicommutant_star {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))) :
    star T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) := by
  intro R hR
  have h := congrArg star (hT _ (commutant_star τ hR))
  simpa only [star_mul,star_star] using h.symm

lemma rightOperator_original (a : A) :
    rightOperator τ hτ (τ.gnsStarAlgHom a)=rightMul τ hτ a := by
  rw [rightOperator,←map_star,operatorConjugate_left,star_star]

theorem commutation {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    ∃ b : τ.GNS →L[ℂ] τ.GNS,
      b∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) ∧
      T=rightOperator τ hτ b ∧ ‖b‖=‖T‖ := by
  refine ⟨star (operatorConjugate τ hτ T),
    bicommutant_star τ (operatorConjugate_commutant_mem_bicommutant τ hτ hT),?_,?_⟩
  · simp only [rightOperator,star_star]
    exact (operatorConjugate_involutive τ hτ T).symm
  · change ‖ContinuousLinearMap.adjoint (operatorConjugate τ hτ T)‖=‖T‖
    rw [ContinuousLinearMap.adjoint.norm_map,operatorConjugate_norm]

end Kadison.TracialGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AbelianGNSMaximal
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

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma rightMul_eq_left_of_commutative (hc : ∀ a b : M,a*b=b*a)
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (a : M) :
    rightMul τ hτ a=τ.gnsStarAlgHom a := by
  ext x
  refine (algebraVector_dense τ).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [algebraVector_apply,rightMul_coe,PositiveLinearMap.ofPreGNS_toPreGNS,left_coe,hc b a]

theorem commutant_range_eq_of_commutative_oai (hc : ∀ a b : M,a*b=b*a)
    (hn : BoundedWOTContinuous M τ) :
    Set.centralizer (Set.range τ.gnsStarAlgHom)=Set.range τ.gnsStarAlgHom := by
  have ht : ∀ a b : M,τ (a*b)=τ (b*a) := fun a b => congrArg τ (hc a b)
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨b,hb,hTb,_⟩ := TracialGNS.commutation τ ht hT
    rw [range_bicommutant M τ ht hn] at hb
    obtain ⟨a,rfl⟩ := hb
    refine ⟨a,?_⟩
    rw [rightOperator_original] at hTb
    exact (hTb.trans (rightMul_eq_left_of_commutative M τ hc ht a)).symm
  · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact (map_mul τ.gnsStarAlgHom b a).symm.trans
      ((congrArg τ.gnsStarAlgHom (hc b a)).trans (map_mul τ.gnsStarAlgHom a b))

end Kadison.NormalGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.NormalGNS.commutant_range_eq_of_commutative_oai.{u_1} := @OAI.Kadison.NormalGNS.commutant_range_eq_of_commutative_oai.{u_1}
