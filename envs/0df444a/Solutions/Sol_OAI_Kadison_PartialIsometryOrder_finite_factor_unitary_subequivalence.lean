-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:46:05.711647+00:00
-- url     : https://prove2.me/submissions/1831715f-66dd-4dab-a028-71a7bb487e2d

import Mathlib
import Definitions.Def_OAIQ039C059

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}

lemma source_cross_zero (v : Link M e f) (w : Link M e' f')
    (h : v.initial*w.initial=0) : v.val*star w.val=0 := by
  have hw : w.initial*star w.val=star w.val := by
    simpa only [star_mul,w.initial_projection.isSelfAdjoint.star_eq] using congrArg star w.mul_initial
  calc
    _=(v.val*v.initial)*(w.initial*star w.val) := by rw [v.mul_initial,hw]
    _=v.val*(v.initial*w.initial)*star w.val := by noncomm_ring
    _=0 := by rw [h,mul_zero,zero_mul]

lemma target_cross_zero (v : Link M e f) (w : Link M e' f')
    (h : v.final*w.final=0) : star v.val*w.val=0 := by
  have hv : star v.val*v.final=star v.val := by
    simpa only [star_mul,v.final_projection.isSelfAdjoint.star_eq] using congrArg star v.final_mul
  calc
    _=(star v.val*v.final)*(w.final*w.val) := by rw [hv,w.final_mul]
    _=star v.val*(v.final*w.final)*w.val := by noncomm_ring
    _=0 := by rw [h,mul_zero,zero_mul]

end Link

theorem finite_factor_unitary_equivalence (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (e f : M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (heq : τ e=τ f) : ∃ u : unitary M, (u:M)*e*star (u:M)=f := by
  have hep := he.map M.toStarSubalgebra.subtype
  have hfp := hf.map M.toStarSubalgebra.subtype
  have heid : (e:H →L[ℂ] H)*(e:H →L[ℂ] H)=(e:H →L[ℂ] H) := hep.isIdempotentElem.eq
  have hfid : (f:H →L[ℂ] H)*(f:H →L[ℂ] H)=(f:H →L[ℂ] H) := hfp.isIdempotentElem.eq
  obtain ⟨v,hvi,hvf⟩ := finite_factor_equivalence_link M hM τ hτ hfaith
    e.property f.property hep hfp heq
  have hcomp : τ (1-e)=τ (1-f) := by simp only [map_sub,heq]
  obtain ⟨w,hwi,hwf⟩ := finite_factor_equivalence_link M hM τ hτ hfaith
    (1-e).property (1-f).property
    ((he.one_sub).map M.toStarSubalgebra.subtype) ((hf.one_sub).map M.toStarSubalgebra.subtype) hcomp
  have hscross : v.val*star w.val=0 := v.source_cross_zero w (by
    rw [hvi,hwi]
    change (e:H →L[ℂ] H)*(1-(e:H →L[ℂ] H))=0
    rw [mul_sub,mul_one,heid,sub_self])
  have htcross : star v.val*w.val=0 := v.target_cross_zero w (by
    rw [hvf,hwf]
    change (f:H →L[ℂ] H)*(1-(f:H →L[ℂ] H))=0
    rw [mul_sub,mul_one,hfid,sub_self])
  have hscross' : w.val*star v.val=0 := by simpa using congrArg star hscross
  have htcross' : star w.val*v.val=0 := by simpa using congrArg star htcross
  let U : M := ⟨v.val+w.val,M.add_mem v.mem w.mem⟩
  have hU : U∈unitary M := by
    constructor
    · apply Subtype.ext
      change star (v.val+w.val)*(v.val+w.val)=1
      rw [star_add,add_mul,mul_add,mul_add,htcross,htcross',add_zero,zero_add]
      change v.initial+w.initial=1
      rw [hvi,hwi]
      change (e:H →L[ℂ] H)+(1-(e:H →L[ℂ] H))=1
      abel
    · apply Subtype.ext
      change (v.val+w.val)*star (v.val+w.val)=1
      rw [star_add,add_mul,mul_add,mul_add,hscross,hscross',add_zero,zero_add]
      change v.final+w.final=1
      rw [hvf,hwf]
      change (f:H →L[ℂ] H)+(1-(f:H →L[ℂ] H))=1
      abel
  refine ⟨⟨U,hU⟩,?_⟩
  apply Subtype.ext
  change (v.val+w.val)*(e:H →L[ℂ] H)*star (v.val+w.val)=(f:H →L[ℂ] H)
  have hve : v.val*(e:H →L[ℂ] H)=v.val := by simpa only [hvi] using v.mul_initial
  have hwe : w.val*(e:H →L[ℂ] H)=0 := by
    calc
      _=(w.val*w.initial)*(e:H →L[ℂ] H) := by rw [w.mul_initial]
      _=w.val*((1-(e:H →L[ℂ] H))*(e:H →L[ℂ] H)) := by rw [hwi,mul_assoc]; rfl
      _=0 := by rw [sub_mul,one_mul,heid,sub_self,mul_zero]
  rw [add_mul,hve,hwe,add_zero,star_add,mul_add,hscross,add_zero]
  exact hvf

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorCornerTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_factor_unitary_subequivalence_oai (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (e f : M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (hle : τ e≤τ f) : ∃ u : unitary M,(u:M)*e*star (u:M)≤f := by
  obtain ⟨v,hvi⟩ := finite_factor_comparison M hM τ hτ hfaith e.property f.property
    (he.map M.toStarSubalgebra.subtype) (hf.map M.toStarSubalgebra.subtype) hle
  let p : M := ⟨v.final,v.final_mem⟩
  have hp : IsStarProjection p := by
    constructor
    · apply Subtype.ext
      exact v.final_projection.isIdempotentElem.eq
    · apply Subtype.ext
      exact v.final_projection.isSelfAdjoint.star_eq
  have htrace : τ e=τ p := by
    have hi : (⟨v.initial,v.initial_mem⟩:M)=e := Subtype.ext hvi
    exact (congrArg τ hi).symm.trans (v.trace_initial_final τ hτ)
  obtain ⟨u,hu⟩ := finite_factor_unitary_equivalence M hM τ hτ hfaith e p he hp htrace
  exact ⟨u,hu.le.trans v.target_le⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence_oai.{u_1}
