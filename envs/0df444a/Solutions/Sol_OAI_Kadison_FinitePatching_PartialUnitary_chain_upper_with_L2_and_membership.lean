-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:50:07.561544+00:00
-- url     : https://prove2.me/submissions/14dfa59d-0e7d-45ce-8f42-b2c16f79ecbb

import Mathlib
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C046

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma norm_nonneg (a : A) : 0≤norm τ a := _root_.norm_nonneg _

lemma norm_sq (a : A) : norm τ a^2=(τ (star a*a)).re := by
  rw [norm,InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
  rfl

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryOrder
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma star_mul_of_le {v w : PartialUnitary A} (h : v ≤ w) :
    star v.val*w.val=v.support := by
  calc
    _=star (w.val*v.support)*w.val := by rw [h.2]
    _=v.support*w.support := by
      rw [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,mul_assoc,w.star_mul]
    _=v.support := (v.projection.le_iff_mul_eq_left w.projection).mp h.1

lemma star_sub_mul_sub {v w : PartialUnitary A} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support-v.support := by
  have h' : star w.val*v.val=v.support := by
    simpa only [StarMul.star_mul,star_star,v.projection.isSelfAdjoint.star_eq] using
      congrArg star (star_mul_of_le h)
  rw [star_sub,sub_mul,mul_sub,mul_sub,w.star_mul,v.star_mul,star_mul_of_le h,h']
  noncomm_ring

lemma norm_sub_sq (τ : A →ₚ[ℂ] ℂ) {v w : PartialUnitary A} (h : v ≤ w) :
    TracialL2.norm τ (w.val-v.val)^2=(τ w.support).re-(τ v.support).re := by
  rw [TracialL2.norm_sq,star_sub_mul_sub h,map_sub,Complex.sub_re]

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryChain
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter ContinuousLinearMapWOT

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FinitePatching

namespace PartialUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma toLink_initial (v : PartialUnitary M) :
    (toLink M v).initial=(v.support : H →L[ℂ] H) := by
  change (star v.val*v.val : M).val=v.support.val
  exact congrArg Subtype.val v.star_mul

lemma toLink_mono : Monotone (toLink M) := by
  intro v w h
  apply (PartialIsometryOrder.Link.le_def _ _).mpr
  rw [toLink_initial,toLink_initial]
  constructor
  · exact h.1
  · change (w.val*v.support : M).val=v.val.val
    exact congrArg Subtype.val h.2

theorem chain_upper_with_L2_and_membership_oai (τ : M →ₚ[ℂ] ℂ)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (c : Set (PartialUnitary M)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v : PartialUnitary M, (∀ w∈c,w ≤ v) ∧
      (∀ R : VonNeumannAlgebra H, (∀ w∈c,(w.val : H →L[ℂ] H)∈R) →
        (v.val : H →L[ℂ] H)∈R) ∧
      ∃ ω : Ultrafilter c, (ω : Filter c) ≤ atTop ∧
        Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) ∧
        Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)) (ω : Filter c) (𝓝 0) := by
  classical
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c) ≤ atTop := Ultrafilter.of_le _
  let P : c → H →L[ℂ] H := fun w => w.val.support
  obtain ⟨p,hp,hPp,hlim,hLeast⟩ := ProjectionChains.monotone_ultralimit ω hω P
    (fun w => w.val.projection.map M.toStarSubalgebra.subtype)
    (fun _ _ h => h.1)
  have hscalar : ∀ x y, Tendsto (fun w : c => inner ℂ (P w x) y) (ω : Filter c)
      (𝓝 (inner ℂ (p x) y)) := by
    intro x y
    have hh := tendsto_iff_forall_inner_apply_tendsto.mp hlim x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using hh.star
  have hpM : p∈M := WeakOperatorLimit.mem_vonNeumann hscalar M
    (Eventually.of_forall fun w => w.val.support.property)
  let ps : M := ⟨p,hpM⟩
  have hps : IsStarProjection ps := by
    constructor
    · exact Subtype.ext hp.isIdempotentElem.eq
    · exact Subtype.ext hp.isSelfAdjoint.star_eq
  have hcl : IsChain (·≤·) (toLink M '' c) :=
    hc.image_of_map_rel (·≤·) (·≤·) (toLink M) (fun _ _ h => toLink_mono M h)
  obtain ⟨U,hU⟩ := PartialIsometryOrder.chain_has_upper M
    (IsStarProjection.one _) (IsStarProjection.one _) (toLink M '' c) hcl
    (hne.image (toLink M))
  have hUw (w : c) : toLink M w.val ≤ U := hU ⟨w.val,w.property,rfl⟩
  have hUP (w : c) : U.val*P w=(w.val.val : H →L[ℂ] H) := by
    have hh := (PartialIsometryOrder.Link.le_def _ _).mp (hUw w) |>.2
    rw [toLink_initial] at hh
    exact hh
  have hpU : p ≤ U.initial := hLeast U.initial U.initial_projection (fun w => by
    have hh := (PartialIsometryOrder.Link.le_def _ _).mp (hUw w) |>.1
    simpa only [toLink_initial] using hh)
  have htarget (w : c) : U.val*P w*star U.val=P w := by
    have hleft : U.val*star (w.val.val : H →L[ℂ] H)=P w := by
      calc
        _=U.val*((P w)*star (w.val.val : H →L[ℂ] H)) := by
          rw [show P w*star (w.val.val : H →L[ℂ] H)=star (w.val.val : H →L[ℂ] H) from
            congrArg Subtype.val w.val.support_mul_star]
        _=P w := by
          rw [←mul_assoc,hUP]
          exact congrArg Subtype.val w.val.mul_star
    have hright : (w.val.val : H →L[ℂ] H)*star U.val=P w := by
      have hh := congrArg star hleft
      have hpw : star (P w)=P w :=
        (w.val.projection.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
      simpa only [StarMul.star_mul,star_star,hpw] using hh
    rw [hUP,hright]
  have hUpU : U.val*p*star U.val=p := by
    ext x
    apply ext_inner_right ℂ
    intro y
    have hl := hscalar (star U.val x) (star U.val y)
    simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hl
    have he : ∀ᶠ w : c in (ω : Filter c),
        inner ℂ (U.val (P w (star U.val x))) y=inner ℂ (P w x) y :=
      Eventually.of_forall fun w => congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) (htarget w)
    exact tendsto_nhds_unique (hl.congr' he) (hscalar x y)
  let a : M := ⟨U.val*p,M.mul_mem U.mem hpM⟩
  have hpa : star a*a=ps := by
    apply Subtype.ext
    change star (U.val*p)*(U.val*p)=p
    rw [StarMul.star_mul,hp.isSelfAdjoint.star_eq]
    have he := (hp.le_iff_mul_eq_left U.initial_projection).mp hpU
    change p*(star U.val*U.val)=p at he
    calc
      _=(p*(star U.val*U.val))*p := by noncomm_ring
      _=p := by rw [he,hp.isIdempotentElem.eq]
  have hap : a*star a=ps := by
    apply Subtype.ext
    change (U.val*p)*star (U.val*p)=p
    rw [StarMul.star_mul,hp.isSelfAdjoint.star_eq]
    calc
      _=U.val*(p*p)*star U.val := by noncomm_ring
      _=p := by rw [hp.isIdempotentElem.eq,hUpU]
  have haP : a*ps=a := by
    apply Subtype.ext
    change (U.val*p)*p=U.val*p
    rw [mul_assoc,hp.isIdempotentElem.eq]
  have hPa : ps*a=a := by rw [←hap,mul_assoc,hpa,haP]
  let v : PartialUnitary M := ⟨a,ps,hps,hpa,hap,haP,hPa⟩
  have hupper (w : c) : w.val ≤ v := by
    refine ⟨hPp w,?_⟩
    apply Subtype.ext
    change (U.val*p)*P w=(w.val.val : H →L[ℂ] H)
    have hm : p*P w=P w :=
      ((w.val.projection.map M.toStarSubalgebra.subtype).le_iff_mul_eq_right hp).mp (hPp w)
    rw [mul_assoc,hm,hUP]
  have htrace : Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) := by
    exact (Complex.continuous_re.tendsto _).comp
      (NormalGNS.tendsto_trace M τ hnormal (fun w : c => w.val.support) ps 1
        (fun w => w.val.projection.norm_le _) (hps.norm_le _) hscalar)
  have hmember (R : VonNeumannAlgebra H) (hR : ∀ w∈c,(w.val : H →L[ℂ] H)∈R) :
      (v.val : H →L[ℂ] H)∈R := by
    apply WeakOperatorLimit.mem_vonNeumann (l:=(ω : Filter c))
      (T:=fun w : c => (w.val.val : H →L[ℂ] H)) _ R
      (Eventually.of_forall fun w => hR w.val w.property)
    intro x y
    have hl := hscalar x (star U.val y)
    simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hl
    simpa only [←mul_apply_eq_comp,hUP] using hl
  refine ⟨v,fun w hw => hupper ⟨w,hw⟩,hmember,ω,hω,htrace,?_⟩
  have hs : Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)^2)
      (ω : Filter c) (𝓝 0) := by
    have hh := (tendsto_const_nhds (x:=(τ v.support).re)).sub htrace
    simp only [sub_self] at hh
    exact hh.congr' (Eventually.of_forall fun w => (norm_sub_sq τ (hupper w)).symm)
  have hh := hs.sqrt
  simpa only [Real.sqrt_sq (TracialL2.norm_nonneg τ _),Real.sqrt_zero] using hh

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership_oai.{u_1} := @OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership_oai.{u_1}
