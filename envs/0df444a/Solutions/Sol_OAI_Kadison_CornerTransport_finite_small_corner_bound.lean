-- Prove2me | solution 1 for OAI.Kadison.CornerTransport.finite_small_corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:48:19.860011+00:00
-- url     : https://prove2.me/submissions/d6c83e8e-f6b4-428c-b5c6-92a2c47a036c

import Mathlib
import Definitions.Def_OAIQ039C054
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_finite_factor_unitary_subequivalence

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorCornerTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

namespace Kadison.CornerTransport

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma conjugate_corner (e f : A) (he : IsStarProjection e) (hf : IsStarProjection f)
    (u : unitary A) (hle : (u:A)*f*star (u:A)≤e) (z : A) (hz : f*z*f=z) :
    e*((u:A)*z*star (u:A))*e=(u:A)*z*star (u:A) := by
  have hu : star (u:A)*(u:A)=1 := u.property.1
  have hp : IsStarProjection ((u:A)*f*star (u:A)) := by
    constructor
    · calc
        _=(u:A)*f*(star (u:A)*(u:A))*f*star (u:A) := by noncomm_ring
        _=(u:A)*f*star (u:A) := by rw [hu,mul_one,mul_assoc (u:A) f f,hf.isIdempotentElem.eq]
    · change star ((u:A)*f*star (u:A))=(u:A)*f*star (u:A)
      simp only [star_mul,star_star,hf.isSelfAdjoint.star_eq,mul_assoc]
  have hleft := (hp.le_iff_mul_eq_right he).mp hle
  have hef : e*(u:A)*f=(u:A)*f := by
    have h := congrArg (fun x : A => x*(u:A)) hleft
    simpa only [mul_assoc,hu,mul_one] using h
  have hfue : f*star (u:A)*e=f*star (u:A) := by
    simpa only [star_mul,he.isSelfAdjoint.star_eq,hf.isSelfAdjoint.star_eq,mul_assoc] using congrArg star hef
  calc
    _=e*((u:A)*(f*z*f)*star (u:A))*e := by rw [hz]
    _=(e*(u:A)*f)*z*(f*star (u:A)*e) := by noncomm_ring
    _=((u:A)*f)*z*(f*star (u:A)) := by rw [hef,hfue]
    _=(u:A)*(f*z*f)*star (u:A) := by noncomm_ring
    _=(u:A)*z*star (u:A) := by rw [hz]

omit [PartialOrder A] [StarOrderedRing A] in
lemma bound_under_unitary (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (u : unitary A) (hTu : T*ρ (u:A)=ρ (u:A)*T)
    (hTu' : T*ρ (star (u:A))=ρ (star (u:A))*T) (z : A) {c : ℝ}
    (h : ‖T*ρ ((u:A)*z*star (u:A))-ρ ((u:A)*z*star (u:A))*T‖ ≤ c*‖(u:A)*z*star (u:A)‖) :
    ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖ := by
  have he : T*ρ ((u:A)*z*star (u:A))-ρ ((u:A)*z*star (u:A))*T=
      ρ (u:A)*(T*ρ z-ρ z*T)*ρ (star (u:A)) := by
    simp only [map_mul]
    calc
      _=(T*ρ (u:A))*ρ z*ρ (star (u:A))-ρ (u:A)*ρ z*(ρ (star (u:A))*T) := by noncomm_ring
      _=(ρ (u:A)*T)*ρ z*ρ (star (u:A))-ρ (u:A)*ρ z*(T*ρ (star (u:A))) := by rw [hTu,←hTu']
      _=_ := by noncomm_ring
  have hU := Unitary.map_mem ρ u.property
  have hU' := Unitary.map_mem ρ (Unitary.star_mem u.property)
  rw [he,CStarRing.norm_mul_mem_unitary _ hU',CStarRing.norm_mem_unitary_mul _ hU,
    CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem u.property),CStarRing.norm_mem_unitary_mul _ u.property] at h
  exact h

end Kadison.CornerTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSmallCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

namespace Kadison.CornerTransport

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finite_small_corner_bound_oai (Q : VonNeumannAlgebra H) (hQ : FactorCorner.IsFactor Q)
    (σ : Q →ₚ[ℂ] ℂ) (hσ : ∀ a b : Q,σ (a*b)=σ (b*a))
    (hfaith : ∀ a : Q,σ (star a*a)=0 → a=0)
    (j : Q →⋆ₐ[ℂ] A) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (T : K →L[ℂ] K) (hT : ∀ q : Q,T*ρ (j q)=ρ (j q)*T)
    (e : Q) (he : IsStarProjection e) {c : ℝ}
    (hbound : ∀ z : A,j e*z*j e=z → ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖)
    (f : Q) (hf : IsStarProjection f) (htrace : σ f≤σ e)
    (z : A) (hz : j f*z*j f=z) : ‖T*ρ z-ρ z*T‖ ≤ c*‖z‖ := by
  obtain ⟨u,hu⟩ := PartialIsometryOrder.finite_factor_unitary_subequivalence Q hQ σ hσ hfaith f e hf he htrace
  let v : unitary A := ⟨j (u:Q),Unitary.map_mem j u.property⟩
  have hv : (v:A)*j f*star (v:A)≤j e := by
    change j (u:Q)*j f*star (j (u:Q))≤j e
    rw [←map_star,←map_mul,←map_mul]
    exact OrderHomClass.monotone j hu
  have hcorner := conjugate_corner (j e) (j f) (he.map j) (hf.map j) v hv z hz
  apply bound_under_unitary ρ T v (hT (u:Q)) ?_ z (hbound _ hcorner)
  change T*ρ (star (j (u:Q)))=ρ (star (j (u:Q)))*T
  rw [←map_star]
  exact hT (star (u:Q))

end Kadison.CornerTransport

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.CornerTransport.finite_small_corner_bound_oai := @OAI.Kadison.CornerTransport.finite_small_corner_bound_oai
