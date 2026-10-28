-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.projection_rep_lift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:51:48.350922+00:00
-- url     : https://prove2.me/submissions/4e0b1ce7-a6e5-4442-92e4-1e46bc633b82

import Mathlib
import Definitions.Def_OAIQ039C048
import Definitions.Def_OAIQ039C064

section
-- module Solutions.OAIQ039_CM.Commutator_BoundedPositiveSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BoundedContinuousFunction

namespace Kadison.BoundedPositiveSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

theorem squareRoot (d : ι →ᵇ A) (hd : ∀ i, 0≤d i) :
    ∃ z : ι →ᵇ A, d=star z*z := by
  let z : ι →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => CFC.sqrt (d i)) (Real.sqrt ‖d‖) (fun i => by
      rw [CFC.norm_sqrt _ (hd i)]
      exact Real.sqrt_le_sqrt (d.norm_coe_le_norm i))
  refine ⟨z,?_⟩
  apply BoundedContinuousFunction.ext
  intro i
  change d i=star (CFC.sqrt (d i))*CFC.sqrt (d i)
  rw [(CFC.sqrt_nonneg (d i)).star_eq,CFC.sqrt_mul_sqrt_self _ (hd i)]

lemma map_nonneg {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : (ι →ᵇ A) →⋆ₐ[ℂ] B) (d : ι →ᵇ A) (hd : ∀ i, 0≤d i) : 0≤φ d := by
  obtain ⟨z,rfl⟩ := squareRoot d hd
  simpa only [map_mul,map_star] using star_mul_self_nonneg (φ z)

end Kadison.BoundedPositiveSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CStarContractiveLifts
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped CStarAlgebra

namespace Kadison.CStarContractiveLifts

lemma radial_continuous : Continuous radial := by
  unfold radial
  exact (continuous_const.max continuous_abs).sqrt.inv₀ (fun t =>
    ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|))))

lemma radial_eq_one {t : ℝ} (ht : |t|≤1) : radial t=1 := by
  simp only [radial,max_eq_left ht,Real.sqrt_one,inv_one]

lemma radial_square (t : ℝ) : radial t*radial t=(max 1 |t|)⁻¹ := by
  rw [radial,←mul_inv,←pow_two,Real.sq_sqrt (zero_le_one.trans (le_max_left 1 |t|))]

lemma radial_bound (t : ℝ) : ‖radial t * t * radial t‖≤1 := by
  have hd : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left 1 |t|)
  rw [show radial t*t*radial t=t*(radial t*radial t) by ring,radial_square,
    Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos hd,←div_eq_mul_inv]
  exact (div_le_one hd).mpr (le_max_right 1 |t|)

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma clip_norm_le (a : A) : ‖clip a‖≤1 := by
  have hs : IsSelfAdjoint (star a*a) := IsSelfAdjoint.star_mul_self a
  have hk : IsSelfAdjoint (cfc radial (star a*a)) := cfc_predicate _ _
  have he : star (clip a)*clip a=cfc (fun t : ℝ => radial t*t*radial t) (star a*a) := by
    rw [clip,star_mul,hk.star_eq]
    calc
      _=cfc radial (star a*a)*(star a*a)*cfc radial (star a*a) := by noncomm_ring
      _=cfc radial (star a*a)*cfc (fun t : ℝ => t) (star a*a)*cfc radial (star a*a) := by
        rw [cfc_id' ℝ _ hs]
      _=_ := by
        rw [←cfc_mul radial (fun t : ℝ => t) _ radial_continuous.continuousOn continuous_id.continuousOn,
          ←cfc_mul (fun t : ℝ => radial t*t) radial _
            (radial_continuous.mul continuous_id).continuousOn radial_continuous.continuousOn]
  have hn : ‖star (clip a)*clip a‖≤1 := by
    rw [he]
    exact norm_cfc_le zero_le_one (fun t _ => radial_bound t)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (clip a)]

lemma clip_fix {a : A} (ha : ‖a‖≤1) : clip a=a := by
  nontriviality A
  have hn : ‖star a*a‖≤1 := by rw [CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg a]
  have he : cfc radial (star a*a)=1 := by
    rw [cfc_congr (g := fun _ : ℝ => 1) (fun t ht =>
      radial_eq_one ((show |t|≤‖star a*a‖ from spectrum.norm_le_norm_of_mem ht).trans hn)),
      cfc_const_one ℝ _ (IsSelfAdjoint.star_mul_self a)]
  rw [clip,he,mul_one]

lemma map_clip (φ : A →⋆ₐ[ℂ] B) (a : A) : φ (clip a)=clip (φ a) := by
  rw [clip,map_mul,φ.map_cfc radial (star a*a) radial_continuous.continuousOn
    (by fun_prop) (IsSelfAdjoint.star_mul_self a)
    ((IsSelfAdjoint.star_mul_self a).map φ),map_mul,map_star]
  rfl

theorem contraction (φ : A →⋆ₐ[ℂ] B) {b : B} (hb : ‖b‖≤1)
    (hr : b∈Set.range φ) : ∃ a : A, ‖a‖≤1 ∧ φ a=b := by
  obtain ⟨a,rfl⟩ := hr
  exact ⟨clip a,clip_norm_le a,by rw [map_clip,clip_fix hb]⟩

end Kadison.CStarContractiveLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralCutoff
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma halfCut_rounding {T : H →L[ℂ] H} (hT : 0≤T) (hT1 : T≤1) :
    star (halfCut T-T)*(halfCut T-T)≤T-T*T := by
  let b := T+T-(1 : H →L[ℂ] H)
  let q := halfCut T
  have hb : IsSelfAdjoint b := ((IsSelfAdjoint.of_nonneg hT).add (IsSelfAdjoint.of_nonneg hT)).sub (IsSelfAdjoint.one _)
  have hc : Commute b T := ((Commute.refl T).add_left (Commute.refl T)).sub_left (Commute.one_left T)
  have hp : Commute b⁺ T := hc.cfcₙ_real (·⁺)
  have hn : Commute b⁻ T := hc.cfcₙ_real (·⁻)
  have hpos : 0≤(1-T)*b⁺+T*b⁻ := add_nonneg
    (Commute.mul_nonneg (sub_nonneg.mpr hT1) (CFC.posPart_nonneg b)
      ((Commute.one_left b⁺).sub_left hp.symm))
    (Commute.mul_nonneg hT (CFC.negPart_nonneg b) hn.symm)
  have hqb : q*b=b⁺ := halfCut_mul_shift (IsSelfAdjoint.of_nonneg hT)
  have hq : q*q=q := (isProjection_halfCut T).isIdempotentElem.eq
  have hcq : q*T=T*q := (halfCut_commute (IsSelfAdjoint.of_nonneg hT)).eq
  have hnb : b⁻=q*b-b := by
    rw [hqb]
    calc
      b⁻=b⁺-(b⁺-b⁻) := by abel
      _=b⁺-b := by rw [CFC.posPart_sub_negPart b hb]
  have he : T-T*T-(q-T)*(q-T)=(1-T)*b⁺+T*b⁻ := by
    rw [hnb,←hqb]
    dsimp only [b]
    noncomm_ring [hq,hcq]
  rw [star_sub,(isProjection_halfCut T).isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg hT).star_eq]
  exact sub_nonneg.mp (he.symm ▸ hpos)

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionLifts
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BoundedContinuousFunction ComplexOrder

namespace Kadison.ProjectionLifts

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma rounding (a : M) (h0 : 0≤a) (h1 : a≤1) :
    star (halfCut M a-a)*(halfCut M a-a)≤a-a*a :=
  Polar.halfCut_rounding h0 h1

variable {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem projection_lift (φ : (ι →ᵇ M) →⋆ₐ[ℂ] B) {p : B} (hp : IsStarProjection p)
    (hr : p∈Set.range φ) : ∃ q : ι →ᵇ M, (∀ i, IsStarProjection (q i)) ∧ φ q=p := by
  obtain ⟨b,hb,hbp⟩ := CStarContractiveLifts.contraction φ (hp.norm_le p) hr
  let c : ι →ᵇ M := star b*b
  have hc (i : ι) : 0 ≤ c i := star_mul_self_nonneg (b i)
  have hc1 (i : ι) : c i≤1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hc i)).mp
    change ‖star (b i)*b i‖≤1
    rw [CStarRing.norm_star_mul_self]
    have hbi : ‖b i‖≤1 := (b.norm_coe_le_norm i).trans hb
    nlinarith [norm_nonneg (b i)]
  have hcp : φ c=p := by
    dsimp only [c]
    rw [map_mul,map_star,hbp,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  let q := roundedSequence M c
  let d := c-c*c-star (q-c)*(q-c)
  have hd (i : ι) : 0≤d i := by
    change 0 ≤ c i-c i*c i-star (halfCut M (c i)-c i)*(halfCut M (c i)-c i)
    exact sub_nonneg.mpr (rounding M (c i) (hc i) (hc1 i))
  have hφd := BoundedPositiveSequence.map_nonneg φ d hd
  have hneg : star (φ q-p)*(φ q-p)≤0 := by
    dsimp only [d] at hφd
    simpa only [map_sub,map_mul,map_star,hcp,hp.isIdempotentElem.eq,sub_self,
      zero_sub,neg_nonneg] using hφd
  have he : φ q-p=0 := (CStarRing.star_mul_self_eq_zero_iff _).mp
    (le_antisymm hneg (star_mul_self_nonneg _))
  exact ⟨q,fun i => isProjection_halfCut M (c i),sub_eq_zero.mp he⟩

end Kadison.ProjectionLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSmallCorners
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma projection_operator_lift {G K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : VonNeumannAlgebra G) (φ : (ℕ →ᵇ N) →⋆ₐ[ℂ] (K →L[ℂ] K))
    {e : K →L[ℂ] K} (he : IsStarProjection e) (her : e∈Set.range φ) :
    ∃ q : ℕ →ᵇ N, (∀ i, IsStarProjection (q i)) ∧ φ q=e :=
  ProjectionLifts.projection_lift (ι:=ℕ) (B:=(K →L[ℂ] K)) N φ he her

lemma projection_rep_lift_oai {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    {e : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f))) :
    ∃ q : ℕ →ᵇ N, (∀ i, IsStarProjection (q i)) ∧ leftRestricted τ ω (mapSequence f q)=e :=
  projection_operator_lift N
    ((leftRestricted τ ω).comp (mapSequence f)) he her

end Kadison.TracialSequence

end

end OAI
end

theorem solution.{u_1, u_3} : type_of% @OAI.Kadison.TracialSequence.projection_rep_lift_oai.{u_1, u_3} := @OAI.Kadison.TracialSequence.projection_rep_lift_oai.{u_1, u_3}
