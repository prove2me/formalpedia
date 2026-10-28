-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.bicommutant_norm_lift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:49:12.952191+00:00
-- url     : https://prove2.me/submissions/7b4c5252-47fb-403a-81a5-05694991a2d3

import Mathlib
import Definitions.Def_OAIQ039C069

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

theorem norm_lift (φ : A →⋆ₐ[ℂ] B) {b : B} (hr : b∈Set.range φ) :
    ∃ a : A, ‖a‖≤‖b‖ ∧ φ a=b := by
  by_cases hb : b=0
  · exact ⟨0,by simp [hb],by simp [hb]⟩
  have hn : ‖b‖≠0 := norm_ne_zero_iff.mpr hb
  obtain ⟨y,hy⟩ := hr
  let z : ℂ := (‖b‖⁻¹:ℝ)
  have hz : ‖z • b‖≤1 := by
    rw [norm_smul,show ‖z‖=‖b‖⁻¹ by simp [z],
      inv_mul_cancel₀ hn]
  obtain ⟨x,hx,hex⟩ := contraction φ hz ⟨z • y,by rw [map_smul,hy]⟩
  refine ⟨(‖b‖:ℂ) • x,?_,?_⟩
  · rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg b)]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg b)).trans_eq (mul_one _)
  · rw [map_smul,hex,smul_smul]
    have he : (‖b‖:ℂ)*z=1 := by
      simp only [z,←Complex.ofReal_mul,mul_inv_cancel₀ hn,Complex.ofReal_one]
    rw [he,one_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma operator_norm_lift (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T∈Set.range φ) : ∃ a : A, ‖a‖≤‖T‖ ∧ φ a=T := norm_lift φ hT

end Kadison.CStarContractiveLifts

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialUltrapower
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder ComplexStarModule

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence ComplexStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma vector_unitball_isClosed (hω : (ω : Filter ℕ)≤atTop) :
    IsClosed {x : boundedSubspace τ ω | ∃ a : ℕ →ᵇ A, ‖a‖≤1 ∧ vectorIn τ ω a=x} := by
  have hc := (bounded_image_isClosed ω (vectorCLM τ) hω {a : A | ‖a‖≤1} 1
    (fun _ h => h)).preimage (continuous_subtype_val (p := fun x => x∈boundedSubspace τ ω))
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,fun i => (a.norm_coe_le_norm i).trans ha,?_⟩
    exact congrArg Subtype.val hax
  · rintro ⟨a,ha,hax⟩
    refine ⟨a,(BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤1)).mpr ha,?_⟩
    exact Subtype.ext hax

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
theorem bicommutant_selfAdjoint_contraction (hω : (ω : Filter ℕ)≤atTop)
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : ℕ →ᵇ A, ‖a‖≤1 ∧ leftRestricted τ ω a=T := by
  have hx : T (sequenceVacuum τ ω)∈closure
      {x : boundedSubspace τ ω | ∃ a : ℕ →ᵇ A, ‖a‖≤1 ∧ vectorIn τ ω a=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,ha⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit (leftRestricted τ ω) hT hsT hnT (fun _ => sequenceVacuum τ ω) ε hε
    refine ⟨vectorIn τ ω a,⟨a,hna,rfl⟩,?_⟩
    simpa only [dist_eq_norm,norm_sub_rev,leftRestricted_vacuum] using ha ()
  rw [(vector_unitball_isClosed τ ω hω).closure_eq] at hx
  obtain ⟨a,hna,ha⟩ := hx
  refine ⟨a,hna,bicommutant_eq_of_vacuum τ ω hτ _ _ ?_ hT ?_⟩
  · exact Set.subset_centralizer_centralizer (Set.mem_range_self a)
  · simpa only [leftRestricted_vacuum] using ha

include hτ in
theorem range_bicommutant (hω : (ω : Filter ℕ)≤atTop) :
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))=
      Set.range (leftRestricted τ ω) := by
  let φ : (ℕ →ᵇ A) →⋆ₐ[ℂ] (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) := leftRestricted τ ω
  have h : ∀ T∈Set.centralizer (Set.centralizer (Set.range φ)),
      IsSelfAdjoint T → ‖T‖≤1 → T∈Set.range φ := by
    intro T hT hsT hnT
    obtain ⟨a,_,ha⟩ := bicommutant_selfAdjoint_contraction τ ω hτ hω hT hsT hnT
    exact ⟨a,ha⟩
  exact BicommutantRange.operatorHom_range φ h

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialUltrapowerTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

include hτ hω in
theorem bicommutant_norm_lift_oai {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
    ∃ a : ℕ →ᵇ A, ‖a‖≤‖T‖ ∧ leftRestricted τ ω a=T := by
  rw [range_bicommutant τ ω hτ hω] at hT
  exact CStarContractiveLifts.operator_norm_lift (leftRestricted τ ω) hT

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialSequence.bicommutant_norm_lift_oai.{u_1} := @OAI.Kadison.TracialSequence.bicommutant_norm_lift_oai.{u_1}
