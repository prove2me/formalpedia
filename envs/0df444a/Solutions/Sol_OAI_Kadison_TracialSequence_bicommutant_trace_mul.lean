-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.bicommutant_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:11:34.694363+00:00
-- url     : https://prove2.me/submissions/0f09bbd0-62f8-4d5b-96d1-5b3276bc0c11

import Mathlib
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_TracialSequence_trace_mul

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
theorem bicommutant_trace_mul_oai
    {S T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hS : S∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω)))) :
    sequenceTrace τ ω (S*T)=sequenceTrace τ ω (T*S) := by
  rw [range_bicommutant τ ω hτ hω] at hS hT
  obtain ⟨a,rfl⟩ := hS
  obtain ⟨b,rfl⟩ := hT
  simpa only [map_mul] using trace_mul τ ω hτ a b

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialSequence.bicommutant_trace_mul_oai.{u_1} := @OAI.Kadison.TracialSequence.bicommutant_trace_mul_oai.{u_1}
