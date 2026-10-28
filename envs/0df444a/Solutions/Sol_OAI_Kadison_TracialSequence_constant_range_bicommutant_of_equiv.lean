-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:51:25.700961+00:00
-- url     : https://prove2.me/submissions/db448aaa-d0b7-4737-ad7f-638e7310d9b7

import Mathlib
import Definitions.Def_OAIQ039C064
import Theorems.Thm_OAI_Kadison_TracialSequence_constant_range_bicommutant_of_closed

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ)) (hcyc : DenseRange (fun a : A => φ a ξ))

lemma equivalence_algebraVector (a : A) :
    equivalence τ φ ξ hτ hcyc (TracialGNS.algebraVector τ a)=φ a ξ :=
  embedding_coe τ φ ξ hτ a

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TraceEquivGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TraceEquivGNS

open TracialGNS

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
  (htrace : ∀ a,σ (e a)=τ a)

lemma unitary_algebraVector (a : A) :
    unitary e τ σ htrace (algebraVector τ a)=algebraVector σ (e a) := by
  rw [unitary,VectorGNS.equivalence_algebraVector]
  exact left_vacuum σ (e a)

include e htrace in
lemma vector_unitball_closed (hc : IsClosed {x : σ.GNS | ∃ b : B,‖b‖≤1 ∧ algebraVector σ b=x}) :
    IsClosed {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x} := by
  have he : {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x} =
      (unitary e τ σ htrace) ⁻¹' {x : σ.GNS | ∃ b : B,‖b‖≤1 ∧ algebraVector σ b=x} := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨e a,by simpa only [StarAlgEquiv.norm_map] using ha,(unitary_algebraVector e τ σ htrace a).symm⟩
    · rintro ⟨b,hb,hbx⟩
      refine ⟨e.symm b,by simpa only [StarAlgEquiv.norm_map] using hb,?_⟩
      apply (unitary e τ σ htrace).injective
      rw [unitary_algebraVector,e.apply_symm_apply,hbx]
  rw [he]
  exact hc.preimage (unitary e τ σ htrace).continuous

end Kadison.TraceEquivGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConstantSequenceClosedTransport
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

open scoped ComplexOrder Topology BoundedContinuousFunction

namespace Kadison.TracialSequence

open TracialGNS

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma constant_vector_closed_of_GNS (hclosed : IsClosed {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x}) :
    IsClosed {x : boundedSubspace τ ω | ∃ a : A,‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} := by
  have heq (a : A) : vectorIn τ ω (constantSequence a)=constantIn τ ω (algebraVector τ a) := by
    apply Subtype.ext
    exact vector_const τ ω a
  have hc := (constantIn τ ω).isometry.isClosedEmbedding.isClosedMap _ hclosed
  suffices he : {x : boundedSubspace τ ω | ∃ a : A,‖a‖≤1 ∧ vectorIn τ ω (constantSequence a)=x} =
      (constantIn τ ω) '' {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x} by
    rw [he]
    exact hc
  ext x
  constructor
  · rintro ⟨a,ha,hax⟩
    exact ⟨algebraVector τ a,⟨a,ha,rfl⟩,(heq a).symm.trans hax⟩
  · rintro ⟨y,⟨a,ha,rfl⟩,hy⟩
    exact ⟨a,ha,(heq a).trans hy⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e : A ≃⋆ₐ[ℂ] M) (σ : M →ₚ[ℂ] ℂ)

lemma constant_range_bicommutant_of_equiv_oai (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (htrace : ∀ a,σ (e a)=τ a) (hnormal : NormalGNS.BoundedWOTContinuous M σ) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp constantSequence)))=Set.range ((leftRestricted τ ω).comp constantSequence) := by
  apply constant_range_bicommutant_of_closed τ ω hτ
  apply constant_vector_closed_of_GNS τ ω
  exact TraceEquivGNS.vector_unitball_closed e τ σ htrace
    (NormalGNS.vector_unitball_isClosed M σ hnormal)

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv_oai := @OAI.Kadison.TracialSequence.constant_range_bicommutant_of_equiv_oai
