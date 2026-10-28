-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.small_projection_lift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:17:27.007206+00:00
-- url     : https://prove2.me/submissions/8fdd0ae3-9229-448c-b41b-5a33175a8da3

import Mathlib
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_TracialSequence_projection_rep_lift

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma norm_coe_tendsto (x : Pre ω H) :
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 ‖(x : Space ω H)‖) := by
  rw [Completion.norm_coe]
  exact tendsto_norm ω H x

lemma coe_eq_zero_iff (x : Pre ω H) : (x : Space ω H)=0 ↔
    Tendsto (fun i => ‖x.seq i‖) (ω : Filter ℕ) (𝓝 0) := by
  constructor
  · intro hx
    simpa only [hx,norm_zero] using norm_coe_tendsto ω H x
  · intro hx
    apply norm_eq_zero.mp
    exact tendsto_nhds_unique (norm_coe_tendsto ω H x) hx

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma norm_rightMulPre_le (a : A) : ‖rightMulPre τ hτ a‖ ≤ ‖a‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end TracialGNS

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma vector_eq_zero_iff (a : ℕ →ᵇ A) : vector τ ω a=0 ↔
    Tendsto (fun i => ‖algebraVector τ (a i)‖) (ω : Filter ℕ) (𝓝 0) :=
  coe_eq_zero_iff ω τ.GNS (vectorPre τ ω a)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma vector_mul_norm (a b : A) : ‖algebraVector τ (a*b)‖≤‖b‖*‖algebraVector τ a‖ := by
  change ‖(τ.toPreGNS (a*b) : τ.GNS)‖≤‖b‖*‖(τ.toPreGNS a : τ.GNS)‖
  simp only [Completion.norm_coe]
  change ‖rightMulPre τ hτ b (τ.toPreGNS a)‖≤_
  exact (rightMulPre τ hτ b).le_of_opNorm_le (norm_rightMulPre_le τ hτ b) _

include hτ in
lemma vector_mul_zero {a : ℕ →ᵇ A} (ha : vector τ ω a=0) (b : ℕ →ᵇ A) :
    vector τ ω (a*b)=0 := by
  rw [vector_eq_zero_iff] at ha ⊢
  have hlim := (tendsto_const_nhds (x := ‖b‖)).mul ha
  apply squeeze_zero (fun i => norm_nonneg _) (fun i =>
    (vector_mul_norm τ hτ (a i) (b i)).trans
      (mul_le_mul_of_nonneg_right (b.norm_coe_le_norm i) (norm_nonneg _)))
  simpa only [mul_zero] using hlim

include hτ in
lemma left_null {a : ℕ →ᵇ A} (ha : vector τ ω a=0) : leftRestricted τ ω a=0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change leftHom τ ω a (x:Space ω τ.GNS)=0
  have hclosed : IsClosed {y : Space ω τ.GNS | leftHom τ ω a y=0} :=
    isClosed_eq (leftHom τ ω a).continuous continuous_const
  apply closure_minimal (t := {y : Space ω τ.GNS | leftHom τ ω a y=0}) ?_ hclosed x.property
  rintro _ ⟨b,rfl⟩
  change leftHom τ ω a (vector τ ω b)=0
  rw [leftHom_vector]
  exact vector_mul_zero τ ω hτ ha b

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

open TracialGNS HilbertSequence ReducingRepresentation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma leftRestricted_eq_zero_iff (hτ : ∀ a b : A, τ (a*b)=τ (b*a)) (a : ℕ →ᵇ A) :
    leftRestricted τ ω a=0 ↔ vector τ ω a=0 := by
  constructor
  · intro h
    let v : boundedSubspace τ ω := ⟨vector τ ω 1,vector_mem τ ω 1⟩
    have he := congrArg (fun T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω =>
      (T v:Space ω τ.GNS)) h
    change leftHom τ ω a (vector τ ω 1)=0 at he
    simpa only [leftHom_vector,mul_one] using he
  · exact left_null τ ω hτ

end Kadison.TracialSequence

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

include hτ in
lemma leftRestricted_eq_of_eventuallyEq {a b : ℕ →ᵇ A}
    (hab : (a : ℕ → A)=ᶠ[ω] b) : leftRestricted τ ω a=leftRestricted τ ω b := by
  apply sub_eq_zero.mp
  rw [←map_sub,leftRestricted_eq_zero_iff τ ω hτ]
  change ((vectorPre τ ω (a-b)) : Space ω τ.GNS)=0
  apply (coe_eq_zero_iff ω τ.GNS _).mpr
  apply tendsto_const_nhds.congr'
  filter_upwards [hab] with i hi
  simp only [vectorPre_seq,BoundedContinuousFunction.sub_apply,hi,sub_self,
    map_zero,norm_zero]

include hτ in
theorem small_projection_lift_oai {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    {b : ℝ} (hb : 0≤b)
    {e : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f)))
    (het : (sequenceTrace τ ω e).re<b) :
    ∃ r : ℕ →ᵇ N, (∀ i, IsStarProjection (r i)) ∧
      (∀ i, (τ (f (r i))).re≤b) ∧ leftRestricted τ ω (mapSequence f r)=e := by
  classical
  obtain ⟨q,hq,hqe⟩ := projection_rep_lift τ ω N f he her
  have ht := Complex.continuous_re.tendsto _ |>.comp (tendsto_trace τ ω (mapSequence f q))
  change Tendsto (fun i => (τ (f (q i))).re) (ω : Filter ℕ)
    (𝓝 (sequenceTrace τ ω (leftRestricted τ ω (mapSequence f q))).re) at ht
  have hlim : (sequenceTrace τ ω (leftRestricted τ ω (mapSequence f q))).re < b :=
    lt_of_eq_of_lt (congrArg (fun T => (sequenceTrace τ ω T).re) hqe) het
  have hg : ∀ᶠ i in (ω : Filter ℕ), (τ (f (q i))).re≤b :=
    (ht.eventually (gt_mem_nhds hlim)).mono (fun _ h => h.le)
  let r := cutSequence N q (fun i => (τ (f (q i))).re≤b)
  have hrq : (r : ℕ → N)=ᶠ[ω] q := by
    filter_upwards [hg] with i hi
    exact ite_eq_left hi
  have hre : leftRestricted τ ω (mapSequence f r)=e := by
    exact (leftRestricted_eq_of_eventuallyEq τ ω hτ
      (a := mapSequence f r) (b := mapSequence f q)
      (hrq.mono (fun _ hi => congrArg f hi))).trans hqe
  have hr (i : ℕ) : IsStarProjection (r i) := by
    change IsStarProjection (if _ then q i else 0)
    split_ifs
    · exact hq i
    · exact IsStarProjection.zero _
  have hrt (i : ℕ) : (τ (f (r i))).re≤b := by
    change (τ (f (if _ then q i else 0))).re≤b
    split_ifs with hi
    · exact hi
    · simpa only [map_zero,Complex.zero_re] using hb
  exact ⟨r,hr,hrt,hre⟩

end Kadison.TracialSequence

end

end OAI
end

theorem solution.{u_1, u_3} : type_of% @OAI.Kadison.TracialSequence.small_projection_lift_oai.{u_1, u_3} := @OAI.Kadison.TracialSequence.small_projection_lift_oai.{u_1, u_3}
