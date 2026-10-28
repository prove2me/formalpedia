-- Prove2me | solution 1 for OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:40:02.615304+00:00
-- url     : https://prove2.me/submissions/0620b3e6-43ba-472f-a303-5e227ef739f3

import Mathlib
import Definitions.Def_OAIQ039C056
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_difference
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_tendsto_of_strong_increasing
import Theorems.Thm_OAI_Kadison_ProjectionDimensionTopology_vector_uniform_absolute_continuity

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionEquivalence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma subEquivalent_of_le {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hef : e≤f) : SubEquivalent M e f := by
  have hi : star e*e=e := by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  refine ⟨⟨e,heM,?_,by rw [hi],?_⟩,hi⟩
  · rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,he.isIdempotentElem.eq]
  · rwa [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]

lemma Equivalent.symm {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (h : Equivalent M e f) : Equivalent M f e := by
  obtain ⟨v,hi,hf⟩ := h
  exact ⟨v.adjoint,by simpa using hf,by simpa using hi⟩

lemma Equivalent.subEquivalent {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (h : Equivalent M e f) : SubEquivalent M e f := by
  obtain ⟨v,hi,_⟩ := h
  exact ⟨v,hi⟩

lemma SubEquivalent.trans {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : SubEquivalent M e f) (k : SubEquivalent M f g) : SubEquivalent M e g := by
  obtain ⟨v,hv⟩ := h
  obtain ⟨w,hw⟩ := k
  exact ⟨w.compFull v he hf hv hw,w.compFull_initial v he hf hv hw⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EqualProjectionPartition
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

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance instDecidableEq_rccbb4b_1 : DecidableEq ι := Classical.decEq ι
lemma triple (i : ι) : D.v i*star (D.v i)*D.v i=D.v i := by
  rw [mul_assoc,D.initial,D.source]

lemma final_projection (i : ι) : IsStarProjection (D.v i*star (D.v i)) :=
  ⟨by change (D.v i*star (D.v i))*(D.v i*star (D.v i))=D.v i*star (D.v i)
      rw [←mul_assoc,D.triple],IsSelfAdjoint.mul_star_self _⟩

lemma final_cross (i j : ι) (hij : i≠j) :
    (D.v i*star (D.v i))*(D.v j*star (D.v j))=0 := by
  rw [mul_assoc,←mul_assoc (star (D.v i)),D.cross i j hij,zero_mul,mul_zero]

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicPartition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DyadicPartition

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma cardinality (n : ℕ) : Fintype.card (Index n)=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Index n × Bool)=2^(n+1)
    rw [Fintype.card_prod,Fintype.card_bool,ih,pow_succ]

end DyadicPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionSumEquivalence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*}

lemma orthogonal_sum_projection (e : ι → H →L[ℂ] H)
    (he : ∀ i,IsStarProjection (e i)) (hc : ∀ i j,i≠j → e i*e j=0)
    (s : Finset ι) : IsStarProjection (∑ i∈s,e i) := by
  classical
  constructor
  · change (∑ i∈s,e i)*(∑ i∈s,e i)=∑ i∈s,e i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · exact (he i).isIdempotentElem.eq
    · intro j hj hne
      exact hc i j hne.symm
  · change star (∑ i∈s,e i)=∑ i∈s,e i
    rw [star_sum]
    exact Finset.sum_congr rfl (fun i _ => (he i).isSelfAdjoint.star_eq)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EqualPartitionSums
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance equalPartitionSumsDecidableEq_rccbb4b_1 : DecidableEq ι := Classical.decEq ι
lemma piece_projection (i : ι) : IsStarProjection (D.piece i) := D.final_projection i

lemma piece_cross (i j : ι) (hij : i≠j) : D.piece i*D.piece j=0 := D.final_cross i j hij

lemma part_projection (s : Finset ι) : IsStarProjection (D.part s) :=
  orthogonal_sum_projection D.piece D.piece_projection D.piece_cross s

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartitionRank
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance partitionRankDecidableEq_rccbb4b_1 : DecidableEq ι := Classical.decEq ι
lemma rank_le_card (e : H →L[ℂ] H) : D.rank e≤Fintype.card ι := by
  classical
  exact Nat.findGreatest_le _

lemma exists_rank (e : H →L[ℂ] H) (he : IsStarProjection e) :
    ∃ s : Finset ι,s.card=D.rank e ∧ SubEquivalent M (D.part s) e := by
  classical
  apply Nat.findGreatest_spec (P := fun k => ∃ s : Finset ι, s.card=k ∧ SubEquivalent M (D.part s) e)
    (Nat.zero_le (Fintype.card ι))
  exact ⟨∅,by simp,by simpa only [D.part_empty] using
    subEquivalent_of_le M.zero_mem (IsStarProjection.zero _) he.nonneg⟩

lemma card_le_rank_of_subEquivalent {e : H →L[ℂ] H} (s : Finset ι)
    (h : SubEquivalent M (D.part s) e) : s.card≤D.rank e := by
  classical
  exact Nat.le_findGreatest (Finset.card_le_univ s) ⟨s,rfl,h⟩

lemma rank_mono_subEquivalent {e f : H →L[ℂ] H}
    (he : IsStarProjection e) (h : SubEquivalent M e f) : D.rank e≤D.rank f := by
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  rw [←hs]
  exact D.card_le_rank_of_subEquivalent s (hse.trans (D.part_projection s) he h)

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicDimension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma lower_le_one (e : H →L[ℂ] H) (n : ℕ) : lower M hfac hd e n≤1 := by
  apply (div_le_one (by positivity : (0:ℝ)<2^n)).mpr
  have h := (partition M hfac hd n).rank_le_card e
  rw [cardinality] at h
  exact_mod_cast h

lemma lower_le_dimension (e : H →L[ℂ] H) (n : ℕ) :
    lower M hfac hd e n≤dimension M hfac hd e :=
  le_csSup ⟨1,by rintro _ ⟨k,rfl⟩; exact lower_le_one M hfac hd e k⟩ ⟨n,rfl⟩

lemma dimension_mono_subEquivalent {e f : H →L[ℂ] H} (he : IsStarProjection e)
    (h : SubEquivalent M e f) : dimension M hfac hd e≤dimension M hfac hd f := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  apply le_trans _ (lower_le_dimension M hfac hd f k)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (partition M hfac hd k).rank_mono_subEquivalent he h

lemma dimension_congr_equivalent {e f : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f) (h : Equivalent M e f) :
    dimension M hfac hd e=dimension M hfac hd f := by
  apply le_antisymm
  · exact dimension_mono_subEquivalent M hfac hd he h.subEquivalent
  · exact dimension_mono_subEquivalent M hfac hd hf h.symm.subEquivalent

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionDimensionUnitary
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma projection_unitary_equivalent {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H)∈M) :
    Equivalent M p ((u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H)) := by
  have hi : star ((u : H →L[ℂ] H)*p)*((u : H →L[ℂ] H)*p)=p := by
    simp only [star_mul,hp.isSelfAdjoint.star_eq,mul_assoc,
      ←mul_assoc (star (u : H →L[ℂ] H)),u.property.1,one_mul,hp.isIdempotentElem.eq]
  have hf : ((u : H →L[ℂ] H)*p)*star ((u : H →L[ℂ] H)*p)=
      (u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H) := by
    rw [star_mul,hp.isSelfAdjoint.star_eq,←mul_assoc, mul_assoc (u : H →L[ℂ] H) p p,
      hp.isIdempotentElem.eq]
  refine ⟨⟨(u : H →L[ℂ] H)*p,M.mul_mem hu hpM,?_,hi.le,hf.le⟩,hi,hf⟩
  rw [mul_assoc,hi,mul_assoc,hp.isIdempotentElem.eq]

lemma unitary_projection {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (u : unitary (H →L[ℂ] H)) :
    IsStarProjection ((u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H)) := by
  exact hp.map (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u)

lemma dimension_unitary {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H)∈M) :
    dimension M hfac hd ((u : H →L[ℂ] H)*p*star (u : H →L[ℂ] H))=
      dimension M hfac hd p :=
  (dimension_congr_equivalent M hfac hd hp (unitary_projection hp u)
    (projection_unitary_equivalent M hpM hp u hu)).symm

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (hfin : IsFiniteAlgebra M)

include hfin in
theorem orbit_vector_uniform_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : H →L[ℂ] H,p∈M → IsStarProjection p →
      dimension M hfac hd p<δ → ∀ u : unitary (H →L[ℂ] H),
      (u : H →L[ℂ] H)∈M → ‖p ((u : H →L[ℂ] H) x)‖<ε := by
  obtain ⟨δ,hδ,h⟩ := ProjectionDimensionTopology.vector_uniform_absolute_continuity
    M hfac hd hfin x ε hε
  refine ⟨δ,hδ,?_⟩
  intro p hpM hp hdp u hu
  have hqM : ((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)*p*
      star ((star u : unitary (H →L[ℂ] H)) : H →L[ℂ] H)∈M :=
    M.mul_mem (M.mul_mem (M.star_mem' hu) hpM) (by simpa using hu)
  have hq := h _ hqM (unitary_projection hp (star u)) (by
    rw [dimension_unitary M hfac hd hpM hp (star u) (M.star_mem' hu)]
    exact hdp)
  simpa only [Unitary.coe_star,star_star,mul_apply_eq_comp,
    ←Unitary.coe_star,Unitary.norm_map] using hq

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakDualHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison.WeakDualHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] OAI.Kadison.WeakDualHull.instAddCommGroupWeakDualComplex_solutions
attribute [local instance] OAI.Kadison.WeakDualHull.instModuleRealWeakDualComplex_solutions
lemma eval_norm_le {S : Set (WeakDual ℂ E)} (a : E) (R : ℝ)
    (h : ∀ f∈S,‖f a‖≤R) {f : WeakDual ℂ E} (hf : f∈hull S) : ‖f a‖≤R := by
  have hc : IsClosed {f : WeakDual ℂ E | ‖f a‖≤R} :=
    isClosed_le (WeakDual.eval_continuous a).norm continuous_const
  have hv : Convex ℝ {f : WeakDual ℂ E | ‖f a‖≤R} := by
    intro g hg k hk s t hs ht hst
    change ‖s • g a+t • k a‖≤R
    calc
      _ ≤ ‖s • g a‖+‖t • k a‖ := norm_add_le _ _
      _ = s*‖g a‖+t*‖k a‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hs,abs_of_nonneg ht]
      _ ≤ s*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hg hs)
        (mul_le_mul_of_nonneg_left hk ht)
      _ = R := by rw [←add_mul,hst,one_mul]
  exact closure_minimal (convexHull_min h hv) hc hf

end Kadison.WeakDualHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrbitStateHull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

variable (hfin : IsFiniteAlgebra M)

include hfac hd hfin

theorem hull_projection_absolute_continuity (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : M,IsStarProjection (p : H →L[ℂ] H) →
      dimension M hfac hd p<δ → ∀ f∈hull M x,‖f p‖≤ε := by
  obtain ⟨δ,hδ,hp⟩ := orbit_vector_uniform_absolute_continuity M hfac hd hfin x
    (ε/(‖x‖+1)) (div_pos hε (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro p hproj hdim f hf
  apply WeakDualHull.eval_norm_le p ε _ hf
  rintro g ⟨u,hu,rfl⟩
  have hv := hp p p.property hproj hdim u hu
  calc
    _ ≤ ‖(u : H →L[ℂ] H) x‖*‖(p : H →L[ℂ] H) ((u : H →L[ℂ] H) x)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖*(ε/(‖x‖+1)) := by
      rw [Unitary.norm_map]
      exact mul_le_mul_of_nonneg_left hv.le (norm_nonneg x)
    _ ≤ (‖x‖+1)*(ε/(‖x‖+1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity)

theorem hull_projection_tendsto (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x)
    (p : M) (hp : IsStarProjection (p : H →L[ℂ] H)) (P : ℕ → M)
    (hP : ∀ n,IsStarProjection ((P n : M) : H →L[ℂ] H))
    (hmono : Monotone (fun n => ((P n : M) : H →L[ℂ] H)))
    (hPp : ∀ n,(P n : H →L[ℂ] H)≤(p : H →L[ℂ] H))
    (hlim : ∀ y,Tendsto (fun n => (P n : H →L[ℂ] H) y) atTop (𝓝 ((p : H →L[ℂ] H) y))) :
    Tendsto (fun n => f (P n)) atTop (𝓝 (f p)) := by
  have hdlim := dimension_tendsto_of_strong_increasing M hfac hd hfin p.property hp
    (fun n => (P n : H →L[ℂ] H)) (fun n => (P n).property) hP hmono hPp hlim
  have hdiff : Tendsto (fun n => dimension M hfac hd ((p-P n : M) : H →L[ℂ] H)) atTop (𝓝 0) := by
    have he (n : ℕ) : dimension M hfac hd ((p-P n : M) : H →L[ℂ] H)=
        dimension M hfac hd p-dimension M hfac hd (P n) :=
      dimension_difference M hfac hd hfin p.property (P n).property hp (hP n) (hPp n)
    simp_rw [he]
    simpa only [sub_self] using (tendsto_const_nhds (x := dimension M hfac hd p)).sub hdlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδp⟩ := hull_projection_absolute_continuity M hfac hd hfin x (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hdiff.eventually_lt_const hδ)
  refine ⟨N,?_⟩
  intro n hn
  have hb := hδp (p-P n) ((hP n).le_iff_sub hp |>.mp (hPp n)) (hN n hn) f hf
  rw [map_sub,norm_sub_rev] at hb
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using lt_of_le_of_lt hb (by linarith : ε/2<ε)

end Kadison.OrbitStateHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.OrbitStateHull

open PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfac hd hfin

lemma hull_projectionContinuousAtOne_oai (x : H) {f : WeakDual ℂ M} (hf : f∈hull M x) :
    PositiveWOT.ProjectionContinuousAtOne M (positive M x f hf) := by
  intro P hP hmono hlim
  exact hull_projection_tendsto M hfac hd hfin x hf 1 (IsStarProjection.one _) P hP hmono
    (fun n => (hP n).le_one) hlim

end Kadison.OrbitStateHull

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne_oai.{u_1} := @OAI.Kadison.OrbitStateHull.hull_projectionContinuousAtOne_oai.{u_1}
