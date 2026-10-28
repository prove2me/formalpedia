-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:43:52.491989+00:00
-- url     : https://prove2.me/submissions/4f7eb565-0bd3-4187-8138-4a17c7020855

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_EqualPartition_rank_add_le_card

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteCancellation
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

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma extend_initial (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).initial=v.initial+w.initial := by
  obtain ⟨hvw,_⟩ := v.residual_cross he hf w
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  change star (v.val+w.val)*(v.val+w.val)=v.initial+w.initial
  simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,initial]

lemma extend_final (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).final=v.final+w.final := by
  obtain ⟨_,hvw⟩ := v.residual_cross he hf w
  have hwv : w.val*star v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  change (v.val+w.val)*star (v.val+w.val)=v.final+w.final
  simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,final]

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

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

namespace Link

variable {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}

lemma compFull_final (w : Link M f g) (v : Link M e f)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hvi : v.initial=e) (hwi : w.initial=f) (hvf : v.final=f) :
    (w.compFull v he hf hvi hwi).final=w.final := by
  change (w.val*v.val)*star (w.val*v.val)=w.val*star w.val
  rw [star_mul,mul_assoc,←mul_assoc v.val,←Link.final,hvf,←mul_assoc,w.mul_source hf]

end Link

lemma subEquivalent_of_le {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hef : e≤f) : SubEquivalent M e f := by
  have hi : star e*e=e := by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  refine ⟨⟨e,heM,?_,by rw [hi],?_⟩,hi⟩
  · rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,he.isIdempotentElem.eq]
  · rwa [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]

lemma equivalent_refl {M : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) : Equivalent M e e := by
  
  have hi : star e*e=e := by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  exact ⟨⟨e,heM,by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,he.isIdempotentElem.eq],
    hi.le,by simp only [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,le_refl]⟩,
    hi,by simp only [Link.final,he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]⟩

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

lemma Equivalent.trans {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : Equivalent M e f) (k : Equivalent M f g) : Equivalent M e g := by
  obtain ⟨v,hvi,hvf⟩ := h
  obtain ⟨w,hwi,hwf⟩ := k
  exact ⟨w.compFull v he hf hvi hwi,w.compFull_initial v he hf hvi hwi,
    (w.compFull_final v he hf hvi hwi hvf).trans hwf⟩

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

local instance instDecidableEq_r891f5f_1 : DecidableEq ι := Classical.decEq ι
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
-- module Solutions.OAIQ039_CM.Commutator_ProjectionAddition
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

namespace Link

variable {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}

lemma orthogonalSum_initial (v : Link M e f) (w : Link M e' f')
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0) (hvi : v.initial=e) :
    (v.orthogonalSum w he hf he' hf' hes hfs hvi).initial=v.initial+w.initial := by
  apply Link.extend_initial
  · exact he.add he' hes
  · exact hf.add hf' hfs

lemma orthogonalSum_final (v : Link M e f) (w : Link M e' f')
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0) (hvi : v.initial=e) :
    (v.orthogonalSum w he hf he' hf' hes hfs hvi).final=v.final+w.final := by
  apply Link.extend_final
  · exact he.add he' hes
  · exact hf.add hf' hfs

end Link

lemma SubEquivalent.orthogonal_add {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0)
    (h : SubEquivalent M e f) (k : SubEquivalent M e' f') :
    SubEquivalent M (e+e') (f+f') := by
  obtain ⟨v,hv⟩ := h
  obtain ⟨w,hw⟩ := k
  exact ⟨v.orthogonalSum w he hf he' hf' hes hfs hv,
    (v.orthogonalSum_initial w he hf he' hf' hes hfs hv).trans (by rw [hv,hw])⟩

lemma Equivalent.orthogonal_add {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0)
    (h : Equivalent M e f) (k : Equivalent M e' f') :
    Equivalent M (e+e') (f+f') := by
  obtain ⟨v,hvi,hvf⟩ := h
  obtain ⟨w,hwi,hwf⟩ := k
  exact ⟨v.orthogonalSum w he hf he' hf' hes hfs hvi,
    (v.orthogonalSum_initial w he hf he' hf' hes hfs hvi).trans (by rw [hvi,hwi]),
    (v.orthogonalSum_final w he hf he' hf' hes hfs hvi).trans (by rw [hvf,hwf])⟩

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

omit [CompleteSpace H] in
lemma orthogonal_mul_sum_eq_zero (e : ι → H →L[ℂ] H)
    (hc : ∀ i j,i≠j → e i*e j=0) (s : Finset ι) {i : ι} (hi : i∉s) :
    e i*(∑ j∈s,e j)=0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact hc i j (fun h => hi (h ▸ hj))

lemma Equivalent.finset_sum {M : VonNeumannAlgebra H} (e f : ι → H →L[ℂ] H)
    (he : ∀ i,IsStarProjection (e i)) (hf : ∀ i,IsStarProjection (f i))
    (hec : ∀ i j,i≠j → e i*e j=0) (hfc : ∀ i j,i≠j → f i*f j=0)
    (h : ∀ i,Equivalent M (e i) (f i)) (s : Finset ι) :
    Equivalent M (∑ i∈s,e i) (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using equivalent_refl M.zero_mem (IsStarProjection.zero _)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (h i).orthogonal_add (he i) (hf i)
      (orthogonal_sum_projection e he hec s) (orthogonal_sum_projection f hf hfc s)
      (orthogonal_mul_sum_eq_zero e hec s hi) (orthogonal_mul_sum_eq_zero f hfc s hi) ih

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

local instance equalPartitionSumsDecidableEq_r891f5f_1 : DecidableEq ι := Classical.decEq ι
lemma piece_projection (i : ι) : IsStarProjection (D.piece i) := D.final_projection i

lemma piece_cross (i j : ι) (hij : i≠j) : D.piece i*D.piece j=0 := D.final_cross i j hij

lemma part_projection (s : Finset ι) : IsStarProjection (D.part s) :=
  orthogonal_sum_projection D.piece D.piece_projection D.piece_cross s

lemma part_mono {s t : Finset ι} (hst : s⊆t) : D.part s≤D.part t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hst
  intro i _ _
  exact (D.piece_projection i).nonneg

lemma part_cross {s t : Finset ι} (hst : Disjoint s t) : D.part s*D.part t=0 := by
  rw [part,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  apply orthogonal_mul_sum_eq_zero D.piece D.piece_cross t
  exact fun ht => (Finset.disjoint_left.mp hst) hi ht

lemma base_equiv_piece (i : ι) : Equivalent M D.base (D.piece i) := by
  exact ⟨⟨D.v i,D.mem i,D.triple i,(D.initial i).le,le_rfl⟩,D.initial i,rfl⟩

lemma piece_equiv (i j : ι) : Equivalent M (D.piece i) (D.piece j) :=
  (D.base_equiv_piece i).symm.trans (D.piece_projection i) D.base_projection (D.base_equiv_piece j)

lemma part_equiv_of_card_eq (s t : Finset ι) (hst : s.card=t.card) :
    Equivalent M (D.part s) (D.part t) := by
  let f : s ≃ t := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hst)
  have h := Equivalent.finset_sum (M:=M) (fun i : s => D.piece i.val)
    (fun i : s => D.piece (f i).val)
    (fun i => D.piece_projection i.val) (fun i => D.piece_projection (f i).val)
    (fun i j hne => D.piece_cross i.val j.val (fun h => hne (Subtype.ext h)))
    (fun i j hne => D.piece_cross (f i).val (f j).val
      (fun h => hne (f.injective (Subtype.ext h))))
    (fun i => D.piece_equiv i.val (f i).val) Finset.univ
  have hf : (∑ i : s,D.piece (f i).val)=D.part t := by
    exact (f.sum_comp (fun j : t => D.piece j.val)).trans (Finset.sum_coe_sort t D.piece)
  simpa only [part,Finset.sum_coe_sort,hf] using h

lemma part_subEquivalent_of_card_le (s t : Finset ι) (hst : s.card≤t.card) :
    SubEquivalent M (D.part s) (D.part t) := by
  obtain ⟨r,hrt,hr⟩ := Finset.exists_subset_card_eq hst
  exact (D.part_equiv_of_card_eq s r hr.symm).subEquivalent.trans
    (D.part_projection s) (D.part_projection r)
    (subEquivalent_of_le (D.part_mem r) (D.part_projection r) (D.part_mono hrt))

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

local instance partitionRankDecidableEq_r891f5f_1 : DecidableEq ι := Classical.decEq ι
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

lemma part_subEquivalent_of_card_le_rank {e : H →L[ℂ] H} (he : IsStarProjection e)
    (s : Finset ι) (hs : s.card≤D.rank e) : SubEquivalent M (D.part s) e := by
  obtain ⟨t,ht,hte⟩ := D.exists_rank e he
  exact (D.part_subEquivalent_of_card_le s t (ht ▸ hs)).trans
    (D.part_projection s) (D.part_projection t) hte

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalRank
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

attribute [local instance] OAI.Kadison.PartialIsometryOrder.EqualPartition.orthogonalRankDecidableEq
lemma part_union {s t : Finset ι} (hst : Disjoint s t) : D.part (s∪t)=D.part s+D.part t :=
  Finset.sum_union hst

variable [Nontrivial H]

lemma orthogonal_rank_lower (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    D.rank e+D.rank f ≤ D.rank (e+f) := by
  have hc := D.rank_add_le_card hfac hfin heM hfM he hf hef
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have hfc : D.rank f ≤ sᶜ.card := by rw [Finset.card_compl,hs]; omega
  obtain ⟨t,hts,ht⟩ := Finset.exists_subset_card_eq hfc
  have hst : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i hi hit
    exact (Finset.mem_compl.mp (hts hit)) hi
  have htf := D.part_subEquivalent_of_card_le_rank hf t ht.le
  have hsub := hse.orthogonal_add (D.part_projection s) he (D.part_projection t) hf
    (D.part_cross hst) hef htf
  have hh : (s∪t).card ≤ D.rank (e+f) := D.card_le_rank_of_subEquivalent (s∪t)
    (by rwa [D.part_union hst])
  simpa only [Finset.card_union_of_disjoint hst,hs,ht] using hh

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicDimensionAdd
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

variable [Nontrivial H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
lemma lower_orthogonal_add_le_oai {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) (n : ℕ) :
    lower M hfac hd e n+lower M hfac hd f n≤lower M hfac hd (e+f) n := by
  dsimp only [lower]
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (partition M hfac hd n).orthogonal_rank_lower hfac hfin heM hfM he hf hef

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_le_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.DyadicPartition.lower_orthogonal_add_le_oai.{u_1}
