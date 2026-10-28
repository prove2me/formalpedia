-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:27:14.806756+00:00
-- url     : https://prove2.me/submissions/f42fbc1f-a5c0-4519-8f65-074581ebc4af

import Mathlib
import Definitions.Def_OAIQ039C051

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

lemma finite_corner_cancel {M : VonNeumannAlgebra H} (hM : IsFiniteAlgebra M)
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (v : Link M e e) (hve : v.initial=e) : v.final=e := by
  let r := 1-e
  have hr : IsStarProjection r := he.one_sub
  have hvr : v.val*r=0 := by
    change v.val*(1-e)=0
    rw [mul_sub,mul_one,v.mul_source he,sub_self]
  have hrv : r*v.val=0 := by
    change (1-e)*v.val=0
    rw [sub_mul,one_mul,v.target_mul he,sub_self]
  have hsvr : star v.val*r=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,star_zero] using congrArg star hrv
  have hrsv : r*star v.val=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,star_zero] using congrArg star hvr
  have hi : star (v.val+r)*(v.val+r)=1 := by
    rw [star_add,hr.isSelfAdjoint.star_eq,add_mul,mul_add,mul_add,hsvr,hrv,
      hr.isIdempotentElem.eq,add_zero,zero_add]
    change v.initial+(1-e)=1
    rw [hve]; abel
  have hf := hM (v.val+r) (M.add_mem v.mem (M.sub_mem M.one_mem heM)) hi
  rw [star_add,hr.isSelfAdjoint.star_eq,add_mul,mul_add,mul_add,hvr,hrsv,
    hr.isIdempotentElem.eq,add_zero,zero_add] at hf
  change v.final+(1-e)=1 at hf
  have := congrArg (fun x : H →L[ℂ] H => x-(1-e)) hf
  have hc : (1 : H →L[ℂ] H)-(1-e)=e := by abel
  simpa only [add_sub_cancel_right,hc] using this

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

lemma finite_subEquivalent_antisymm_of_le {M : VonNeumannAlgebra H}
    (hfin : IsFiniteAlgebra M) {e f : H →L[ℂ] H}
    (hfM : f∈M) (hf : IsStarProjection f) (hef : e≤f)
    (hfe : SubEquivalent M f e) : e=f := by
  obtain ⟨v,hvi⟩ := hfe
  let w : Link M f f := ⟨v.val,v.mem,v.triple,v.source_le,v.target_le.trans hef⟩
  have hwf : w.final=f := finite_corner_cancel hfin hfM hf w hvi
  apply le_antisymm hef
  exact hwf ▸ v.target_le

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

local instance instDecidableEq_re92726_1 : DecidableEq ι := Classical.decEq ι
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

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

attribute [local instance] OAI.Kadison.PartialIsometryOrder.EqualPartition.instDecidableEq_1
lemma base_ne_zero [Nontrivial H] : D.base≠0 := by
  intro hz
  have hv : ∀ i,D.v i=0 := by
    intro i
    simpa only [hz,mul_zero] using (D.source i).symm
  have hone : (1 : H →L[ℂ] H)=0 := by
    rw [←D.total]
    simp only [hv,zero_mul,Finset.sum_const_zero]
  exact one_ne_zero hone

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

local instance equalPartitionSumsDecidableEq_re92726_1 : DecidableEq ι := Classical.decEq ι
lemma piece_projection (i : ι) : IsStarProjection (D.piece i) := D.final_projection i

lemma piece_cross (i j : ι) (hij : i≠j) : D.piece i*D.piece j=0 := D.final_cross i j hij

lemma part_projection (s : Finset ι) : IsStarProjection (D.part s) :=
  orthogonal_sum_projection D.piece D.piece_projection D.piece_cross s

lemma part_mono {s t : Finset ι} (hst : s⊆t) : D.part s≤D.part t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hst
  intro i _ _
  exact (D.piece_projection i).nonneg

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

lemma piece_ne_zero [Nontrivial H] (i : ι) : D.piece i≠0 := by
  intro hz
  have hv : D.v i=0 := by
    have ht := D.triple i
    change D.piece i*D.v i=D.v i at ht
    simpa only [hz,zero_mul] using ht.symm
  exact D.base_ne_zero (by rw [←D.initial i,hv,star_zero,zero_mul])

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartitionRankComparison
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

attribute [local instance] OAI.Kadison.PartialIsometryOrder.EqualPartition.instDecidableEq_2
lemma piece_mul_part_of_mem (s : Finset ι) {i : ι} (hi : i∈s) :
    D.piece i*D.part s=D.piece i := by
  rw [part,Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
  · exact (D.piece_projection i).isIdempotentElem.eq
  · intro j hj hne
    exact D.piece_cross i j hne.symm

lemma piece_mul_part_of_not_mem (s : Finset ι) {i : ι} (hi : i∉s) :
    D.piece i*D.part s=0 := orthogonal_mul_sum_eq_zero D.piece D.piece_cross s hi

lemma part_injective [Nontrivial H] : Function.Injective D.part := by
  intro s t hst
  apply Finset.ext
  intro i
  constructor
  · intro hi
    by_contra ht
    have h := D.piece_mul_part_of_mem s hi
    rw [hst,D.piece_mul_part_of_not_mem t ht] at h
    exact D.piece_ne_zero i h.symm
  · intro hi
    by_contra hs
    have h := D.piece_mul_part_of_mem t hi
    rw [←hst,D.piece_mul_part_of_not_mem s hs] at h
    exact D.piece_ne_zero i h.symm

lemma card_le_of_part_subEquivalent_oai [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (s t : Finset ι) (h : SubEquivalent M (D.part s) (D.part t)) : s.card≤t.card := by
  by_contra hle
  have hlt : t.card < s.card := Nat.lt_of_not_ge hle
  obtain ⟨r,hrs,hr⟩ := Finset.exists_subset_card_eq hlt.le
  have htr := (D.part_equiv_of_card_eq t r hr.symm).subEquivalent
  have hsr : SubEquivalent M (D.part s) (D.part r) :=
    h.trans (D.part_projection s) (D.part_projection t) htr
  have heq : D.part r=D.part s := finite_subEquivalent_antisymm_of_le hfin
    (D.part_mem s) (D.part_projection s) (D.part_mono hrs) hsr
  have hrc : r.card=s.card := congrArg Finset.card (D.part_injective heq)
  omega

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent_oai.{u_1, u_2} := @OAI.Kadison.PartialIsometryOrder.EqualPartition.card_le_of_part_subEquivalent_oai.{u_1, u_2}
