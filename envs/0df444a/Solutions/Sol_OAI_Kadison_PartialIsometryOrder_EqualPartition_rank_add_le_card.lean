-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:27:59.362487+00:00
-- url     : https://prove2.me/submissions/23142da8-197d-4867-9417-ae0b1224cc15

import Mathlib
import Definitions.Def_OAIQ039C046
import Definitions.Def_OAIQ039C051
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_EqualPartition_card_le_of_part_subEquivalent

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

lemma IsFiniteAlgebra.coisometry {M : VonNeumannAlgebra H} (hM : IsFiniteAlgebra M)
    {v : H →L[ℂ] H} (hv : v∈M) (h : v*star v=1) : star v*v=1 := by
  simpa only [star_star] using hM (star v) (M.star_mem' hv) (by simpa only [star_star] using h)

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

theorem finite_unitary_extension (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {p q : H →L[ℂ] H} (hpM : p∈M) (hqM : q∈M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : Link M p q) (hvi : v.initial=p) (hvf : v.final=q) :
    ∃ u∈M,star u*u=1 ∧ u*star u=1 ∧ u*p=v.val := by
  let b : Link M 1 1 := ⟨v.val,v.mem,v.triple,v.source_le.trans hp.le_one,v.target_le.trans hq.le_one⟩
  have hbi : b.initial=p := hvi
  have hbf : b.final=q := hvf
  have hiM : 1-b.initial∈M := by rw [hbi]; exact M.sub_mem M.one_mem hpM
  have hfM : 1-b.final∈M := by rw [hbf]; exact M.sub_mem M.one_mem hqM
  obtain ⟨w,hw⟩ := factor_comparison M hfac hiM hfM
    (b.residual_source_projection (IsStarProjection.one _))
    (b.residual_target_projection (IsStarProjection.one _))
  let z := b.extend (IsStarProjection.one _) (IsStarProjection.one _) w
  have hz : z.initial=1 ∧ z.final=1 := by
    rcases hw with hw|hw
    · have he : z.initial=1 := by
        rw [show z.initial=b.initial+w.initial from b.extend_initial _ _ w,hw]; abel
      exact ⟨he,hfin z.val z.mem he⟩
    · have he : z.final=1 := by
        rw [show z.final=b.final+w.final from b.extend_final _ _ w,hw]; abel
      exact ⟨hfin.coisometry z.mem he,he⟩
  refine ⟨z.val,z.mem,hz.1,hz.2,?_⟩
  simpa only [hbi] using (b.le_extend (IsStarProjection.one _) (IsStarProjection.one _) w).2

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

lemma subEquivalent_of_le {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hef : e≤f) : SubEquivalent M e f := by
  have hi : star e*e=e := by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  refine ⟨⟨e,heM,?_,by rw [hi],?_⟩,hi⟩
  · rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,he.isIdempotentElem.eq]
  · rwa [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]

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

local instance instDecidableEq_r4725b0_1 : DecidableEq ι := Classical.decEq ι
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

theorem subEquivalent_unitary (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (h : SubEquivalent M e f) :
    ∃ u∈M,star u*u=1 ∧ u*star u=1 ∧ u*e*star u≤f := by
  obtain ⟨v,hvi⟩ := h
  obtain ⟨u,hu,hui,huf,huv⟩ := finite_unitary_extension M hfac hfin
    heM (M.mul_mem v.mem (M.star_mem' v.mem)) he v.final_projection
    (⟨v.val,v.mem,v.triple,v.source_le,le_rfl⟩ : Link M e v.final) hvi rfl
  have heq : u*e*star u=v.final := by
    calc
      _=(u*e)*star (u*e) := by rw [star_mul,he.isSelfAdjoint.star_eq,←mul_assoc,
        mul_assoc u e e,he.isIdempotentElem.eq]
      _=v.final := by rw [huv]; rfl
  exact ⟨u,hu,hui,huf,heq ▸ v.target_le⟩

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

local instance equalPartitionSumsDecidableEq_r4725b0_1 : DecidableEq ι := Classical.decEq ι
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

local instance partitionRankDecidableEq_r4725b0_1 : DecidableEq ι := Classical.decEq ι
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

lemma rank_part [Nontrivial H] (hfin : IsFiniteAlgebra M) (s : Finset ι) : D.rank (D.part s)=s.card := by
  obtain ⟨t,ht,hts⟩ := D.exists_rank (D.part s) (D.part_projection s)
  apply Nat.le_antisymm
  · rw [←ht]
    exact D.card_le_of_part_subEquivalent hfin t s hts
  · exact D.card_le_rank_of_subEquivalent s
      (subEquivalent_of_le (D.part_mem s) (D.part_projection s) le_rfl)

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionComplements
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

lemma conjugate_projection {e u : H →L[ℂ] H} (he : IsStarProjection e)
    (hui : star u*u=1) : IsStarProjection (u*e*star u) := by
  constructor
  · change (u*e*star u)*(u*e*star u)=u*e*star u
    calc
      _=u*e*(star u*u)*e*star u := by noncomm_ring
      _=u*e*star u := by rw [hui,mul_one,mul_assoc u e e,he.isIdempotentElem.eq]
  · change star (u*e*star u)=u*e*star u
    simp only [star_mul,star_star,he.isSelfAdjoint.star_eq,mul_assoc]

lemma equivalent_conjugate {M : VonNeumannAlgebra H} {e u : H →L[ℂ] H}
    (heM : e∈M) (huM : u∈M) (he : IsStarProjection e) (hui : star u*u=1) :
    Equivalent M e (u*e*star u) := by
  have hi : star (u*e)*(u*e)=e := by
    rw [star_mul,he.isSelfAdjoint.star_eq,mul_assoc,←mul_assoc (star u),hui,one_mul,
      he.isIdempotentElem.eq]
  have hf : (u*e)*star (u*e)=u*e*star u := by
    rw [star_mul,he.isSelfAdjoint.star_eq,←mul_assoc,mul_assoc u e e,he.isIdempotentElem.eq]
  have ht : (u*e)*star (u*e)*(u*e)=u*e := by
    rw [mul_assoc,hi,mul_assoc,he.isIdempotentElem.eq]
  exact ⟨⟨u*e,M.mul_mem huM heM,ht,hi.le,hf.le⟩,hi,hf⟩

lemma subEquivalent_complement (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : SubEquivalent M e f) :
    SubEquivalent M (1-f) (1-e) := by
  obtain ⟨u,hu,hui,huf,hle⟩ := subEquivalent_unitary M hfac hfin heM he hef
  have hconj : star u*(u*e*star u)*u=e := by
    calc
      _=(star u*u)*e*(star u*u) := by noncomm_ring
      _=e := by rw [hui,one_mul,mul_one]
  have he_le : e ≤ star u*f*u := by
    simpa only [hconj] using star_left_conjugate_le_conjugate hle u
  have hcomp : star u*(1-f)*u≤1-e := by
    calc
      _=1-star u*f*u := by rw [mul_sub,sub_mul,mul_one,hui]
      _≤1-e := sub_le_sub_left he_le 1
  have hsu : star (star u)*star u=1 := by simpa only [star_star] using huf
  have hg : IsStarProjection (star u*(1-f)*u) := by
    simpa only [star_star] using (conjugate_projection (u := star u) hf.one_sub hsu)
  have hgM : star u*(1-f)*u∈M :=
    M.mul_mem (M.mul_mem (M.star_mem' hu) (M.sub_mem M.one_mem hfM)) hu
  have heq : Equivalent M (1-f) (star u*(1-f)*u) := by
    simpa only [star_star] using
      (equivalent_conjugate (M.sub_mem M.one_mem hfM) (M.star_mem' hu) hf.one_sub hsu)
  exact heq.subEquivalent.trans hf.one_sub hg (subEquivalent_of_le hgM hg hcomp)

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
lemma part_compl (s : Finset ι) : D.part sᶜ=1-D.part s := by
  have h : D.part s+D.part sᶜ=1 := by
    have hh := Finset.sum_add_sum_compl s D.piece
    change D.part s+D.part sᶜ=D.part Finset.univ at hh
    rwa [D.part_univ] at hh
  exact eq_sub_of_add_eq' h

variable [Nontrivial H]

lemma rank_add_le_card_oai (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    D.rank e+D.rank f ≤ Fintype.card ι := by
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have hscomp := subEquivalent_complement M hfac hfin (D.part_mem s) heM
    (D.part_projection s) he hse
  have hfle : f ≤ 1-e := by
    apply le_sub_iff_add_le.mpr
    simpa only [add_comm f e] using (he.add hf hef).le_one
  have hfs : SubEquivalent M f (D.part sᶜ) := by
    rw [D.part_compl]
    exact (subEquivalent_of_le hfM hf hfle).trans hf he.one_sub hscomp
  have hr := D.rank_mono_subEquivalent hf hfs
  rw [D.rank_part hfin,Finset.card_compl] at hr
  have hsc := Finset.card_le_univ s
  omega

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card_oai.{u_1, u_2} := @OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card_oai.{u_1, u_2}
