-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_tendsto_of_strong_increasing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:42:40.662246+00:00
-- url     : https://prove2.me/submissions/91aad956-f4fe-4322-9d59-808a7de7fe2e

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_base
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_difference
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_exists_coherent_comparisons
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_subEquivalent_of_dimension_le

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

local instance instDecidableEq_rc3eb4e_1 : DecidableEq ι := Classical.decEq ι
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

local instance equalPartitionSumsDecidableEq_rc3eb4e_1 : DecidableEq ι := Classical.decEq ι
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

local instance partitionRankDecidableEq_rc3eb4e_1 : DecidableEq ι := Classical.decEq ι
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

lemma lower_nonneg (e : H →L[ℂ] H) (n : ℕ) : 0≤lower M hfac hd e n :=
  div_nonneg (Nat.cast_nonneg _) (by positivity)

lemma lower_le_one (e : H →L[ℂ] H) (n : ℕ) : lower M hfac hd e n≤1 := by
  apply (div_le_one (by positivity : (0:ℝ)<2^n)).mpr
  have h := (partition M hfac hd n).rank_le_card e
  rw [cardinality] at h
  exact_mod_cast h

lemma lower_le_dimension (e : H →L[ℂ] H) (n : ℕ) :
    lower M hfac hd e n≤dimension M hfac hd e :=
  le_csSup ⟨1,by rintro _ ⟨k,rfl⟩; exact lower_le_one M hfac hd e k⟩ ⟨n,rfl⟩

lemma dimension_nonneg (e : H →L[ℂ] H) : 0≤dimension M hfac hd e :=
  (lower_nonneg M hfac hd e 0).trans (lower_le_dimension M hfac hd e 0)

lemma dimension_le_one (e : H →L[ℂ] H) : dimension M hfac hd e≤1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  exact lower_le_one M hfac hd e k

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
-- module Solutions.OAIQ039_CM.Commutator_DyadicDimensionComparison
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma Link.equivalentSupports {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (v : Link M e f) : Equivalent M v.initial v.final :=
  ⟨⟨v.val,v.mem,v.triple,le_rfl,le_rfl⟩,rfl,rfl⟩

end Kadison.PartialIsometryOrder

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

omit [Nontrivial H] in
lemma dimension_mono {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (hef : e≤f) : dimension M hfac hd e≤dimension M hfac hd f :=
  dimension_mono_subEquivalent M hfac hd he (subEquivalent_of_le heM he hef)

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CoherentComparison
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

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
theorem subEquivalent_of_strong_increasing {p r : H →L[ℂ] H} (hp : IsStarProjection p)
    (hrM : r∈M) (hr : IsStarProjection r) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n)) (hmono : Monotone P)
    (hPp : ∀ n,P n≤p) (hdim : ∀ n,dimension M hfac hd (P n)≤dimension M hfac hd r)
    (hlim : ∀ x,Tendsto (fun n => P n x) atTop (𝓝 (p x))) : SubEquivalent M p r := by
  obtain ⟨v,hvmono,hvi⟩ := exists_coherent_comparisons M hfac hd hfin hp hrM hr P hPM hP hmono hPp hdim
  have hc : IsChain (·≤·) (Set.range v) := by
    rintro _ ⟨n,rfl⟩ _ ⟨m,rfl⟩ hne
    rcases le_total n m with h|h
    · exact Or.inl (hvmono h)
    · exact Or.inr (hvmono h)
  obtain ⟨u,hu⟩ := chain_has_upper M hp hr (Set.range v) hc (Set.range_nonempty v)
  have hPu (n : ℕ) : P n≤u.initial := by
    rw [←hvi n]
    exact ((Link.le_def _ _).mp (hu (Set.mem_range_self n))).1
  have hEq : u.initial*p=p := by
    ext x
    have hconv := u.initial.continuous.tendsto (p x) |>.comp (hlim x)
    have heq (n : ℕ) : u.initial (P n x)=P n x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (((hP n).le_iff_mul_eq_right u.initial_projection).mp (hPu n))
    have hconv' : Tendsto (fun n => u.initial (P n x)) atTop (𝓝 (p x)) := by
      simpa only [heq] using hlim x
    exact tendsto_nhds_unique hconv hconv'
  refine ⟨u,le_antisymm u.source_le ((hp.le_iff_mul_eq_right u.initial_projection).mpr hEq)⟩

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicDimensionNormal
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

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
theorem dimension_tendsto_of_strong_increasing_oai {p : H →L[ℂ] H}
    (hpM : p∈M) (hp : IsStarProjection p) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n)) (hmono : Monotone P)
    (hPp : ∀ n,P n≤p) (hlim : ∀ x,Tendsto (fun n => P n x) atTop (𝓝 (p x))) :
    Tendsto (fun n => dimension M hfac hd (P n)) atTop (𝓝 (dimension M hfac hd p)) := by
  let d (n : ℕ) := dimension M hfac hd (P n)
  let L := sSup (Set.range d)
  have hdmono : Monotone d := fun n m h => dimension_mono M hfac hd (hPM n) (hP n) (hmono h)
  have hb : BddAbove (Set.range d) := ⟨1,by
    rintro _ ⟨n,rfl⟩
    exact dimension_le_one M hfac hd (P n)⟩
  have hnL (n : ℕ) : d n≤L := le_csSup hb (Set.mem_range_self n)
  have hLpos : 0≤L := (dimension_nonneg M hfac hd (P 0)).trans (hnL 0)
  have hLp : L≤dimension M hfac hd p := by
    apply csSup_le (Set.range_nonempty d)
    rintro _ ⟨n,rfl⟩
    exact dimension_mono M hfac hd (hPM n) (hP n) (hPp n)
  have hLeq : L=dimension M hfac hd p := by
    by_contra hne
    have hlt : L<dimension M hfac hd p := lt_of_le_of_ne hLp hne
    have ht : Tendsto (fun n : ℕ => (1:ℝ)/2^n) atTop (𝓝 0) := by
      simpa only [div_pow,one_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
          (by norm_num : (1/2:ℝ)<1))
    obtain ⟨n,hn⟩ := (ht.eventually_lt_const (sub_pos.mpr hlt)).exists
    let D := partition M hfac hd n
    have hDb : dimension M hfac hd D.base=(1:ℝ)/2^n := dimension_base M hfac hd hfin n
    have hDpos : 0<dimension M hfac hd D.base := by rw [hDb]; positivity
    have hDp : dimension M hfac hd D.base≤dimension M hfac hd p := by rw [hDb]; linarith
    obtain ⟨v,hvi⟩ := subEquivalent_of_dimension_le M hfac hd hfin D.base_mem hpM
      D.base_projection hp hDp
    have hqM : v.final∈M := M.mul_mem v.mem (M.star_mem' v.mem)
    have hq : dimension M hfac hd v.final=dimension M hfac hd D.base :=
      dimension_congr_equivalent M hfac hd v.final_projection D.base_projection
        (by simpa only [hvi] using v.equivalentSupports.symm)
    have hr := v.residual_target_projection hp
    have hdr := dimension_difference M hfac hd hfin hpM hqM hp v.final_projection v.target_le
    have hPr : ∀ k,dimension M hfac hd (P k)≤dimension M hfac hd (p-v.final) := by
      intro k
      have hk := hnL k
      change dimension M hfac hd (P k)≤L at hk
      rw [hdr,hq,hDb]
      linarith
    have hcmp := subEquivalent_of_strong_increasing M hfac hd hfin hp
      (M.sub_mem hpM hqM) hr P hPM hP hmono hPp hPr hlim
    have heq : p-v.final=p := finite_subEquivalent_antisymm_of_le hfin hpM hp
      (sub_le_self _ v.final_projection.nonneg) hcmp
    rw [heq,hq] at hdr
    linarith
  rw [←hLeq]
  exact tendsto_atTop_ciSup hdmono hb

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_tendsto_of_strong_increasing_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_tendsto_of_strong_increasing_oai.{u_1}
