-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_coherent_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:43:51.341413+00:00
-- url     : https://prove2.me/submissions/7300bd69-3356-4908-a13e-362d2ea379c7

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_difference
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

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma extend_initial (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).initial=v.initial+w.initial := by
  obtain ⟨hvw,_⟩ := v.residual_cross he hf w
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  change star (v.val+w.val)*(v.val+w.val)=v.initial+w.initial
  simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,initial]

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

local instance instDecidableEq_rf6bc0e_1 : DecidableEq ι := Classical.decEq ι
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

local instance equalPartitionSumsDecidableEq_rf6bc0e_1 : DecidableEq ι := Classical.decEq ι
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

local instance partitionRankDecidableEq_rf6bc0e_1 : DecidableEq ι := Classical.decEq ι
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
lemma extend_comparison {p r q : H →L[ℂ] H} (hp : IsStarProjection p)
    (hrM : r∈M) (hr : IsStarProjection r) (hqM : q∈M) (hq : IsStarProjection q)
    (hqp : q≤p) (v : Link M p r) (hvi : v.initial≤q)
    (hdr : dimension M hfac hd q≤dimension M hfac hd r) :
    ∃ w : Link M p r,v≤w ∧ w.initial=q := by
  let b : Link M q r := ⟨v.val,v.mem,v.triple,hvi,v.target_le⟩
  have hiM : b.initial∈M := M.mul_mem (M.star_mem' b.mem) b.mem
  have hfM : b.final∈M := M.mul_mem b.mem (M.star_mem' b.mem)
  have heq := dimension_congr_equivalent M hfac hd b.initial_projection b.final_projection
    b.equivalentSupports
  have hds := dimension_difference M hfac hd hfin hqM hiM hq b.initial_projection b.source_le
  have hdt := dimension_difference M hfac hd hfin hrM hfM hr b.final_projection b.target_le
  obtain ⟨u,hui⟩ := subEquivalent_of_dimension_le M hfac hd hfin
    (M.sub_mem hqM hiM) (M.sub_mem hrM hfM) (b.residual_source_projection hq)
    (b.residual_target_projection hr) (by rw [hds,hdt,heq]; linarith)
  let z := b.extend hq hr u
  have hzp : z.initial≤p := by
    apply (z.initial_projection.le_iff_mul_eq_right hp).mpr
    calc
      p*z.initial = p*(q*z.initial) := by
        rw [(z.initial_projection.le_iff_mul_eq_right hq).mp z.source_le]
      _ = z.initial := by
        rw [←mul_assoc,(hq.le_iff_mul_eq_right hp).mp hqp,
          (z.initial_projection.le_iff_mul_eq_right hq).mp z.source_le]
  let w : Link M p r := ⟨z.val,z.mem,z.triple,hzp,z.target_le⟩
  refine ⟨w,?_,?_⟩
  · exact b.le_extend hq hr u
  · change z.initial=q
    rw [Link.extend_initial,hui]
    abel

include hfin in
theorem exists_coherent_comparisons_oai {p r : H →L[ℂ] H} (hp : IsStarProjection p)
    (hrM : r∈M) (hr : IsStarProjection r) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n)) (hmono : Monotone P)
    (hPp : ∀ n,P n≤p) (hdim : ∀ n,dimension M hfac hd (P n)≤dimension M hfac hd r) :
    ∃ v : ℕ → Link M p r,Monotone v ∧ ∀ n,(v n).initial=P n := by
  classical
  obtain ⟨b,hb⟩ := subEquivalent_of_dimension_le M hfac hd hfin (hPM 0) hrM (hP 0) hr (hdim 0)
  let V (n : ℕ) := {v : Link M p r // v.initial=P n}
  let v0 : V 0 := ⟨⟨b.val,b.mem,b.triple,b.source_le.trans (hPp 0),b.target_le⟩,hb⟩
  have hstep (n : ℕ) (v : V n) : ∃ w : V (n+1),v.val≤w.val := by
    obtain ⟨w,hvw,hw⟩ := extend_comparison M hfac hd hfin hp hrM hr (hPM (n+1))
      (hP (n+1)) (hPp (n+1)) v.val (by rw [v.property]; exact hmono (Nat.le_succ n)) (hdim (n+1))
    exact ⟨⟨w,hw⟩,hvw⟩
  let step (n : ℕ) (v : V n) : V (n+1) := (hstep n v).choose
  let v : (n : ℕ) → V n := fun n => Nat.rec v0 step n
  refine ⟨fun n => (v n).val,?_,fun n => (v n).property⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (hstep n (v n)).choose_spec

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_coherent_comparisons_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.DyadicPartition.exists_coherent_comparisons_oai.{u_1}
