-- Prove2me | solution 1 for OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:09:21.73412+00:00
-- url     : https://prove2.me/submissions/53f60a91-f7e3-43b7-a73f-2c8a5d36d891

import Mathlib
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_complement
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_exists_base_subEquivalent
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_EqualPartition_card_le_of_part_subEquivalent
import Theorems.Thm_OAI_Kadison_ProjectionJoin_dimension_sup_le

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

local instance instDecidableEq_r405b5d_1 : DecidableEq ι := Classical.decEq ι
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

local instance equalPartitionSumsDecidableEq_r405b5d_1 : DecidableEq ι := Classical.decEq ι
lemma piece_projection (i : ι) : IsStarProjection (D.piece i) := D.final_projection i

lemma piece_cross (i j : ι) (hij : i≠j) : D.piece i*D.piece j=0 := D.final_cross i j hij

lemma part_projection (s : Finset ι) : IsStarProjection (D.part s) :=
  orthogonal_sum_projection D.piece D.piece_projection D.piece_cross s

lemma base_equiv_piece (i : ι) : Equivalent M D.base (D.piece i) := by
  exact ⟨⟨D.v i,D.mem i,D.triple i,(D.initial i).le,le_rfl⟩,D.initial i,rfl⟩

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

local instance partitionRankDecidableEq_r405b5d_1 : DecidableEq ι := Classical.decEq ι
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

lemma rank_part [Nontrivial H] (hfin : IsFiniteAlgebra M) (s : Finset ι) : D.rank (D.part s)=s.card := by
  obtain ⟨t,ht,hts⟩ := D.exists_rank (D.part s) (D.part_projection s)
  apply Nat.le_antisymm
  · rw [←ht]
    exact D.card_le_of_part_subEquivalent hfin t s hts
  · exact D.card_le_rank_of_subEquivalent s
      (subEquivalent_of_le (D.part_mem s) (D.part_projection s) le_rfl)

lemma rank_zero [Nontrivial H] (hfin : IsFiniteAlgebra M) : D.rank 0=0 := by
  simpa only [D.part_empty,Finset.card_empty] using D.rank_part hfin ∅

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

lemma dimension_zero [Nontrivial H] (hfin : IsFiniteAlgebra M) : dimension M hfac hd 0=0 := by
  apply le_antisymm _ (dimension_nonneg M hfac hd 0)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k,rfl⟩
  simp only [lower,EqualPartition.rank_zero _ hfin,Nat.cast_zero,zero_div,le_refl]

lemma dimension_pos [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) : 0<dimension M hfac hd e := by
  obtain ⟨n,hn⟩ := exists_base_subEquivalent M hfac hd hfin heM he hen
  obtain ⟨i⟩ := (inferInstance : Nonempty (Index n))
  let D := partition M hfac hd n
  have hi : SubEquivalent M (D.piece i) e :=
    (D.base_equiv_piece i).symm.subEquivalent.trans (D.piece_projection i) D.base_projection hn
  have hk : 1≤D.rank e := by
    simpa only [Finset.card_singleton] using D.card_le_rank_of_subEquivalent {i}
      (by simpa only [D.part_singleton] using hi)
  apply lt_of_lt_of_le _ (lower_le_dimension M hfac hd e n)
  apply div_pos _ (by positivity)
  exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)

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

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

omit [Nontrivial H] in
lemma dimension_mono {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (hef : e≤f) : dimension M hfac hd e≤dimension M hfac hd f :=
  dimension_mono_subEquivalent M hfac hd he (subEquivalent_of_le heM he hef)

section Separable

variable [TopologicalSpace.SeparableSpace H]

include hfin

lemma dimension_eq_zero_iff {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    dimension M hfac hd e=0 ↔ e=0 := by
  constructor
  · intro h
    by_contra hn
    have hp := dimension_pos M hfac hd hfin heM he hn
    linarith
  · rintro rfl
    exact dimension_zero M hfac hd hfin

end Separable

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableProjectionJoin
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

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sup_mem (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : sup M P hP hPM∈M :=
  (exists_countable_sup M P hP hPM).choose_spec.1

lemma sup_projection (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) : IsStarProjection (sup M P hP hPM) :=
  (exists_countable_sup M P hP hPM).choose_spec.2.1

lemma le_sup (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M) (n : ℕ) : P n≤ sup M P hP hPM :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.1 n

lemma sup_le (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hP : ∀ n,IsStarProjection (P n)) (hPM : ∀ n,P n∈M)
    {Q : H →L[ℂ] H} (hQ : IsStarProjection Q) (hle : ∀ n,P n≤Q) : sup M P hP hPM≤Q :=
  (exists_countable_sup M P hP hPM).choose_spec.2.2.2.2 Q hQ hle

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionDimensionTopology
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

namespace Kadison.ProjectionDimensionTopology

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin

theorem strong_zero_of_geometric_dimension (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n))
    (hbound : ∀ n,dimension M hfac hd (P n)≤(1/2:ℝ)^n) (x : H) :
    Tendsto (fun n => P n x) atTop (𝓝 0) := by
  let T (n : ℕ) := sup M (fun k => P (n+k)) (fun k => hP (n+k)) (fun k => hPM (n+k))
  have hTM (n : ℕ) : T n∈M := sup_mem M _ _ _
  have hTP (n : ℕ) : IsStarProjection (T n) := sup_projection M _ _ _
  have hPT (n : ℕ) : P n≤T n := by
    simpa only [Nat.add_zero] using le_sup M (fun k => P (n+k))
      (fun k => hP (n+k)) (fun k => hPM (n+k)) 0
  have hmono : Antitone T := by
    apply antitone_nat_of_succ_le
    intro n
    apply sup_le M _ _ _ (hTP n)
    intro k
    have hh := le_sup M (fun k => P (n+k)) (fun k => hP (n+k)) (fun k => hPM (n+k)) (k+1)
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hh
  have hdim (n : ℕ) : dimension M hfac hd (T n)≤2*(1/2:ℝ)^n := by
    have hs : Summable (fun k : ℕ => (1/2:ℝ)^(n+k)) := by
      simpa only [pow_add] using (summable_geometric_of_lt_one
        (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)).mul_left ((1/2:ℝ)^n)
    have hh := dimension_sup_le M hfac hd hfin (fun k => P (n+k))
      (fun k => hP (n+k)) (fun k => hPM (n+k)) (fun k => (1/2:ℝ)^(n+k)) hs
      (fun k => hbound (n+k))
    have he : (∑' k : ℕ,(1/2:ℝ)^(n+k))=2*(1/2:ℝ)^n := by
      simp only [pow_add,tsum_mul_left]
      rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)]
      ring
    exact he ▸ hh
  let Q (n : ℕ) := 1-T n
  have hQM (n : ℕ) : Q n∈M := M.sub_mem M.one_mem (hTM n)
  have hQP (n : ℕ) : IsStarProjection (Q n) := (hTP n).one_sub
  have hQmono : Monotone Q := fun n m h => sub_le_sub_left (hmono h) 1
  obtain ⟨W,hWM,hWP,hQW,hlim,_⟩ := ProjectionChains.exists_strong_sup M Q hQP hQM hQmono
  have hc : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdW : 1≤dimension M hfac hd W := by
    have ht : Tendsto (fun n : ℕ => 1-2*(1/2:ℝ)^n) atTop (𝓝 1) := by
      simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hc)
    apply le_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro n
    have hh := dimension_mono M hfac hd (hQM n) (hQP n) (hQW n)
    change dimension M hfac hd (1-T n)≤_ at hh
    rw [dimension_complement M hfac hd hfin (hTM n) (hTP n)] at hh
    linarith [hdim n]
  have hW : W=1 := by
    have hdz : dimension M hfac hd (1-W)=0 := by
      rw [dimension_complement M hfac hd hfin hWM hWP]
      linarith [dimension_le_one M hfac hd W]
    have he := (dimension_eq_zero_iff M hfac hd hfin (M.sub_mem M.one_mem hWM)
      hWP.one_sub).mp hdz
    exact (sub_eq_zero.mp he).symm
  have hTlim : Tendsto (fun n => T n x) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := x)).sub (hlim x)
    rw [hW] at hh
    simpa only [Q,sub_apply,one_apply_eq_self,sub_sub_cancel,sub_self] using hh
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    ProjectionChains.projection_norm_mono (hP n) (hTP n) (hPT n) x) (by
      simpa only [norm_zero] using hTlim.norm)

theorem vector_uniform_absolute_continuity_oai (x : H) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ p : H →L[ℂ] H,p∈M → IsStarProjection p →
      dimension M hfac hd p<δ → ‖p x‖<ε := by
  classical
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ p : H →L[ℂ] H,p∈M ∧ IsStarProjection p ∧
      dimension M hfac hd p<(1/2:ℝ)^n ∧ ε≤‖p x‖ := hn ((1/2:ℝ)^n) (by positivity)
  choose P hPM hP hdP hnorm using hex
  have ht := strong_zero_of_geometric_dimension M hfac hd hfin P hPM hP (fun n => (hdP n).le) x
  have he := (show Tendsto (fun n => ‖P n x‖) atTop (𝓝 0) by
    simpa only [norm_zero] using ht.norm).eventually_lt_const hε
  obtain ⟨n,hn⟩ := he.exists
  exact (not_lt_of_ge (hnorm n)) hn

end Kadison.ProjectionDimensionTopology

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity_oai.{u_1} := @OAI.Kadison.ProjectionDimensionTopology.vector_uniform_absolute_continuity_oai.{u_1}
