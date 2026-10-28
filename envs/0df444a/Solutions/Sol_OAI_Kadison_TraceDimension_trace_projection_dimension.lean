-- Prove2me | solution 1 for OAI.Kadison.TraceDimension.trace_projection_dimension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:47:58.166751+00:00
-- url     : https://prove2.me/submissions/b7ee5d2d-14df-430e-822f-f80db32104ef

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_dimension_complement

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

local instance instDecidableEq_r373c3d_1 : DecidableEq ι := Classical.decEq ι
lemma triple (i : ι) : D.v i*star (D.v i)*D.v i=D.v i := by
  rw [mul_assoc,D.initial,D.source]

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
lemma double_val (w : Link M D.base D.base) (hww : w.val*w.val=0)
    (hsum : w.initial+w.final=D.base) (i : ι) (b : Bool) :
    (D.double w hww hsum).v (i,b)=D.v i*(if b then w.val else w.initial) := rfl

end EqualPartition

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

local instance equalPartitionSumsDecidableEq_r373c3d_1 : DecidableEq ι := Classical.decEq ι
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

local instance partitionRankDecidableEq_r373c3d_1 : DecidableEq ι := Classical.decEq ι
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

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicRankStep
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

local instance instDecidableEq_3_r373c3d_1 : DecidableEq ι := Classical.decEq ι
variable (w : Link M D.base D.base) (hww : w.val*w.val=0) (hsum : w.initial+w.final=D.base)

lemma double_piece_sum (i : ι) :
    (∑ b : Bool,(D.double w hww hsum).piece (i,b))=D.piece i := by
  rw [Fintype.sum_bool]
  simp only [piece,double_val,Bool.false_eq_true,↓reduceIte,star_mul,
    w.initial_projection.isSelfAdjoint.star_eq]
  have hi : w.initial*w.initial=w.initial := w.initial_projection.isIdempotentElem.eq
  calc
    _=D.v i*(w.final+w.initial*w.initial)*star (D.v i) := by
      dsimp only [Link.final]
      noncomm_ring
    _=D.v i*D.base*star (D.v i) := by rw [hi,add_comm w.final,hsum]
    _=D.piece i := by rw [D.source]; rfl

lemma double_part (s : Finset ι) :
    (D.double w hww hsum).part ((s ×ˢ Finset.univ))=D.part s := by
  change (∑ j∈(s ×ˢ Finset.univ),(D.double w hww hsum).piece j)=_
  rw [Finset.sum_product]
  simp only [double_piece_sum]
  rfl

lemma double_rank_lower {e : H →L[ℂ] H} (he : IsStarProjection e) :
    2*D.rank e≤(D.double w hww hsum).rank e := by
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have h := (D.double w hww hsum).card_le_rank_of_subEquivalent ((s ×ˢ Finset.univ))
    (by rwa [D.double_part w hww hsum])
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_bool,hs,Nat.mul_comm] using h

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

lemma rank_succ_lower {e : H →L[ℂ] H} (he : IsStarProjection e) (n : ℕ) :
    2*(partition M hfac hd n).rank e≤(partition M hfac hd (n+1)).rank e := by
  let D := partition M hfac hd n
  let p : ProjectionIn M := ⟨D.base,D.base_mem,D.base_projection⟩
  change 2*D.rank e≤(D.double (DyadicCuts.half M hfac hd p)
    (DyadicCuts.half_square M hfac hd p) (DyadicCuts.half_sum M hfac hd p)).rank e
  exact D.double_rank_lower (DyadicCuts.half M hfac hd p)
    (DyadicCuts.half_square M hfac hd p) (DyadicCuts.half_sum M hfac hd p) he

lemma lower_monotone {e : H →L[ℂ] H} (he : IsStarProjection e) : Monotone (lower M hfac hd e) := by
  apply monotone_nat_of_le_succ
  intro n
  have h : (2:ℝ)*(partition M hfac hd n).rank e≤(partition M hfac hd (n+1)).rank e :=
    by exact_mod_cast rank_succ_lower M hfac hd he n
  dsimp only [lower]
  rw [pow_succ]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

lemma lower_tendsto_dimension {e : H →L[ℂ] H} (he : IsStarProjection e) :
    Tendsto (lower M hfac hd e) atTop (𝓝 (dimension M hfac hd e)) := by
  exact tendsto_atTop_ciSup (lower_monotone M hfac hd he)
    ⟨1,by rintro _ ⟨k,rfl⟩; exact lower_le_one M hfac hd e k⟩

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TraceDimension
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

namespace Kadison.TraceDimension

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

include hτ

lemma trace_subEquivalent {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (h : SubEquivalent M e f) : (τ ⟨e,heM⟩).re≤(τ ⟨f,hfM⟩).re := by
  obtain ⟨v,hv⟩ := h
  let a : M := ⟨v.val,v.mem⟩
  have ha : star a*a=⟨e,heM⟩ := Subtype.ext hv
  have hb : a*star a≤⟨f,hfM⟩ := v.target_le
  calc
    _=(τ (star a*a)).re := by rw [ha]
    _=(τ (a*star a)).re := congrArg Complex.re (hτ (star a) a)
    _≤_ := (τ.monotone hb).1

lemma trace_equivalent {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (h : Equivalent M e f) : τ ⟨e,heM⟩=τ ⟨f,hfM⟩ := by
  obtain ⟨v,hvi,hvf⟩ := h
  let a : M := ⟨v.val,v.mem⟩
  have ha : star a*a=⟨e,heM⟩ := Subtype.ext hvi
  have hb : a*star a=⟨f,hfM⟩ := Subtype.ext hvf
  rw [←ha,←hb,hτ]

lemma partition_base_trace {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : EqualPartition M ι) (hone : τ 1=1) :
    τ ⟨D.base,D.base_mem⟩=(Fintype.card ι:ℂ)⁻¹ := by
  have hpiece (i : ι) : τ ⟨D.piece i,D.piece_mem i⟩=τ ⟨D.base,D.base_mem⟩ :=
    (trace_equivalent M τ hτ D.base_mem (D.piece_mem i) (D.base_equiv_piece i)).symm
  have hsum : (∑ i, (⟨D.piece i,D.piece_mem i⟩:M))=1 := by
    apply Subtype.ext
    change M.toStarSubalgebra.subtype (∑ i,(⟨D.piece i,D.piece_mem i⟩:M))=1
    rw [map_sum]
    exact D.total
  have he := congrArg τ hsum
  rw [map_sum] at he
  simp_rw [hpiece] at he
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hone] at he
  have hn : (Fintype.card ι:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact he

lemma partition_part_trace {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : EqualPartition M ι) (hone : τ 1=1) (s : Finset ι) :
    (τ ⟨D.part s,D.part_mem s⟩).re=(s.card:ℝ)/(Fintype.card ι:ℝ) := by
  have hp : (⟨D.part s,D.part_mem s⟩:M)=∑ i∈s,(⟨D.piece i,D.piece_mem i⟩:M) := by
    apply Subtype.ext
    change D.part s=M.toStarSubalgebra.subtype _
    rw [map_sum]
    rfl
  rw [hp,map_sum]
  have he (i : ι) : τ ⟨D.piece i,D.piece_mem i⟩=(Fintype.card ι:ℂ)⁻¹ :=
    (trace_equivalent M τ hτ D.base_mem (D.piece_mem i) (D.base_equiv_piece i)).symm.trans
      (partition_base_trace M τ hτ D hone)
  simp_rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,←Complex.ofReal_natCast,
    ←Complex.ofReal_inv,←Complex.ofReal_mul,Complex.ofReal_re,div_eq_mul_inv]

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

lemma dimension_le_trace (hone : τ 1=1) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) :
    dimension M hfac hd e≤(τ ⟨e,heM⟩).re := by
  apply le_of_tendsto (lower_tendsto_dimension M hfac hd he)
  apply Eventually.of_forall
  intro n
  let D := partition M hfac hd n
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have ht := trace_subEquivalent M τ hτ (D.part_mem s) heM hse
  rw [partition_part_trace M τ hτ D hone s,hs] at ht
  change ((D.rank e:ℝ)/(2:ℝ)^n)≤_
  simpa only [D,cardinality,Nat.cast_pow,Nat.cast_ofNat] using ht

theorem trace_projection_dimension_oai [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (hone : τ 1=1) {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    (τ ⟨e,heM⟩).re=dimension M hfac hd e := by
  apply le_antisymm _ (dimension_le_trace M τ hτ hfac hd hone heM he)
  have hc := dimension_le_trace M τ hτ hfac hd hone (M.sub_mem M.one_mem heM) he.one_sub
  have hsub : (⟨1-e,M.sub_mem M.one_mem heM⟩:M)=1-⟨e,heM⟩ := rfl
  rw [hsub,map_sub,hone,Complex.sub_re,Complex.one_re,
    dimension_complement M hfac hd hfin heM he] at hc
  linarith

end Kadison.TraceDimension

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TraceDimension.trace_projection_dimension_oai.{u_1} := @OAI.Kadison.TraceDimension.trace_projection_dimension_oai.{u_1}
