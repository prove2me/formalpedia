-- Prove2me | solution 1 for OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_difference
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:41:34.168255+00:00
-- url     : https://prove2.me/submissions/ce24f922-79e7-45c5-a629-495a295b30e3

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_lower_orthogonal_add_le
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_lower_orthogonal_add_upper

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

local instance partitionRankDecidableEq_r51289b_1 : DecidableEq ι := Classical.decEq ι
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

local instance instDecidableEq_3_r51289b_1 : DecidableEq ι := Classical.decEq ι
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

lemma dyadic_error_tendsto : Tendsto (fun n : ℕ => (2:ℝ)/2^n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
    (by norm_num : (1/2:ℝ)<1)).const_mul 2
  simpa only [div_pow,one_pow,mul_one_div,mul_zero] using h

include hfin in
theorem dimension_orthogonal_add {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    dimension M hfac hd (e+f)=dimension M hfac hd e+dimension M hfac hd f := by
  have heT := lower_tendsto_dimension M hfac hd he
  have hfT := lower_tendsto_dimension M hfac hd hf
  have hefT := lower_tendsto_dimension M hfac hd (he.add hf hef)
  apply le_antisymm
  · have ht := (heT.add hfT).add dyadic_error_tendsto
    rw [add_zero] at ht
    exact le_of_tendsto_of_tendsto hefT ht (Eventually.of_forall
      (lower_orthogonal_add_upper M hfac hd hfin heM hfM he hf hef))
  · exact le_of_tendsto_of_tendsto (heT.add hfT) hefT (Eventually.of_forall
      (lower_orthogonal_add_le M hfac hd hfin heM hfM he hf hef))

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

include hfin in
lemma dimension_difference_oai {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hfe : f≤e) :
    dimension M hfac hd (e-f)=dimension M hfac hd e-dimension M hfac hd f := by
  have hfe' := (hf.le_iff_mul_eq_left he).mp hfe
  have hp := hf.sub_of_mul_eq_left he hfe'
  have ho : f*(e-f)=0 := by rw [mul_sub,hfe',hf.isIdempotentElem.eq,sub_self]
  have h := dimension_orthogonal_add M hfac hd hfin hfM (M.sub_mem heM hfM) hf hp ho
  have ha : f+(e-f)=e := by abel
  rw [ha] at h
  linarith

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_difference_oai.{u_1} := @OAI.Kadison.PartialIsometryOrder.DyadicPartition.dimension_difference_oai.{u_1}
