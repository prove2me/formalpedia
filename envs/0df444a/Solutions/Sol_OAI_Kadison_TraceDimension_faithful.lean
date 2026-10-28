-- Prove2me | solution 1 for OAI.Kadison.TraceDimension.faithful
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:46:30.28254+00:00
-- url     : https://prove2.me/submissions/4415f0b1-b932-46ee-a777-6f149b53270e

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_DyadicPartition_exists_base_subEquivalent
import Theorems.Thm_OAI_Kadison_PartialIsometryOrder_EqualPartition_card_le_of_part_subEquivalent
import Theorems.Thm_OAI_Kadison_TraceDimension_trace_projection_dimension

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

local instance instDecidableEq_r0e9c00_1 : DecidableEq ι := Classical.decEq ι
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

local instance equalPartitionSumsDecidableEq_r0e9c00_1 : DecidableEq ι := Classical.decEq ι
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

local instance partitionRankDecidableEq_r0e9c00_1 : DecidableEq ι := Classical.decEq ι
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
-- module Solutions.OAIQ039_CM.Commutator_ProjectionFaithfulFunctional
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

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionFaithfulFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem positive_eq_zero_of_projection_faithful
    (hfaith : ∀ p : M,IsStarProjection (p : H →L[ℂ] H) → τ p=0 → p=0)
    (a : M) (ha : 0≤a) (hτa : τ a=0) : a=0 := by
  let c : ℝ := ‖a‖+1
  have hc : 0 < c := by dsimp [c]; positivity
  let b : M := ((c⁻¹:ℝ):ℂ) • a
  have hb : 0≤b := smul_nonneg (show (0:ℂ)≤(c⁻¹:ℝ) from by exact_mod_cast inv_nonneg.mpr hc.le) ha
  have hbn : ‖b‖≤1 := by
    have he : ‖a‖ ≤ c := by dsimp [c]; linarith
    have hh : c⁻¹ * ‖a‖≤1 := by
      simpa only [inv_mul_cancel₀ hc.ne'] using mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hc.le)
    simpa only [b,norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)] using hh
  have hb1 : b≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn
  have hτb : τ b=0 := by simp only [b,map_smul,hτa,smul_zero]
  let B (n : ℕ) : M := ⟨Polar.dyadicRemainder (b:H →L[ℂ] H) n,
    Polar.dyadicRemainder_mem M b.property n⟩
  let P (n : ℕ) : M := ⟨Polar.halfCut (B n : H →L[ℂ] H),Polar.halfCut_mem M (B n).property⟩
  have hBpos (n : ℕ) : 0≤B n := (Polar.dyadicRemainder_bounds hb hb1 n).1
  have hPproj (n : ℕ) : IsStarProjection (P n : H →L[ℂ] H) := Polar.isProjection_halfCut _
  have hnext (n : ℕ) : B (n+1)=B n+B n-P n := rfl
  have hPpos (n : ℕ) : 0≤P n := (hPproj n).nonneg
  have hPτ (n : ℕ) : τ (B n)=0 ∧ P n=0 := by
    induction n with
    | zero =>
      have hz : τ (B 0)=0 := hτb
      have hsmall : τ (P 0)≤0 := by
        have h : τ (P 0)≤τ (B 0+B 0) := τ.monotone
          (show P 0≤B 0+B 0 from sub_nonneg.mp (hnext 0 ▸ hBpos 1))
        simpa only [map_add,hz,zero_add] using h
      exact ⟨hz,hfaith (P 0) (hPproj 0) (le_antisymm hsmall (τ.map_nonneg (hPpos 0)))⟩
    | succ n ih =>
      have hz : τ (B (n+1))=0 := by rw [hnext,ih.2,sub_zero,map_add,ih.1,zero_add]
      have hsmall : τ (P (n+1))≤0 := by
        have h : τ (P (n+1))≤τ (B (n+1)+B (n+1)) := τ.monotone
          (show P (n+1)≤B (n+1)+B (n+1) from
          sub_nonneg.mp (hnext (n+1) ▸ hBpos (n+2)))
        simpa only [map_add,hz,zero_add] using h
      exact ⟨hz,hfaith (P (n+1)) (hPproj (n+1))
        (le_antisymm hsmall (τ.map_nonneg (hPpos (n+1))))⟩
  have hstep (n : ℕ) : Polar.dyadicStep (b:H →L[ℂ] H) n=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have he : Polar.halfCut (Polar.dyadicRemainder (b:H →L[ℂ] H) i)=0 :=
      congrArg (fun a : M => (a:H →L[ℂ] H)) (hPτ i).2
    rw [he,smul_zero]
  have hnorm : ‖b‖≤0 := by
    apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x:=‖b‖))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num))
    apply Eventually.of_forall
    intro n
    have h := Polar.dyadicStep_norm_error hb hb1 n
    change ‖(b:H →L[ℂ] H)‖≤2⁻¹^n
    simpa only [hstep,sub_zero] using h
  have hzero : b=0 := norm_le_zero_iff.mp hnorm
  have hc0 : ((c⁻¹:ℝ):ℂ)≠0 := by exact_mod_cast inv_ne_zero hc.ne'
  exact (smul_eq_zero.mp hzero).resolve_left hc0

end Kadison.ProjectionFaithfulFunctional

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalizedTrace
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

namespace Kadison.TraceDimension

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable (hfac : FactorCorner.IsFactor M) (hd : DiffuseProjection.HasNoMinimalProjections M)

variable (hfin : IsFiniteAlgebra M) (hone : τ 1=1)

include hτ hfac hd hfin hone

theorem positive_faithful (a : M) (ha : 0≤a) (hzero : τ a=0) : a=0 := by
  apply ProjectionFaithfulFunctional.positive_eq_zero_of_projection_faithful M τ _ a ha hzero
  intro p hp hτp
  have he := trace_projection_dimension M τ hτ hfac hd hfin hone p.property hp
  rw [hτp,Complex.zero_re] at he
  apply Subtype.ext
  exact (dimension_eq_zero_iff M hfac hd hfin p.property hp).mp he.symm

theorem faithful_oai (a : M) (hzero : τ (star a*a)=0) : a=0 := by
  have he := positive_faithful M τ hτ hfac hd hfin hone (star a*a) (star_mul_self_nonneg a) hzero
  apply norm_eq_zero.mp
  have hn := congrArg norm he
  rw [CStarRing.norm_star_mul_self,norm_zero] at hn
  nlinarith [norm_nonneg a]

end Kadison.TraceDimension

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TraceDimension.faithful_oai.{u_1} := @OAI.Kadison.TraceDimension.faithful_oai.{u_1}
