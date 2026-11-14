-- Prove2me | solution 1 for OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:47:08.963207+00:00
-- url     : https://prove2.me/submissions/9f4ee120-369b-4d24-a0f6-f5afacddd10f

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke035
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_EliminationChain_predecessor_root_information
import Theorems.Thm_OAI_DukePrimeDegree_RootPrefixBox_ae_normalized_uncentered_eq_regularLeaf

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
namespace PrimeDegreePackets


lemma finiteShannon_nonneg {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (h1 : ∑ a, p a = 1) : 0 ≤ finiteShannon p := by
  classical
  apply Finset.sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  rw [← h1]
  exact Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)

lemma negMulLog_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) :
    Real.negMulLog p ≤ -p * Real.log q + q-p := by
  by_cases hp0 : p = 0
  · simp [hp0,hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < q := lt_of_le_of_ne hq (fun h => hp0 (hzero h.symm))
  have H := mul_le_mul_of_nonneg_right
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  rw [Real.log_div hp0 hq'.ne'] at H
  have heq : (p/q-1)*q = p-q := by field_simp
  have heq' : (p/q*(Real.log p-Real.log q))*q = p*(Real.log p-Real.log q) := by
    field_simp
  rw [heq,heq'] at H
  unfold Real.negMulLog
  linarith

 
theorem finiteShannon_le_cross {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1)
    (hzero : ∀ a, q a = 0 → p a = 0) :
    finiteShannon p ≤ ∑ a, -p a * Real.log (q a) := by
  calc
    finiteShannon p ≤ ∑ a, (-p a * Real.log (q a) + q a-p a) :=
      Finset.sum_le_sum (fun a _ => negMulLog_le_cross (hp a) (hq a) (hzero a))
    _ = ∑ a, -p a * Real.log (q a) := by
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1]
      ring

 
theorem finiteShannon_joint_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    finiteShannon p ≤ finiteShannon (fun a => ∑ b, p (a,b)) +
      finiteShannon (fun b => ∑ a, p (a,b)) := by
  classical
  let r : α → ℝ := fun a => ∑ b, p (a,b)
  let c : β → ℝ := fun b => ∑ a, p (a,b)
  have hr a : 0 ≤ r a := Finset.sum_nonneg fun _ _ => hp _
  have hc b : 0 ≤ c b := Finset.sum_nonneg fun _ _ => hp _
  have hr1 : ∑ a, r a = 1 := by simpa [r,Fintype.sum_prod_type] using hp1
  have hc1 : ∑ b, c b = 1 := by
    change (∑ b, ∑ a, p (a,b)) = 1
    rw [Finset.sum_comm]
    simpa only [r] using hr1
  have hpr a b : p (a,b) ≤ r a := Finset.single_le_sum
    (fun j _ => hp (a,j)) (Finset.mem_univ b)
  have hpc a b : p (a,b) ≤ c b := Finset.single_le_sum
    (fun i _ => hp (i,b)) (Finset.mem_univ a)
  have hq1 : ∑ z : α × β, r z.1 * c z.2 = 1 := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,hc1,mul_one,hr1]
  have H := finiteShannon_le_cross hp (fun z => mul_nonneg (hr z.1) (hc z.2)) hp1 hq1
    (fun z hz => by
      rcases mul_eq_zero.mp hz with h | h
      · exact le_antisymm (h ▸ hpr z.1 z.2) (hp z)
      · exact le_antisymm (h ▸ hpc z.1 z.2) (hp z))
  refine H.trans_eq ?_
  have heq (a : α) (b : β) : -p (a,b)*Real.log (r a*c b) =
      -p (a,b)*Real.log (r a) + -p (a,b)*Real.log (c b) := by
    by_cases h : p (a,b) = 0
    · simp [h]
    have hpos := lt_of_le_of_ne (hp (a,b)) (Ne.symm h)
    rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le hpos (hpr a b)))
      (ne_of_gt (lt_of_lt_of_le hpos (hpc a b))),mul_add]
  simp only [Fintype.sum_prod_type,heq,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => -p (a,b)*Real.log (c b))]
  congr 1
  · simp only [finiteShannon,Real.negMulLog,r,← Finset.sum_mul,Finset.sum_neg_distrib]
  · simp only [finiteShannon,Real.negMulLog,c,← Finset.sum_mul,Finset.sum_neg_distrib]

 
theorem finiteShannon_le_log_card {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    finiteShannon p ≤ Real.log (Fintype.card α) := by
  classical
  have hn : 0 < Fintype.card α := by
    by_contra hn
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    simp at hp1
  have hn' : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have H := finiteShannon_le_cross hp
    (q := fun _ => (Fintype.card α : ℝ)⁻¹) (fun _ => by positivity) hp1
    (by simp [hn']) (fun _ h => (inv_ne_zero hn' h).elim)
  refine H.trans_eq ?_
  rw [← Finset.sum_mul,Finset.sum_neg_distrib,hp1,Real.log_inv]
  ring


lemma observation_distribution_sum {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    ∑ a, μ.real {y | P y = a} = 1 := by
  have hd : Pairwise (fun a b => Disjoint {y | P y = a} {y | P y = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hab (hy.symm.trans hy')
  rw [← measureReal_iUnion_fintype hd hP]
  have heq : (⋃ a, {y | P y = a}) = Set.univ := by ext; simp
  rw [heq]; simp [Measure.real]

lemma observationEntropy_nonneg {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    0 ≤ observationEntropy μ P :=
  finiteShannon_nonneg (fun _ => measureReal_nonneg) (observation_distribution_sum μ P hP)

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal
namespace PrimeDegreePackets

lemma observationEntropy_equiv {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) (P : Y → α) (e : α ≃ β) :
    observationEntropy μ (fun y => e (P y)) = observationEntropy μ P := by
  classical
  unfold observationEntropy finiteShannon
  rw [← e.sum_comp]
  simp only [Equiv.apply_eq_iff_eq]

lemma observation_joint_row {Y α β : Type*} [MeasurableSpace Y]
    [Fintype β] (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (a : α) :
    ∑ b, μ.real {y | (P y,Q y) = (a,b)} = μ.real {y | P y = a} := by
  have hd : Pairwise (fun b c => Disjoint {y | (P y,Q y) = (a,b)}
      {y | (P y,Q y) = (a,c)}) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro y hy hz
    exact hbc ((congrArg Prod.snd hy).symm.trans (congrArg Prod.snd hz))
  have hm b : MeasurableSet {y | (P y,Q y) = (a,b)} := by
    simpa only [Prod.mk.injEq,Set.ofPred_and] using (hP a).inter (hQ b)
  rw [← measureReal_iUnion_fintype hd hm]
  congr 1
  ext y
  simp

 
theorem observationEntropy_joint_le {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ (fun y => (P y,Q y)) ≤
      observationEntropy μ P + observationEntropy μ Q := by
  have hm (z : α × β) : MeasurableSet {y | (P y,Q y) = z} := by
    rcases z with ⟨a,b⟩
    simpa only [Prod.mk.injEq,Set.ofPred_and] using (hP a).inter (hQ b)
  have H := finiteShannon_joint_le (fun z =>
    measureReal_nonneg (μ := μ) (s := {y | (P y,Q y) = z}))
    (observation_distribution_sum μ (fun y => (P y,Q y)) hm)
  have hrow := observation_joint_row μ P Q hP hQ
  have hcol (b : β) : (∑ a, μ.real {y | (P y,Q y) = (a,b)}) = μ.real {y | Q y = b} := by
    convert observation_joint_row μ Q P hQ hP b using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext a
    congr 1
    ext y
    simp only [Prod.mk.injEq,and_comm]
  simpa only [hrow,hcol,observationEntropy] using H

lemma observationEntropy_comp_preserving {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (μ : Measure Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) {S : Y → Y} (hS : MeasurePreserving S μ μ) :
    observationEntropy μ (fun y => P (S y)) = observationEntropy μ P := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (μ (S ⁻¹' {y | P y = a})).toReal = (μ {y | P y = a}).toReal
  rw [hS.measure_preimage (hP a).nullMeasurableSet]


lemma orbitName_measurable_fiber {Y α : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | orbitName T P N y = a} := by
  have heq : {y | orbitName T P N y = a} = ⋂ j : Fin N, {y | P (T^[j] y) = a j} := by
    ext y
    simp [orbitName,funext_iff]
  rw [heq]
  exact MeasurableSet.iInter fun j => (hP (a j)).preimage (hT.iterate j)

lemma orbitName_add {Y α : Type*} (T : Y → Y) (P : Y → α) (m n : ℕ) :
    orbitName T P (m+n) = fun y => (Fin.appendEquiv m n)
      (orbitName T P m y,orbitName T P n (T^[m] y)) := by
  funext y
  apply (Fin.appendEquiv m n).symm.injective
  ext i
  · simp [orbitName]
  · simp only [Fin.appendEquiv_symm_apply,orbitName,
      Equiv.symm_apply_apply,Fin.val_natAdd]
    rw [Function.iterate_add_apply,← Function.iterate_add_apply,
      ← Function.iterate_add_apply,Nat.add_comm]

 
theorem orbitEntropy_subadditive {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Subadditive (fun N => observationEntropy μ (orbitName T P N)) := by
  intro m n
  change observationEntropy μ (orbitName T P (m+n)) ≤
    observationEntropy μ (orbitName T P m) + observationEntropy μ (orbitName T P n)
  rw [orbitName_add,observationEntropy_equiv]
  have H := observationEntropy_joint_le μ (orbitName T P m)
    (fun y => orbitName T P n (T^[m] y))
    (orbitName_measurable_fiber hT.measurable hP m)
    (fun a => (orbitName_measurable_fiber hT.measurable hP n a).preimage
      (hT.measurable.iterate m))
  rw [observationEntropy_comp_preserving μ _
    (orbitName_measurable_fiber hT.measurable hP n) (hT.iterate m)] at H
  exact H



theorem tendsto_observationEntropyRate {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Tendsto (fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ)) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  have h := orbitEntropy_subadditive μ hT P hP
  have hb : BddBelow (Set.range (fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ))) := by
    refine ⟨0,?_⟩
    rintro _ ⟨N,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _
      (orbitName_measurable_fiber hT.measurable hP N)) (Nat.cast_nonneg N)
  simpa only [Subadditive.lim,observationEntropyRate] using h.tendsto_lim hb



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

lemma negMulLog_sum_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Real.negMulLog (∑ i, p i) ≤ ∑ i, Real.negMulLog (p i) := by
  rw [Real.negMulLog, ← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases h0 : p i = 0
  · simp [h0]
  have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm h0)
  have hs : p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  exact mul_le_mul_of_nonpos_left (Real.log_le_log hi hs) (neg_nonpos.mpr (hp i))

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Filter Set
namespace PrimeDegreePackets

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]



lemma measurable_kernel_real (κ : Kernel Z Y) {S : Set Y} (hS : MeasurableSet S) :
    Measurable (fun z => (κ z).real S) := (κ.measurable_coe hS).ennreal_toReal

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma continuous_finiteShannon {α : Type*} [Fintype α] :
    Continuous (finiteShannon (α := α)) := by
  unfold finiteShannon
  exact continuous_finsetSum _ (fun a _ => Real.continuous_negMulLog.comp (continuous_apply a))

lemma measurable_kernel_entropy {Z Y α : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype α] (κ : Kernel Z Y) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Measurable (fun z => observationEntropy (κ z) P) := by
  exact continuous_finiteShannon.measurable.comp (measurable_pi_iff.mpr
    (fun a => measurable_kernel_real κ (hP a)))

lemma integrable_kernel_entropy {Z Y α : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [Fintype α] (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Integrable (fun z => observationEntropy (κ z) P) τ := by
  apply Integrable.mono' (integrable_const (Real.log (Fintype.card α)))
    (measurable_kernel_entropy κ P hP).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (observationEntropy_nonneg (κ z) P hP)]
    exact finiteShannon_le_log_card (fun a => measureReal_nonneg)
      (observation_distribution_sum (κ z) P hP)

lemma ae_nonnull_fiber {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) (Q : Z → ι) :
    ∀ᵐ z ∂τ, τ {z' | Q z' = Q z} ≠ 0 := by
  have H (i : ι) : ∀ᵐ z ∂τ, Q z = i → τ {z' | Q z' = i} ≠ 0 := by
    by_cases hi : τ {z' | Q z' = i} = 0
    · apply ae_iff.mpr
      simp only [hi, ne_eq, not_true_eq_false, imp_false, not_not]
    · exact ae_of_all _ (fun _ _ => hi)
  filter_upwards [ae_all_iff.mpr H] with z hz
  exact hz (Q z) rfl



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma integrable_finite_values {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) [IsFiniteMeasure τ] (Q : Z → ι)
    (hQ : ∀ i, MeasurableSet {z | Q z = i}) (c : ι → ℝ) :
    Integrable (fun z => c (Q z)) τ := by
  have H : (fun z => c (Q z)) = fun z =>
      ∑ i, {z | Q z = i}.indicator (fun _ => c i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [H]
  exact integrable_finsetSum _ (fun i _ => (integrable_const (c i)).indicator (hQ i))

lemma integral_finite_values {Z ι : Type*} [MeasurableSpace Z] [Fintype ι]
    (τ : Measure Z) [IsFiniteMeasure τ] (Q : Z → ι)
    (hQ : ∀ i, MeasurableSet {z | Q z = i}) (c : ι → ℝ) :
    (∫ z, c (Q z) ∂τ) = ∑ i, τ.real {z | Q z = i} * c i := by
  have H : (fun z => c (Q z)) = fun z =>
      ∑ i, {z | Q z = i}.indicator (fun _ => c i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [H,integral_finsetSum _ (fun i _ => (integrable_const (c i)).indicator (hQ i))]
  simp only [integral_indicator_const _ (hQ _), smul_eq_mul]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootSubgroups
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical

open scoped Topology Classical Matrix


namespace PrimeDegreePackets

lemma observationEntropy_le_joint {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ P ≤ observationEntropy μ (fun y => (P y,Q y)) := by
  unfold observationEntropy finiteShannon
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro a _
  dsimp only
  rw [← observation_joint_row μ P Q hP hQ a]
  exact negMulLog_sum_le _ (fun _ => measureReal_nonneg)

lemma observationEntropy_joint_eq_of_refines {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (h : ∀ x y, Q x = Q y → P x = P y) :
    observationEntropy μ (fun y => (P y,Q y)) = observationEntropy μ Q := by
  unfold observationEntropy finiteShannon
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only
  by_cases hb : ∃ x, Q x = b
  · obtain ⟨x,hx⟩ := hb
    have he (a : α) : {y | (P y,Q y) = (a,b)} =
        if a = P x then {y | Q y = b} else ∅ := by
      split_ifs with ha
      · subst a
        ext y
        simp only [mem_ofPred_eq,Prod.mk.injEq]
        exact ⟨And.right,fun hy => ⟨h y x (hy.trans hx.symm),hy⟩⟩
      · ext y
        simp only [mem_ofPred_eq,Prod.mk.injEq,mem_empty_iff_false,iff_false,not_and]
        intro hya hyb
        exact ha (hya.symm.trans (h y x (hyb.trans hx.symm)))
    simp only [he]
    simp only [apply_ite,measureReal_empty,Real.negMulLog_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  · have hQb : {y | Q y = b} = ∅ := by
      ext y
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact fun hy => hb ⟨y,hy⟩
    have he (a : α) : {y | (P y,Q y) = (a,b)} = ∅ := by
      ext y
      simp only [mem_ofPred_eq,Prod.mk.injEq,mem_empty_iff_false,iff_false,not_and]
      exact fun _ hy => hb ⟨y,hy⟩
    simp only [he,hQb,measureReal_empty,Real.negMulLog_zero,Finset.sum_const_zero]

lemma observationEntropy_le_of_refines {Y α β : Type*} [MeasurableSpace Y]
    [Fintype α] [Fintype β] (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (h : ∀ x y, Q x = Q y → P x = P y) :
    observationEntropy μ P ≤ observationEntropy μ Q := by
  exact (observationEntropy_le_joint μ P Q hP hQ).trans_eq
    (observationEntropy_joint_eq_of_refines μ P Q h)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_GenericLatticeStabilizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A generic lattice stabilizer cannot have an identity column -/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem stabilizer_trivial_of_identity_column {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (g : G n) (hfix : rightAction x g = x) (k : Fin n)
    (hcol : ∀ r, g.val r k = (1 : Matrix (Fin n) (Fin n) ℝ) r k) : g = 1 := by
  have hvec (v : Fin n → ℝ) (hv : v ∈ pointLattice x) : v ᵥ* g.val = v := by
    let w := v ᵥ* g.val - v
    have hw : w ∈ pointLattice x := by
      apply Submodule.sub_mem _ _ hv
      simpa only [hfix] using vecMul_mem_pointLattice_rightAction x g v hv
    have he : (v ᵥ* g.val) k = v k := by
      calc
        _ = (v ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ)) k := by
          change (∑ r, v r * g.val r k) = ∑ r, v r * (1 : Matrix (Fin n) (Fin n) ℝ) r k
          simp_rw [hcol]
        _ = _ := by rw [Matrix.vecMul_one]
    have hwk : w k = 0 := by change (v ᵥ* g.val) k - v k = 0; exact sub_eq_zero.mpr he
    have hw0 : w = 0 := by
      by_contra h
      exact hx w hw h k hwk
    exact sub_eq_zero.mp hw0
  induction x using Quotient.inductionOn with
  | h q =>
    have hm : q.val * g.val = q.val := by
      ext r s
      have hmem : q.val r ∈ pointLattice (Quotient.mk _ q) := by
        rw [pointLattice_mk, ← integerRowMap_range]
        refine ⟨Pi.single r 1, ?_⟩
        ext j
        simp [integerRowMap_apply, Matrix.vecMul, dotProduct, Pi.single_apply]
      exact congrFun (hvec (q.val r) hmem) s
    have hgroup : q * g = q := Subtype.ext hm
    exact mul_left_cancel (hgroup.trans (mul_one q).symm)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_UnipotentFreeness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Freeness of the full positive unipotent action

At the generic lattices already supplied by diagonal recurrence, no
nonzero lattice vector has a zero coordinate. A stabilizer element with
one identity column must therefore fix every lattice vector, so is the
identity. In particular all positive-root groups act freely there,
simultaneously.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem positiveRootPattern_stabilizer_trivial {d : ℕ}
    (x : X (d + 1)) (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (S : Finset (Fin (d + 1) × Fin (d + 1))) (hpos : ∀ p ∈ S, p.1 < p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) (hfix : rightAction x g = x) :
    g = 1 := by
  apply stabilizer_trivial_of_identity_column x hx g hfix 0
  intro r
  apply hg r 0
  intro h
  exact (Fin.not_lt_zero r) (hpos (r, 0) h)

theorem ae_positiveRootPattern_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ (S : Finset (Fin (d + 1) × Fin (d + 1))),
      (∀ p ∈ S, p.1 < p.2) → ∀ g : G (d + 1),
        PositiveRootPattern S g → rightAction x g = x → g = 1 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx S hpos g hg hfix
  exact positiveRootPattern_stabilizer_trivial x hx S hpos g hg hfix

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalShannon
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite conditional entropy, including zero-mass cells

These algebraic chain rules are used to compare finite observations with
the expanding leaf partitions in the metric entropy calculation.
-/

noncomputable section
open scoped BigOperators

namespace PrimeDegreePackets

lemma finiteShannon_mul {α : Type*} [Fintype α] (r : ℝ) (p : α → ℝ) :
    finiteShannon (fun a => r * p a) =
      Real.negMulLog r * (∑ a, p a) + r * finiteShannon p := by
  simp only [finiteShannon, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma finiteShannon_mass_decomposition {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    finiteShannon p = Real.negMulLog (∑ a, p a) +
      (∑ a, p a) * finiteShannon (fun a => p a / (∑ b, p b)) := by
  classical
  let r := ∑ a, p a
  by_cases hr : r = 0
  · have hp0 : ∀ a, p a = 0 := by
      intro a
      have h := Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
      change p a ≤ r at h
      exact le_antisymm (hr ▸ h) (hp a)
    simp only [hp0, finiteShannon, Finset.sum_const_zero, Real.negMulLog_zero,
      zero_div, zero_mul, zero_add]
  · have hs : ∑ a, p a / r = 1 := by rw [← Finset.sum_div]; exact div_self hr
    have heq : (fun a => r * (p a / r)) = p := by
      funext a
      exact mul_div_cancel₀ (p a) hr
    have h := finiteShannon_mul r (fun a => p a / r)
    rw [heq, hs, mul_one] at h
    exact h

lemma finiteShannon_fst_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon (fun a => ∑ b, p (a,b)) ≤ finiteShannon p := by
  simpa only [finiteShannon, Fintype.sum_prod_type] using
    Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      negMulLog_sum_le (fun b => p (a,b)) (fun b => hp (a,b)))

lemma finiteShannon_joint_decomposition {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon p = finiteShannon (fun a => ∑ b, p (a,b)) +
      ∑ a, (∑ b, p (a,b)) *
        finiteShannon (fun b => p (a,b) / (∑ c, p (a,c))) := by
  have H := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ =>
    finiteShannon_mass_decomposition (fun b => p (a,b)) (fun b => hp (a,b)))
  simpa only [finiteShannon, Fintype.sum_prod_type, Finset.sum_add_distrib] using H

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalObservations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional entropy of finite observations

The conditioning variable is the last argument. All identities below use
the actual distribution under `μ`, including its zero-mass cells.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β γ : Type*} [MeasurableSpace Y]

lemma observationPair_measurable_fiber (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    ∀ z, MeasurableSet {y | (P y,Q y) = z} := by
  rintro ⟨a,b⟩
  simpa only [Prod.mk.injEq, Set.ofPred_and] using (hP a).inter (hQ b)

lemma observationEntropy_swap [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (Q : Y → β) :
    observationEntropy μ (fun y => (P y,Q y)) =
      observationEntropy μ (fun y => (Q y,P y)) := by
  exact (observationEntropy_equiv μ (fun y => (P y,Q y)) (Equiv.prodComm α β)).symm

lemma observationEntropy_assoc [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) (P : Y → α) (Q : Y → β) (R : Y → γ) :
    observationEntropy μ (fun y => ((P y,Q y),R y)) =
      observationEntropy μ (fun y => (P y,(Q y,R y))) := by
  exact (observationEntropy_equiv μ (fun y => ((P y,Q y),R y))
    (Equiv.prodAssoc α β γ)).symm

lemma conditionalObservationEntropy_nonneg [Fintype α] [Fintype β]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    0 ≤ conditionalObservationEntropy μ P Q := by
  have H := finiteShannon_fst_le
    (fun z : β × α => μ.real {y | (Q y,P y) = z}) (fun _ => measureReal_nonneg)
  simp only [observation_joint_row μ Q P hQ hP] at H
  exact sub_nonneg.mpr H

lemma conditionalObservationEntropy_le [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q ≤ observationEntropy μ P := by
  have H := observationEntropy_joint_le μ Q P hQ hP
  unfold conditionalObservationEntropy
  linarith

lemma conditionalObservationEntropy_chain [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) (P : Y → α) (R : Y → β) (Q : Y → γ) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) Q =
      conditionalObservationEntropy μ P Q +
      conditionalObservationEntropy μ R (fun y => (Q y,P y)) := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_assoc]
  ring

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationRefinement
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Refining and recoding finite observations -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β γ δ : Type*} [MeasurableSpace Y]

lemma conditionalObservationEntropy_comp_preserving [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    {T : Y → Y} (hT : MeasurePreserving T μ μ) :
    conditionalObservationEntropy μ (fun y => P (T y)) (fun y => Q (T y)) =
      conditionalObservationEntropy μ P Q := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_comp_preserving μ (fun y => (Q y,P y))
    (observationPair_measurable_fiber Q P hQ hP) hT,
    observationEntropy_comp_preserving μ Q hQ hT]

lemma observationEntropy_le_add_conditional [Fintype α] [Fintype β]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropy μ P ≤ observationEntropy μ Q + conditionalObservationEntropy μ P Q := by
  have H := conditionalObservationEntropy_nonneg μ Q P hQ hP
  unfold conditionalObservationEntropy at H ⊢
  rw [observationEntropy_swap μ P Q] at H
  linarith

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalOrbitEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entropy-rate comparison from one-step conditional entropy

The finite-block estimate here is the approximation step needed when
replacing finite observations by successively finer geometric partitions.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y]

lemma observationEntropy_unique [Fintype α] [Unique α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α) :
    observationEntropy μ P = 0 := by
  have hP : P = fun _ => default := funext (fun y => Subsingleton.elim _ _)
  rw [hP]
  simp [observationEntropy, finiteShannon]

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationConditionalProbability
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional probabilities of finite observations

The conditional entropy is the integral of the entropy of the actual
finite conditional distributions. Zero-mass conditioning cells contribute
zero, without requiring arbitrary probability distributions on them.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]

omit [Fintype α] [Fintype β] in
lemma observationConditionalProbability_nonneg
    (μ : Measure Y) (P : Y → α) (Q : Y → β) (a : α) (y : Y) :
    0 ≤ observationConditionalProbability μ P Q a y :=
  div_nonneg measureReal_nonneg measureReal_nonneg

omit [Fintype β] in
lemma observationConditionalProbability_sum
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    {y : Y} (hy : μ {z | Q z = Q y} ≠ 0) :
    ∑ a, observationConditionalProbability μ P Q a y = 1 := by
  have hr : μ.real {z | Q z = Q y} ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hy,measure_ne_top _ _⟩
  simp only [observationConditionalProbability, ← Finset.sum_div,
    observation_joint_row μ Q P hQ hP, div_self hr]

lemma observationConditionalProbability_ae_sum
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    ∀ᵐ y ∂μ, ∑ a, observationConditionalProbability μ P Q a y = 1 := by
  filter_upwards [ae_nonnull_fiber μ Q] with y hy
  exact observationConditionalProbability_sum μ P Q hP hQ hy

theorem conditionalObservationEntropy_eq_sum
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q =
      ∑ b, μ.real {y | Q y = b} *
        finiteShannon (fun a => μ.real {y | (Q y,P y) = (b,a)} /
          μ.real {y | Q y = b}) := by
  have H := finiteShannon_joint_decomposition
    (fun z : β × α => μ.real {y | (Q y,P y) = z}) (fun _ => measureReal_nonneg)
  simp only [observation_joint_row μ Q P hQ hP] at H
  unfold conditionalObservationEntropy observationEntropy
  linarith

theorem conditionalObservationEntropy_eq_integral
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q =
      ∫ y, finiteShannon (fun a => observationConditionalProbability μ P Q a y) ∂μ := by
  rw [conditionalObservationEntropy_eq_sum μ P Q hP hQ]
  symm
  exact integral_finite_values μ Q hQ (fun b => finiteShannon (fun a =>
    μ.real {y | (Q y,P y) = (b,a)} / μ.real {y | Q y = b}))

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationSigmaAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sigma algebra and conditional expectations of finite observations -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace PrimeDegreePackets

variable {Y β : Type*} [mY : MeasurableSpace Y] [Fintype β]

lemma observationSigma_le (Q : Y → β)
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) : observationSigma Q ≤ mY := by
  classical
  rintro s ⟨t,_,rfl⟩
  have heq : Q ⁻¹' t = ⋃ b : t, {y | Q y = b.val} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨Q y,h⟩,rfl⟩, fun ⟨b,h⟩ => h ▸ b.property⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun b => hQ b.val)

omit mY in
lemma stronglyMeasurable_observation_values (Q : Y → β) (c : β → ℝ) :
    StronglyMeasurable[observationSigma Q] (fun y => c (Q y)) := by
  let : MeasurableSpace β := ⊤
  exact ((measurable_of_finite c).comp (comap_measurable Q)).stronglyMeasurable

/-- Equality on the finitely many observation atoms determines all set integrals
over the sigma algebra generated by that observation. -/
lemma setIntegral_eq_of_observation_atoms
    (μ : Measure Y) (Q : Y → β) (hQ : ∀ b, MeasurableSet {y | Q y = b})
    {f g : Y → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hatom : ∀ b, ∫ y in {y | Q y = b}, f y ∂μ = ∫ y in {y | Q y = b}, g y ∂μ)
    {s : Set Y} (hs : MeasurableSet[observationSigma Q] s) :
    ∫ y in s, f y ∂μ = ∫ y in s, g y ∂μ := by
  classical
  obtain ⟨t,_,rfl⟩ := hs
  have heq : Q ⁻¹' t = ⋃ b : t, {y | Q y = b.val} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨Q y,h⟩,rfl⟩, fun ⟨b,h⟩ => h ▸ b.property⟩
  have hd : Pairwise (fun b c : t => Disjoint {y | Q y = b.val} {y | Q y = c.val}) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro y hy hz
    exact hbc (Subtype.ext (hy.symm.trans hz))
  rw [heq, integral_iUnion_fintype (fun b : t => hQ b.val) hd
      (fun _ => hf.integrableOn),
    integral_iUnion_fintype (fun b : t => hQ b.val) hd (fun _ => hg.integrableOn)]
  exact Finset.sum_congr rfl (fun b _ => hatom b.val)

lemma observation_values_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ] (Q : Y → β)
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (f : Y → ℝ) (hf : Integrable f μ)
    (c : β → ℝ)
    (hatom : ∀ b, ∫ y in {y | Q y = b}, c (Q y) ∂μ =
      ∫ y in {y | Q y = b}, f y ∂μ) :
    (fun y => c (Q y)) =ᵐ[μ] μ[f | observationSigma Q] := by
  have hg := integrable_finite_values μ Q hQ c
  apply ae_eq_condExp_of_forall_setIntegral_eq (observationSigma_le Q hQ) hf
  · exact fun _ _ _ => hg.integrableOn
  · intro s hs _
    exact setIntegral_eq_of_observation_atoms μ Q hQ hg hf hatom hs
  · exact (stronglyMeasurable_observation_values Q c).aestronglyMeasurable

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalProbabilityExpectation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification with genuine conditional expectation -/

noncomputable section
open MeasureTheory Set

namespace PrimeDegreePackets

variable {Y α β : Type*} [MeasurableSpace Y] [Fintype β]

omit [Fintype β] in
lemma setIntegral_observationConditionalProbability
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (a : α) (b : β) :
    (∫ y in {y | Q y = b}, observationConditionalProbability μ P Q a y ∂μ) =
      μ.real {y | (Q y,P y) = (b,a)} := by
  have heq : (fun y => observationConditionalProbability μ P Q a y) =ᵐ[μ.restrict {y | Q y = b}]
      (fun _ => μ.real {y | (Q y,P y) = (b,a)} / μ.real {y | Q y = b}) := by
    filter_upwards [ae_restrict_mem (hQ b)] with y hy
    simp only [observationConditionalProbability, hy]
  rw [integral_congr_ae heq, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  by_cases hb : μ.real {y | Q y = b} = 0
  · have hz : μ.real {y | (Q y,P y) = (b,a)} = 0 := by
      apply le_antisymm _ measureReal_nonneg
      have hsub : {y | (Q y,P y) = (b,a)} ⊆ {y | Q y = b} :=
        fun y hy => congrArg Prod.fst hy
      calc
        _ ≤ μ.real {y | Q y = b} :=
          measureReal_mono hsub (measure_ne_top _ _)
        _ = 0 := hb
    rw [hb,hz]
    simp only [zero_div,mul_zero]
  · exact mul_div_cancel₀ _ hb

theorem observationConditionalProbability_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (a : α) :
    observationConditionalProbability μ P Q a =ᵐ[μ]
      μ[({y | P y = a}.indicator (fun _ => (1 : ℝ))) | observationSigma Q] := by
  apply observation_values_ae_eq_condExp μ Q hQ _ ((integrable_const (1 : ℝ)).indicator (hP a))
    (fun b => μ.real {y | (Q y,P y) = (b,a)} / μ.real {y | Q y = b})
  intro b
  change (∫ y in {y | Q y = b}, observationConditionalProbability μ P Q a y ∂μ) = _
  rw [setIntegral_observationConditionalProbability μ P Q hQ a b,
    integral_indicator (hP a), integral_const]
  simp only [measureReal_restrict_apply_univ, measureReal_restrict_apply (hP a), smul_eq_mul, mul_one]
  apply congrArg μ.real
  ext y
  simp only [Prod.mk.injEq, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalSigmaEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite observation entropy conditioned on a sigma algebra -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]

theorem conditionalObservationEntropy_tendsto_sigma
    {β : ℕ → Type*} [∀ n, Fintype (β n)]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a})
    (Q : ∀ n, Y → β n) (hQ : ∀ n b, MeasurableSet {y | Q n y = b})
    (hmono : Monotone (fun n => observationSigma (Q n))) :
    Tendsto (fun n => conditionalObservationEntropy μ P (Q n)) atTop
      (𝓝 (conditionalSigmaEntropy μ P (⨆ n, observationSigma (Q n)))) := by
  let ℱ : Filtration ℕ mY :=
    ⟨fun n => observationSigma (Q n), hmono, fun n => observationSigma_le (Q n) (hQ n)⟩
  let F : ℕ → Y → ℝ := fun n y =>
    finiteShannon (fun a => observationConditionalProbability μ P (Q n) a y)
  let G : Y → ℝ := fun y => finiteShannon (fun a =>
    (μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) | ⨆ n, ℱ n]) y)
  have hFint n : Integrable (F n) μ :=
    integrable_finite_values μ (Q n) (hQ n) (fun b => finiteShannon (fun a =>
      μ.real {y | (Q n y,P y) = (b,a)} / μ.real {y | Q n y = b}))
  have hbound n : ∀ᵐ y ∂μ, ‖F n y‖ ≤ Real.log (Fintype.card α) := by
    filter_upwards [observationConditionalProbability_ae_sum μ P (Q n) hP (hQ n)] with y hy
    have hn := fun a => observationConditionalProbability_nonneg μ P (Q n) a y
    change ‖finiteShannon (fun a => observationConditionalProbability μ P (Q n) a y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteShannon_nonneg hn hy)]
    exact finiteShannon_le_log_card hn hy
  have hcoord (a : α) : ∀ᵐ y ∂μ,
      Tendsto (fun n => observationConditionalProbability μ P (Q n) a y) atTop
        (𝓝 ((μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) | ⨆ n, ℱ n]) y)) := by
    have H := MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ)
      ({z | P z = a}.indicator (fun _ => (1 : ℝ)))
    have heq := ae_all_iff.mpr (fun n =>
      observationConditionalProbability_ae_eq_condExp μ P (Q n) hP (hQ n) a)
    filter_upwards [H,heq] with y hy he
    simpa only [he] using hy
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y) atTop (𝓝 (G y)) := by
    filter_upwards [ae_all_iff.mpr hcoord] with y hy
    have H := continuous_finiteShannon.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hy)
    simpa only [F,G,Function.comp_def] using H
  have H := tendsto_integral_of_dominated_convergence
    (fun _ : Y => Real.log (Fintype.card α)) (fun n => (hFint n).aestronglyMeasurable)
    (integrable_const _) hbound hlim
  have heq n : conditionalObservationEntropy μ P (Q n) = ∫ y, F n y ∂μ :=
    conditionalObservationEntropy_eq_integral μ P (Q n) hP (hQ n)
  simpa only [← heq, conditionalSigmaEntropy, G] using H

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning on more measurable information decreases entropy

Conditional Jensen and the tower property apply directly to the actual
conditional expectations defining finite-observation entropy.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma integrable_negMulLog_of_unit_bounds {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {f : Y → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ y ∂μ, f y ∈ Icc 0 1) :
    Integrable (fun y => Real.negMulLog (f y)) μ := by
  apply (integrable_const (1:ℝ)).mono'
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hf)
  filter_upwards [hb] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg hy.1 hy.2)]
  have H := Real.negMulLog_le_one_sub_self hy.1
  linarith [hy.1]

lemma conditionalProbability_unit_bounds {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) (S : Set Y) (m : MeasurableSpace Y) :
    ∀ᵐ y ∂μ, (μ[S.indicator (fun _ => (1:ℝ)) | m]) y ∈ Icc 0 1 := by
  have hn : 0 ≤ᵐ[μ] S.indicator (fun _ => (1:ℝ)) := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  have hu : ∀ᵐ y ∂μ, S.indicator (fun _ => (1:ℝ)) y ≤ 1 := by
    apply ae_of_all
    intro y
    by_cases hy : y ∈ S <;> simp [hy]
  filter_upwards [condExp_nonneg (m := m) hn,
    condExp_le_nonneg_const (m := m) (show (0:ℝ)≤1 by norm_num) hu] with y hy hz
  exact ⟨hy,hz⟩

theorem conditionalSigmaEntropy_antitone {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    {m n : MeasurableSpace Y} (hmn : m ≤ n) (hn : n ≤ mY) :
    conditionalSigmaEntropy (mY := mY) μ P n ≤ conditionalSigmaEntropy (mY := mY) μ P m := by
  have hm := hmn.trans hn
  let g (a : α) : Y → ℝ := {y | P y=a}.indicator (fun _ => 1)
  have hg a : Integrable (g a) μ := (integrable_const (1:ℝ)).indicator (hP a)
  have hi (s : MeasurableSpace Y) (hs : s ≤ mY) (a : α) :
      Integrable (fun y => Real.negMulLog ((μ[g a | s]) y)) μ :=
    integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono hs).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} s)
  unfold conditionalSigmaEntropy finiteShannon
  rw [integral_finsetSum _ (fun a _ => hi n hn a),
    integral_finsetSum _ (fun a _ => hi m hm a)]
  apply Finset.sum_le_sum
  intro a _
  have hJ := Real.concaveOn_negMulLog.condExp_map_le (μ := μ) (f := μ[g a | n]) hm
    (Real.continuous_negMulLog.upperSemicontinuous.upperSemicontinuousOn _)
    ((conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} n).mono fun _ h => h.1)
    isClosed_Ici integrable_condExp (hi n hn a)
  have hTower := condExp_condExp_of_le (μ := μ) (f := g a) hmn hn
  have hle : (μ[(fun y => Real.negMulLog ((μ[g a | n]) y)) | m]) ≤ᵐ[μ]
      (fun y => Real.negMulLog ((μ[g a | m]) y)) := by
    filter_upwards [hJ,hTower] with y hy ht
    simpa only [Function.comp_def,ht] using hy
  calc
    _ = ∫ y, (μ[(fun z => Real.negMulLog ((μ[g a | n]) z)) | m]) y ∂μ :=
      (integral_condExp hm).symm
    _ ≤ _ := integral_mono_ae integrable_condExp (hi m hm a) hle

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootLongBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Long boxes for the full positive-root group

The ordered root word is injective. Generic arithmetic lattices have
free upper unipotent orbits, so every compact set of full root times
fits into one actual quotient box containing the chosen basepoint.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_upperRoot_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ g ∈ positiveRootGeneratedGroup (allPositiveRoots (d + 1)),
      rightAction x g = x → g = 1 := by
  filter_upwards [ae_positiveRootPattern_stabilizer_trivial d μ hA] with x hx g hg hfix
  exact hx (allPositiveRoots (d + 1)) (fun p hp => (Finset.mem_filter.mp hp).2) g
    (positiveRootGeneratedGroup_pattern _ (allPositiveRoots_closed _) hg) hfix

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FiniteGeneratingObservations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual finite generating observations on countably generated spaces

The observations record finitely many bits of Mathlib's canonical countable
generating family. Thus the entropy approximation hypotheses are supplied by
the measurable space itself, rather than assumed for an arbitrary sequence.
-/

noncomputable section
open MeasureTheory MeasurableSpace Set
open scoped ENNReal

namespace PrimeDegreePackets

lemma observationSigma_comp_le {Y α β : Type*} (P : Y → α) (f : α → β) :
    observationSigma (fun y => f (P y)) ≤ observationSigma P := by
  rintro s ⟨t,_,rfl⟩
  exact ⟨f ⁻¹' t, trivial, rfl⟩

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy along increasing conditioning sigma algebras

The martingale limit applies also when the conditioning includes an
arbitrary transverse coordinate in addition to finite future names.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma finiteShannon_norm_le_card_of_unit_bounds {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, p a ∈ Icc 0 1) :
    ‖finiteShannon p‖ ≤ Fintype.card α := by
  unfold finiteShannon
  calc
    ‖∑ a, Real.negMulLog (p a)‖ ≤ ∑ a, ‖Real.negMulLog (p a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : α, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hp a).1 (hp a).2)]
      have H := Real.negMulLog_le_one_sub_self (hp a).1
      linarith [(hp a).1]
    _ = _ := by simp

theorem conditionalSigmaEntropy_tendsto_iSup {Y α : Type*}
    [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (m : ℕ → MeasurableSpace Y) (hm : Monotone m) (hle : ∀ n, m n ≤ mY) :
    Tendsto (fun n => conditionalSigmaEntropy (mY := mY) μ P (m n)) atTop
      (𝓝 (conditionalSigmaEntropy (mY := mY) μ P (⨆ n, m n))) := by
  let ℱ : Filtration ℕ mY := ⟨m,hm,hle⟩
  let g (a : α) : Y → ℝ := {z | P z=a}.indicator (fun _ => 1)
  let F : ℕ → Y → ℝ := fun n y => finiteShannon (fun a => (μ[g a | m n]) y)
  let G : Y → ℝ := fun y => finiteShannon (fun a => (μ[g a | ⨆ n, m n]) y)
  have hFi n : Integrable (F n) μ := by
    change Integrable (fun y => ∑ a, Real.negMulLog ((μ[g a | m n]) y)) μ
    apply integrable_finsetSum
    intro a _
    exact integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {z | P z=a} (m n))
  have hbound n : ∀ᵐ y ∂μ, ‖F n y‖ ≤ (Fintype.card α:ℝ) := by
    filter_upwards [ae_all_iff.mpr (fun a =>
      conditionalProbability_unit_bounds (mY := mY) μ {z | P z=a} (m n))] with y hy
    exact finiteShannon_norm_le_card_of_unit_bounds _ hy
  have hcoord (a : α) : ∀ᵐ y ∂μ, Tendsto (fun n => (μ[g a | m n]) y) atTop
      (𝓝 ((μ[g a | ⨆ n, m n]) y)) := by
    exact MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (g a)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => F n y) atTop (𝓝 (G y)) := by
    filter_upwards [ae_all_iff.mpr hcoord] with y hy
    have H := continuous_finiteShannon.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hy)
    simpa only [F,G,Function.comp_def] using H
  have H := tendsto_integral_of_dominated_convergence
    (fun _ : Y => (Fintype.card α:ℝ)) (fun n => (hFi n).aestronglyMeasurable)
    (integrable_const _) hbound hlim
  simpa only [conditionalSigmaEntropy,F,G,g] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual quotient boxes for every remaining root subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
  {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
  {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

omit [MeasurableSpace T] [BorelSpace T] in
lemma range_open (B : RootPrefixBox C c hP hfinal g) : IsOpen B.range := B.embedding.isOpen_range

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing a remaining-subgroup leaf at its current coordinate -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingRebase_word (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t u : c.Time) :
    c.remainingWordHomeomorph hP hfinal (c.remainingRebase hP hfinal t u) =
      (c.remainingWordHomeomorph hP hfinal t)⁻¹ * c.remainingWordHomeomorph hP hfinal u :=
  (c.remainingWordHomeomorph hP hfinal).apply_symm_apply _

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixBasedMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable remaining-subgroup leaves based at the sampled point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]

lemma timeParam_rebased (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (g : G n) (s : UpperRootTransverse n × T) (t u : c.Time) :
    C.timeParam c hP hfinal g (s,u) =
      rightAction (C.timeParam c hP hfinal g (s,t))
        (c.word (c.remainingRebase hP hfinal t u)) := by
  rw [C.timeParam_eq_action,C.timeParam_eq_action,rightAction_mul]
  congr 1
  have he := congrArg Subtype.val (c.remainingRebase_word hP hfinal t u)
  change c.word (c.remainingRebase hP hfinal t u) = (c.word t)⁻¹ * c.word u at he
  rw [he,mul_inv_cancel_left]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralConditionalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual conditional measures on bilateral itinerary fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Disintegration of the graph of a measurable map is concentrated on
the corresponding fibers. -/
theorem ae_graph_condKernel_fiber
    {S Y : Type*} [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → S) (hf : Measurable f) :
    let ρ := μ.map (fun y => (f y,y))
    ∀ᵐ s ∂ρ.fst, ∀ᵐ y ∂ρ.condKernel s, f y=s := by
  let ρ := μ.map (fun y => (f y,y))
  have hg : ∀ᵐ z ∂ρ, f z.2=z.1 := by
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall fun _ => rfl
  have hcomp : ∀ᵐ z ∂ρ.fst ⊗ₘ ρ.condKernel, f z.2=z.1 := by
    rwa [Measure.disintegrate]
  exact Measure.ae_ae_of_ae_compProd hcomp

theorem ae_condDistrib_self_fiber
    {S Y : Type*} [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : Y → S) (hf : Measurable f) :
    ∀ᵐ s ∂μ.map f, ∀ᵐ y ∂condDistrib id f μ s, f y=s := by
  have H := ae_graph_condKernel_fiber μ f hf
  change ∀ᵐ s ∂(μ.map (fun y => (f y,y))).fst,
    ∀ᵐ y ∂(μ.map (fun y => (f y,y))).condKernel s, f y=s at H
  have hm : (μ.map (fun y => (f y,y))).fst=μ.map f :=
    Measure.fst_map_prodMk measurable_id
  rw [hm] at H
  simpa only [condDistrib,id_eq] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalMapEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite entropy conditioned on a measurable observation -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_comap_eq_integral
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) =
      ∫ s, observationEntropy (condDistrib id F μ s) P ∂μ.map F := by
  have hc (a : α) :
      μ[({y | P y=a}.indicator (fun _ => (1 : ℝ))) |
        MeasurableSpace.comap F inferInstance] =ᵐ[μ]
        fun y => (condDistrib id F μ (F y)).real {z | P z=a} := by
    have H := condExp_ae_eq_integral_condDistrib_id (μ := μ) hF
      ((integrable_const (μ := μ) (1 : ℝ)).indicator (hP a))
    have hi (s : S) : (∫ z, {y | P y=a}.indicator (fun _ => (1 : ℝ)) z
        ∂condDistrib id F μ s) = (condDistrib id F μ s).real {z | P z=a} := by
      rw [integral_indicator_const _ (hP a)]
      simp only [smul_eq_mul,mul_one]
    simpa only [hi] using H
  have hall := ae_all_iff.mpr hc
  unfold conditionalSigmaEntropy
  calc
    _ = ∫ y, observationEntropy (condDistrib id F μ (F y)) P ∂μ := by
      apply integral_congr_ae
      filter_upwards [hall] with y hy
      unfold observationEntropy
      congr 1
      exact funext hy
    _ = _ := (integral_map hF.aemeasurable
      (integrable_kernel_entropy (μ.map F) (condDistrib id F μ) P hP).aestronglyMeasurable).symm

theorem conditionalSigmaEntropy_comap_nonneg
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    0 ≤ conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) := by
  rw [conditionalSigmaEntropy_comap_eq_integral μ F hF P hP]
  exact integral_nonneg fun s => observationEntropy_nonneg (condDistrib id F μ s) P hP

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ObservationInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable pointwise information of finite observations -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem observationInformation_integrable {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (ν : Measure Y) [IsFiniteMeasure ν] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) : Integrable (observationInformation ν P) ν :=
  integrable_finite_values ν P hP (fun a => -Real.log (ν.real {z | P z=a}))

theorem integral_observationInformation {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (ν : Measure Y) [IsFiniteMeasure ν] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) :
    ∫ y, observationInformation ν P y ∂ν = observationEntropy ν P := by
  calc
    _ = ∑ a, ν.real {y | P y=a} * -Real.log (ν.real {z | P z=a}) :=
      integral_finite_values ν P hP (fun a => -Real.log (ν.real {z | P z=a}))
    _ = _ := by
      unfold observationEntropy finiteShannon
      apply Finset.sum_congr rfl
      intro a _
      simp only [Real.negMulLog_def,neg_mul,mul_neg]

lemma observationInformation_nonneg {Y α : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (P : Y → α) (y : Y) :
    0 ≤ observationInformation ν P y := by
  exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureFiberMeasurability
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional measurability from constancy on conull future fibers

Disintegration supplies the almost-everywhere factorization; no Borel
choice of a representative of every future fiber is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExp_eq_of_conull_fiber_constant
    {Y S : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F) (g : Y → ℝ) (hg : Integrable g μ)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E, F x=F y → g x=g y) :
    μ[g | MeasurableSpace.comap F inferInstance] =ᵐ[μ] g := by
  let ν := condDistrib id F μ
  have hcomp : ν ∘ₘ (μ.map F)=μ := by
    simpa only [ν,Measure.map_id] using
      condDistrib_comp_map hF.aemeasurable aemeasurable_id
  have hgood : ∀ᵐ s ∂μ.map F, ∀ᵐ y ∂ν s, y ∈ E := by
    apply Measure.ae_ae_of_ae_comp
    rwa [hcomp]
  have hgx : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν (F x), y ∈ E :=
    ae_of_ae_map hF.aemeasurable hgood
  have hfx : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν (F x), F y=F x :=
    ae_of_ae_map hF.aemeasurable (ae_condDistrib_self_fiber μ F hF)
  have hc := condExp_ae_eq_integral_condDistrib_id hF hg
  filter_upwards [hc,hE,hgx,hfx] with x hx hxE hyE hyF
  rw [hx]
  calc
    (∫ y, g y ∂ν (F x)) = ∫ _, g x ∂ν (F x) := by
      apply integral_congr_ae
      filter_upwards [hyE,hyF] with y hy hyF
      exact (hconst x hxE y hy hyF.symm).symm
    _ = g x := by simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConullFiberEntropyOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy order from refinement of conull fibers

A finer future observation need only determine a kernel outside a null
set. Its conditional entropy is then at most the kernel-label entropy;
no support of that kernel on the finer future fibers is required.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma condExp_condExp_of_ae_measurable_sets
    {Y : Type*} [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    {m n : MeasurableSpace Y} (hm : m ≤ mY) (hn : n ≤ mY)
    (hsub : ∀ s, MeasurableSet[m] s →
      ∃ t, MeasurableSet[n] t ∧ s =ᵐ[μ] t)
    (f : Y → ℝ) (hf : Integrable f μ) :
    μ[μ[f | n] | m] =ᵐ[μ] μ[f | m] := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm integrable_condExp
    (fun _ _ _ => integrable_condExp.integrableOn) _
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  obtain ⟨t,ht,hst⟩ := hsub s hs
  calc
    (∫ x in s, μ[f | m] x ∂μ) = ∫ x in s, f x ∂μ := setIntegral_condExp hm hf hs
    _ = ∫ x in t, f x ∂μ := setIntegral_congr_set hst
    _ = ∫ x in t, μ[f | n] x ∂μ := (setIntegral_condExp hn hf ht).symm
    _ = ∫ x in s, μ[f | n] x ∂μ := setIntegral_congr_set hst.symm

theorem conditionalSigmaEntropy_le_of_ae_measurable_sets
    {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    {m n : MeasurableSpace Y} (hm : m ≤ mY) (hn : n ≤ mY)
    (hsub : ∀ s, MeasurableSet[m] s →
      ∃ t, MeasurableSet[n] t ∧ s =ᵐ[μ] t) :
    conditionalSigmaEntropy (mY := mY) μ P n ≤ conditionalSigmaEntropy (mY := mY) μ P m := by
  let g (a : α) : Y → ℝ := {y | P y=a}.indicator (fun _ => 1)
  have hg a : Integrable (g a) μ := (integrable_const (1:ℝ)).indicator (hP a)
  have hi (s : MeasurableSpace Y) (hs : s ≤ mY) (a : α) :
      Integrable (fun y => Real.negMulLog ((μ[g a | s]) y)) μ :=
    integrable_negMulLog_of_unit_bounds (mY := mY) μ
      (stronglyMeasurable_condExp.mono hs).aestronglyMeasurable
      (conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} s)
  unfold conditionalSigmaEntropy finiteShannon
  rw [integral_finsetSum _ (fun a _ => hi n hn a),
    integral_finsetSum _ (fun a _ => hi m hm a)]
  apply Finset.sum_le_sum
  intro a _
  have hJ := Real.concaveOn_negMulLog.condExp_map_le (μ := μ) (f := μ[g a | n]) hm
    (Real.continuous_negMulLog.upperSemicontinuous.upperSemicontinuousOn _)
    ((conditionalProbability_unit_bounds (mY := mY) μ {y | P y=a} n).mono fun _ h => h.1)
    isClosed_Ici integrable_condExp (hi n hn a)
  have htower := condExp_condExp_of_ae_measurable_sets (mY := mY) μ hm hn hsub (g a) (hg a)
  have hle : μ[(fun y => Real.negMulLog ((μ[g a | n]) y)) | m] ≤ᵐ[μ]
      fun y => Real.negMulLog ((μ[g a | m]) y) := by
    filter_upwards [hJ,htower] with y hy ht
    simpa only [Function.comp_def,ht] using hy
  calc
    _ = ∫ y, μ[(fun z => Real.negMulLog ((μ[g a | n]) z)) | m] y ∂μ :=
      (integral_condExp hm).symm
    _ ≤ _ := integral_mono_ae integrable_condExp (hi m hm a) hle

/-- The finer observation can carry extra information: only determination
of the coarser label on a conull set is used. -/
theorem conditionalSigmaEntropy_le_of_conull_fibers
    {Y S T α : Type*} [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S] [MeasurableSpace T] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F) (G : Y → T) (hG : Measurable G)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E, F x=F y → G x=G y)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy (mY := mY) μ P (MeasurableSpace.comap F inferInstance) ≤
      conditionalSigmaEntropy (mY := mY) μ P (MeasurableSpace.comap G inferInstance) := by
  apply conditionalSigmaEntropy_le_of_ae_measurable_sets μ P hP hG.comap_le hF.comap_le
  intro s hs
  have hsm : MeasurableSet s := hG.comap_le s hs
  let q := μ[s.indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap F inferInstance]
  have hfix : q =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) := by
    apply condExp_eq_of_conull_fiber_constant μ F hF _
      ((integrable_const (1:ℝ)).indicator hsm) E hE
    intro x hx y hy hxy
    have hg := hconst x hx y hy hxy
    have hmem : x ∈ s ↔ y ∈ s := by
      obtain ⟨A,_,rfl⟩ := hs
      change G x ∈ A ↔ G y ∈ A
      rw [hg]
    change s.indicator (fun _ => (1:ℝ)) x=s.indicator (fun _ => (1:ℝ)) y
    by_cases hxS : x ∈ s
    · simp only [indicator_of_mem hxS,indicator_of_mem (hmem.mp hxS)]
    · simp only [indicator_of_notMem hxS,indicator_of_notMem (fun hyS => hxS (hmem.mpr hyS))]
  have hqm : @Measurable Y ℝ (MeasurableSpace.comap F inferInstance) _ q :=
    stronglyMeasurable_condExp.measurable
  refine ⟨{x | (1/2:ℝ) < q x},measurableSet_lt measurable_const hqm,?_⟩
  filter_upwards [hfix] with x hx
  apply propext
  show x ∈ s ↔ (1/2:ℝ) < q x
  rw [hx]
  by_cases hsx : x ∈ s <;> norm_num [hsx]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableShannonInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable information for the countable return observations

The summable atom estimates for return refinements give the actual
integrable information function, and bound every finite recoding.
-/

noncomputable section
open MeasureTheory Set Function
namespace DukePrimeDegree
open PrimeDegreePackets

lemma integrableOn_observationInformation_fiber
    {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) (a : α) :
    IntegrableOn (observationInformation μ P) {y | P y=a} μ := by
  apply (integrable_const (-Real.log (μ.real {y | P y=a}))).congr
  filter_upwards [ae_restrict_mem (hP a)] with y hy
  simp only [observationInformation,hy]

lemma setIntegral_observationInformation_fiber
    {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) (a : α) :
    (∫ y in {y | P y=a}, observationInformation μ P y ∂μ) =
      Real.negMulLog (μ.real {y | P y=a}) := by
  calc
    _ = ∫ _ in {y | P y=a}, -Real.log (μ.real {y | P y=a}) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (hP a)] with y hy
      simp only [observationInformation,hy]
    _ = _ := by simp [Real.negMulLog_def,Measure.real,neg_mul,mul_neg]

/-- Summable Shannon terms are sufficient for integrability of the
countable partition's pointwise information. -/
theorem countable_observationInformation_integrable
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hs : Summable (fun a => Real.negMulLog (μ.real {y | P y=a}))) :
    Integrable (observationInformation μ P) μ := by
  have hnorm (a : α) :
      (∫ y in {y | P y=a}, ‖observationInformation μ P y‖ ∂μ) =
        Real.negMulLog (μ.real {y | P y=a}) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (observationInformation_nonneg μ P _)]
    exact setIntegral_observationInformation_fiber μ P hP a
  have H := integrableOn_iUnion_of_summable_integral_norm
    (fun a => integrableOn_observationInformation_fiber μ P hP a)
    (by simpa only [hnorm] using hs)
  have he : (⋃ a, {y | P y=a})=univ := by ext y; simp
  rwa [he,integrableOn_univ] at H

theorem integral_countable_observationInformation
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hs : Summable (fun a => Real.negMulLog (μ.real {y | P y=a}))) :
    (∫ y, observationInformation μ P y ∂μ) =
      ∑' a, Real.negMulLog (μ.real {y | P y=a}) := by
  have he : (⋃ a, {y | P y=a})=univ := by ext y; simp
  have hd : Pairwise (Disjoint on (fun a => {y | P y=a})) := by
    intro a b hab
    change Disjoint {y | P y=a} {y | P y=b}
    rw [Set.disjoint_left]
    intro y ha hb
    exact hab (ha.symm.trans hb)
  have H := integral_iUnion hP hd
    ((countable_observationInformation_integrable μ P hP hs).integrableOn)
  simpa only [he,Measure.restrict_univ,setIntegral_observationInformation_fiber μ P hP] using H

lemma ae_observation_fiber_pos
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) (P : Y → α) :
    ∀ᵐ y ∂μ, 0 < μ {z | P z=P y} := by
  have h (a : α) : ∀ᵐ y ∂μ, P y=a → 0 < μ {z | P z=a} := by
    by_cases ha : μ {z | P z=a}=0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp ha] with y hy
      exact fun hya => (hy hya).elim
    · exact ae_of_all _ (fun _ _ => pos_iff_ne_zero.mpr ha)
  filter_upwards [ae_all_iff.mpr h] with y hy
  exact hy (P y) rfl

/-- Every finite recoding is bounded by the same countable Shannon sum. -/
theorem finite_recode_entropy_le_countable_information
    {Y α β : Type*} [MeasurableSpace Y] [Countable α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hs : Summable (fun a => Real.negMulLog (μ.real {y | P y=a})))
    (f : α → β) (hf : ∀ b, MeasurableSet {y | f (P y)=b}) :
    observationEntropy μ (f ∘ P) ≤ ∑' a, Real.negMulLog (μ.real {y | P y=a}) := by
  rw [←integral_countable_observationInformation μ P hP hs,
    ←integral_observationInformation μ (f ∘ P) hf]
  apply integral_mono_ae (observationInformation_integrable μ (f ∘ P) hf)
    (countable_observationInformation_integrable μ P hP hs)
  filter_upwards [ae_observation_fiber_pos μ P] with y hy
  apply neg_le_neg
  apply Real.log_le_log (ENNReal.toReal_pos hy.ne' (measure_ne_top μ _))
  exact measureReal_mono (μ := μ) (fun z hz => congrArg f hz) (measure_ne_top μ _)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableObservationInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite clipping of a countable observation

At a sampled point, clipping above its observed value leaves its atom
unchanged. Positive atom mass also gives a common information bound.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma heightClip_atom_eq_of_lt {Y : Type*} (Q : Y → ℕ) (y : Y)
    {N : ℕ} (hN : Q y < N) :
    {z | heightClip Q N z = heightClip Q N y} = {z | Q z = Q y} := by
  ext z
  simp only [mem_ofPred_eq, heightClip, Fin.mk.injEq]
  omega

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableBoundaryEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable boundary label has sublinear information cost

Finite clipping controls the information in a single countable label,
even when that label has infinite Shannon entropy. The clipping error
depends only on its tail probability and the alphabet of the observed
word, rather than on the entropy of the countable label.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem heightClip_sigma_monotone {Y : Type*} (Q : Y → ℕ) :
    Monotone (fun L => observationSigma (heightClip Q L)) := by
  intro L J hLJ
  let f : Fin (J+1) → Fin (L+1) := fun a =>
    ⟨min a.val L,Nat.lt_succ_of_le (min_le_right _ _)⟩
  have he : heightClip Q L = f ∘ heightClip Q J := by
    funext y
    apply Fin.ext
    change min (Q y) L=min (min (Q y) J) L
    omega
  change observationSigma (heightClip Q L) ≤ observationSigma (heightClip Q J)
  rw [he]
  exact observationSigma_comp_le (heightClip Q J) f

theorem heightClip_sigma_generate {Y : Type*} (Q : Y → ℕ) :
    (⨆ L, observationSigma (heightClip Q L)) =
      MeasurableSpace.comap Q inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Y := MeasurableSpace.comap Q inferInstance
    have hQ : Measurable Q := comap_measurable Q
    exact iSup_le fun L => observationSigma_le _
      (fun a => heightClip_measurable hQ L (measurableSet_singleton a))
  · let : MeasurableSpace Y := ⨆ L, observationSigma (heightClip Q L)
    have hQ : Measurable Q := by
      apply measurable_to_countable'
      intro a
      have hc : Measurable (heightClip Q (a+1)) := by
        apply measurable_to_countable'
        intro b
        exact (le_iSup (fun L => observationSigma (heightClip Q L)) (a+1))
          _ ⟨{b},trivial,rfl⟩
      have he : {y | Q y=a} =
          {y | (heightClip Q (a+1) y).val=a} := by
        ext y
        change Q y=a ↔ min (Q y) (a+1)=a
        omega
      change MeasurableSet {y | Q y=a}
      rw [he]
      exact measurableSet_eq_fun
        ((measurable_of_finite (fun b : Fin (a+2) => b.val)).comp hc) measurable_const
    exact hQ.comap_le

theorem conditional_heightClip_tendsto {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun L => conditionalObservationEntropy μ P (heightClip Q L)) atTop
      (𝓝 (conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance))) := by
  have H := conditionalObservationEntropy_tendsto_sigma μ P hP (heightClip Q)
    (fun L a => heightClip_measurable hQ L (measurableSet_singleton a))
    (heightClip_sigma_monotone Q)
  rwa [heightClip_sigma_generate] at H

private theorem conditional_heightClip_le_larger {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) {L J : ℕ} (hLJ : L ≤ J) :
    conditionalObservationEntropy μ P (heightClip Q L) ≤
      conditionalObservationEntropy μ P (heightClip Q J) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
  let F (M : ℕ) (y : Y) :=
    finiteShannon (fun a => observationConditionalProbability μ P (heightClip Q M) a y)
  have hFint (M : ℕ) : Integrable (F M) μ :=
    integrable_finite_values μ (heightClip Q M)
      (fun a => heightClip_measurable hQ M (measurableSet_singleton a))
      (fun b => finiteShannon (fun a =>
        μ.real {y | (heightClip Q M y,P y)=(b,a)} /
          μ.real {y | heightClip Q M y=b}))
  have hB : MeasurableSet {y | L ≤ Q y} := hQ measurableSet_Ici
  have hbound : F L ≤ᵐ[μ] fun y => F J y +
      {y | L ≤ Q y}.indicator (fun _ => Real.log (Fintype.card α)) y := by
    filter_upwards [observationConditionalProbability_ae_sum μ P (heightClip Q L) hP
      (fun a => heightClip_measurable hQ L (measurableSet_singleton a)),
      observationConditionalProbability_ae_sum μ P (heightClip Q J) hP
      (fun a => heightClip_measurable hQ J (measurableSet_singleton a))] with y hyL hyJ
    by_cases hy : L ≤ Q y
    · rw [Set.indicator_of_mem (show y ∈ {y | L ≤ Q y} from hy)]
      have hlow : 0 ≤ F J y := finiteShannon_nonneg
        (fun a => observationConditionalProbability_nonneg μ P (heightClip Q J) a y) hyJ
      have hu : F L y ≤ Real.log (Fintype.card α) := finiteShannon_le_log_card
        (fun a => observationConditionalProbability_nonneg μ P (heightClip Q L) a y) hyL
      linarith
    · have hyL' : Q y < L := Nat.lt_of_not_ge hy
      have hyJ' : Q y < J := lt_of_lt_of_le hyL' hLJ
      have he : F L y=F J y := by
        apply congrArg finiteShannon
        funext a
        unfold observationConditionalProbability
        have hnum (M : ℕ) (hM : Q y < M) :
            {z | (heightClip Q M z,P z)=(heightClip Q M y,a)} =
              {z | Q z=Q y ∧ P z=a} := by
          ext z
          simp only [Prod.mk.injEq,Set.mem_ofPred_eq]
          have hh := Set.ext_iff.mp (heightClip_atom_eq_of_lt Q y hM) z
          exact and_congr_left fun _ => hh
        rw [hnum L hyL',hnum J hyJ',heightClip_atom_eq_of_lt Q y hyL',
          heightClip_atom_eq_of_lt Q y hyJ']
      rw [Set.indicator_of_notMem (show y ∉ {y | L ≤ Q y} from hy),he,add_zero]
  rw [conditionalObservationEntropy_eq_integral μ P (heightClip Q L) hP
    (fun a => heightClip_measurable hQ L (measurableSet_singleton a)),
    conditionalObservationEntropy_eq_integral μ P (heightClip Q J) hP
    (fun a => heightClip_measurable hQ J (measurableSet_singleton a))]
  have H := integral_mono_ae (hFint L)
    ((hFint J).add ((integrable_const _).indicator hB)) hbound
  simp only [Pi.add_apply] at H
  rw [integral_add (hFint J) ((integrable_const _).indicator hB),
    integral_indicator_const _ hB,smul_eq_mul] at H
  exact H

/-- Removing a finite clipping of the conditioning label changes entropy
only on the clipped tail. -/
theorem conditional_heightClip_le_countable {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) (L : ℕ) :
    conditionalObservationEntropy μ P (heightClip Q L) ≤
      conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
  apply ge_of_tendsto ((conditional_heightClip_tendsto μ P hP Q hQ).add_const _)
  filter_upwards [eventually_ge_atTop L] with J hLJ
  exact conditional_heightClip_le_larger μ P hP Q hQ hLJ

theorem observationEntropy_le_countable_conditioning {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) (L : ℕ) :
    observationEntropy μ P ≤ Real.log (L+1) +
      conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
  have hC a := heightClip_measurable hQ L (measurableSet_singleton a)
  have hjoint := observationEntropy_le_add_conditional μ P (heightClip Q L) hP hC
  have hcard := finiteShannon_le_log_card (fun a =>
    measureReal_nonneg (μ := μ) (s := {y | heightClip Q L y=a}))
    (observation_distribution_sum μ (heightClip Q L) hC)
  have htail := conditional_heightClip_le_countable μ P hP Q hQ L
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hcard
  change observationEntropy μ (heightClip Q L) ≤ _ at hcard
  linarith

theorem conditional_countable_le_observationEntropy {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance) ≤
      observationEntropy μ P := by
  apply le_of_tendsto (conditional_heightClip_tendsto μ P hP Q hQ)
  exact Eventually.of_forall fun L => conditionalObservationEntropy_le μ P
    (heightClip Q L) hP
    (fun a => heightClip_measurable hQ L (measurableSet_singleton a))

theorem countable_tail_measureReal_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun L => μ.real {y | L ≤ Q y}) atTop (𝓝 0) := by
  have he : (⋂ L : ℕ, {y | L ≤ Q y}) = ∅ := by
    ext y
    simp only [mem_iInter,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro h
    exact Nat.not_succ_le_self (Q y) (h (Q y+1))
  have H := tendsto_measure_iInter_atTop
    (μ := μ) (fun L => (hQ measurableSet_Ici).nullMeasurableSet)
    (show Antitone (fun L => {y | L ≤ Q y}) from fun L J h y hy => h.trans hy)
    ⟨0,measure_ne_top _ _⟩
  change Tendsto (fun L => μ {y | L ≤ Q y}) atTop
    (𝓝 (μ (⋂ L : ℕ, {y | L ≤ Q y}))) at H
  rw [he,measure_empty] at H
  simpa only [measureReal_def,ENNReal.toReal_zero,Function.comp_def] using
    (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp H

/-- A single countable observation at the end of an orbit word carries
sublinear information about that word. Its Shannon entropy may be infinite. -/
theorem countable_boundary_information_sublinear {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun N : ℕ =>
      (observationEntropy μ (orbitName T P N) -
        conditionalSigmaEntropy μ (orbitName T P N)
          (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance)) / N)
      atTop (𝓝 0) := by
  let E (N : ℕ) := observationEntropy μ (orbitName T P N) -
    conditionalSigmaEntropy μ (orbitName T P N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance)
  have hE (N : ℕ) : 0 ≤ E N := sub_nonneg.mpr
    (conditional_countable_le_observationEntropy μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) (Q ∘ T^[N])
      (hQ.comp (hT.measurable.iterate N)))
  have hbound (L N : ℕ) :
      E N ≤ Real.log (L+1) + μ.real {y | L ≤ Q y} *
        ((N : ℝ) * Real.log (Fintype.card α)) := by
    have H := observationEntropy_le_countable_conditioning μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) (Q ∘ T^[N])
      (hQ.comp (hT.measurable.iterate N)) L
    have htail : μ.real {y | L ≤ (Q ∘ T^[N]) y} = μ.real {y | L ≤ Q y} :=
      (hT.iterate N).measureReal_preimage (hQ measurableSet_Ici).nullMeasurableSet
    rw [htail,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at H
    dsimp only [E]
    linarith
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun L => μ.real {y | L ≤ Q y} *
      Real.log (Fintype.card α)) atTop (𝓝 0) := by
    simpa using (countable_tail_measureReal_tendsto_zero μ Q hQ).mul_const
      (Real.log (Fintype.card α))
  obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))).exists
  have hl : Tendsto (fun N : ℕ => Real.log (L+1)/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hl.eventually (gt_mem_nhds (show 0 < ε/2 by positivity)),
    eventually_ge_atTop (1 : ℕ)] with N hlog hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have he : E N/(N : ℝ) ≤ Real.log (L+1)/(N : ℝ) +
      μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
    apply (div_le_iff₀ hn).mpr
    have hh := hbound L N
    have heq : (Real.log (L+1)/(N : ℝ) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α)) * N =
        Real.log (L+1) + μ.real {y | L ≤ Q y} *
          ((N : ℝ) * Real.log (Fintype.card α)) := by
      field_simp
    rwa [heq]
  change dist (E N/(N : ℝ)) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hE N) hn.le)]
  linarith

theorem conditional_boundary_entropy_rate {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun N : ℕ => conditionalSigmaEntropy μ (orbitName T P N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) / N) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  have H := (tendsto_observationEntropyRate μ hT P hP).sub
    (countable_boundary_information_sublinear μ hT P hP Q hQ)
  simp only [sub_zero] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  rw [sub_div]
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableConditioningChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chain rules with one countable conditioning label

Finite clipping of the conditioning label and the martingale limit extend
the finite chain rule without requiring finite entropy of that label.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_pair_eq {Y α β : Type*} [Countable α] [Countable β]
    (P : Y → α) (Q : Y → β) :
    observationSigma (fun y => (P y,Q y))=observationSigma P ⊔ observationSigma Q := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hprod : (inferInstance : MeasurableSpace (α × β))=⊤ := by
    apply top_unique
    intro s _
    exact (Set.to_countable s).measurableSet
  unfold observationSigma
  rw [←hprod]
  exact MeasurableSpace.comap_prodMk P Q

theorem conditionalSigmaEntropy_chain_nat {Y α β : Type*}
    [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b})
    (F : Y → ℕ) (hF : Measurable F) :
    conditionalSigmaEntropy μ (fun y => (P y,R y))
        (MeasurableSpace.comap F inferInstance) =
      conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) +
        conditionalSigmaEntropy μ R
          (MeasurableSpace.comap F inferInstance ⊔ observationSigma P) := by
  let C := fun L : ℕ => fun y : Y => (heightClip F L y,P y)
  have hC (L : ℕ) (b : Fin (L+1) × α) : MeasurableSet {y | C L y=b} :=
    observationPair_measurable_fiber _ _
      (fun a => heightClip_measurable hF L (measurableSet_singleton a)) hP b
  have hCm : Monotone (fun L => observationSigma (C L)) := by
    intro L J hLJ
    simp only [C,observationSigma_pair_eq]
    exact sup_le_sup_right (heightClip_sigma_monotone F hLJ) _
  have hCg : (⨆ L, observationSigma (C L))=
      MeasurableSpace.comap F inferInstance ⊔ observationSigma P := by
    simp only [C,observationSigma_pair_eq]
    rw [iSup_sup_eq,heightClip_sigma_generate,iSup_const]
  have h₁ := conditional_heightClip_tendsto μ (fun y => (P y,R y))
    (observationPair_measurable_fiber P R hP hR) F hF
  have h₂ := conditional_heightClip_tendsto μ P hP F hF
  have h₃ := conditionalObservationEntropy_tendsto_sigma μ R hR C hC hCm
  rw [hCg] at h₃
  apply tendsto_nhds_unique h₁
  apply (h₂.add h₃).congr
  intro L
  exact (conditionalObservationEntropy_chain μ P R (heightClip F L)).symm

theorem conditionalSigmaEntropy_comp_preserving_nat {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (F : Y → ℕ) (hF : Measurable F) :
    conditionalSigmaEntropy μ (P ∘ T) (MeasurableSpace.comap (F ∘ T) inferInstance) =
      conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) := by
  have h₁ := conditional_heightClip_tendsto μ (P ∘ T)
    (fun a => (hP a).preimage hT.measurable) (F ∘ T) (hF.comp hT.measurable)
  have h₂ := conditional_heightClip_tendsto μ P hP F hF
  apply tendsto_nhds_unique h₁
  apply h₂.congr
  intro L
  symm
  exact conditionalObservationEntropy_comp_preserving μ P (heightClip F L) hP
    (fun a => heightClip_measurable hF L (measurableSet_singleton a)) hT

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorSymbols
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite symbol recovers a countable label from its successor

A uniform finite predecessor bound replaces an unbounded observation by
a finite symbol once its next countable label is known.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

lemma predecessor_word_recovers {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    {x y : Y} {N : ℕ}
    (hterminal : Q (T^[N] x)=Q (T^[N] y))
    (hword : ∀ k < N, B (T^[k] x)=B (T^[k] y)) :
    ∀ k ≤ N, Q (T^[k] x)=Q (T^[k] y) := by
  induction N with
  | zero =>
      intro k hk
      have hk0 : k=0 := by omega
      subst k
      exact hterminal
  | succ N ih =>
      have hlast : Q (T^[N] x)=Q (T^[N] y) := by
        rw [←hdecode (T^[N] x),←hdecode (T^[N] y)]
        have ht : T (T^[N] x)=T^[N+1] x := (Function.iterate_succ_apply' T N x).symm
        have hu : T (T^[N] y)=T^[N+1] y := (Function.iterate_succ_apply' T N y).symm
        rw [ht,hu,hterminal,hword N (Nat.lt_succ_self N)]
      intro k hk
      by_cases hkn : k ≤ N
      · exact ih hlast (fun i hi => hword i (Nat.lt_trans hi (Nat.lt_succ_self N))) k hkn
      · have he : k=N+1 := by omega
        subst k
        exact hterminal

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalFiberRecoding
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite recoding within the fibers of a countable observation -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationEntropy_eq_of_ae_eq {Y α : Type*} [MeasurableSpace Y]
    [Fintype α] (ν : Measure Y) (P R : Y → α) (h : P =ᵐ[ν] R) :
    observationEntropy ν P=observationEntropy ν R := by
  unfold observationEntropy
  congr 1
  funext a
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [h] with y hy
  show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
  simp only [Set.mem_setOf_eq, hy]

theorem conditionalSigmaEntropy_le_fiber_recoding
    {Y S α β : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (f : S → β → α) (hf : ∀ x, P x=f (F x) (B x)) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) ≤
      conditionalSigmaEntropy μ B (MeasurableSpace.comap F inferInstance) := by
  rw [conditionalSigmaEntropy_comap_eq_integral μ F hF P
      (fun a => hP (measurableSet_singleton a)),
    conditionalSigmaEntropy_comap_eq_integral μ F hF B
      (fun a => hB (measurableSet_singleton a))]
  apply integral_mono_ae
    (integrable_kernel_entropy (μ.map F) (condDistrib id F μ) P
      (fun a => hP (measurableSet_singleton a)))
    (integrable_kernel_entropy (μ.map F) (condDistrib id F μ) B
      (fun a => hB (measurableSet_singleton a)))
  filter_upwards [ae_condDistrib_self_fiber μ F hF] with s hs
  have he : P =ᵐ[condDistrib id F μ s] (f s ∘ B) := by
    filter_upwards [hs] with y hy
    simpa only [Function.comp_apply,hy] using hf y
  rw [observationEntropy_eq_of_ae_eq _ P (f s ∘ B) he]
  apply observationEntropy_le_of_refines _ _ B
    (fun a => ((measurable_of_finite (f s)).comp hB) (measurableSet_singleton a))
    (fun a => hB (measurableSet_singleton a))
  intro x y hxy
  exact congrArg (f s) hxy

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorWordEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite predecessor words control clipped countable words -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_le_of_fiber_refinement
    {Y S α β : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (href : ∀ x y, F x=F y → B x=B y → P x=P y) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) ≤
      conditionalSigmaEntropy μ B (MeasurableSpace.comap F inferInstance) := by
  classical
  let f : S → β → α := fun s b =>
    if h : ∃ x, F x=s ∧ B x=b then P h.choose else Classical.choice inferInstance
  apply conditionalSigmaEntropy_le_fiber_recoding μ F hF P hP B hB f
  intro x
  have hx : ∃ y, F y=F x ∧ B y=B x := ⟨x,rfl,rfl⟩
  dsimp only [f]
  rw [dite_eq_left hx]
  exact href x hx.choose hx.choose_spec.1.symm hx.choose_spec.2.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureLabelBlocks
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite blocks of countable future labels -/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_le_of_fiber_refinement {Y α β : Type*}
    (P : Y → α) (Q : Y → β)
    (href : ∀ x y, Q x=Q y → P x=P y) :
    observationSigma P ≤ observationSigma Q := by
  rintro s ⟨t,_,rfl⟩
  refine ⟨Q '' (P ⁻¹' t),trivial,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,hyx⟩
    change P x ∈ t
    rw [←href y x hyx]
    exact hy
  · intro hx
    exact ⟨x,hx,rfl⟩

lemma futureLabelBlock_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) (N : ℕ) :
    Measurable (futureLabelBlock T Q N) := by
  exact (measurable_of_countable (Encodable.encode : (Fin N → ℕ) → ℕ)).comp
    (measurable_pi_iff.mpr fun i => hQ.comp (hT.iterate (i.val+1)))

lemma futureLabelBlock_eq_iff {Y : Type*} (T : Y → Y) (Q : Y → ℕ)
    (N : ℕ) (x y : Y) :
    futureLabelBlock T Q N x=futureLabelBlock T Q N y ↔
      ∀ i : Fin N, Q (T^[i.val+1] x)=Q (T^[i.val+1] y) := by
  exact Encodable.encode_injective.eq_iff.trans funext_iff

lemma futureLabelBlock_sigma_monotone {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    Monotone (fun N => observationSigma (futureLabelBlock T Q N)) := by
  intro N M hNM
  apply observationSigma_le_of_fiber_refinement
  intro x y hxy
  rw [futureLabelBlock_eq_iff] at hxy ⊢
  intro i
  exact hxy ⟨i.val,lt_of_lt_of_le i.isLt hNM⟩

lemma futureLabelBlock_sigma_generate {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    (⨆ N, observationSigma (futureLabelBlock T Q N)) =
      ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x)) := by
  apply le_antisymm
  · let : MeasurableSpace Y := ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x))
    apply iSup_le
    intro N
    have hQ (k : ℕ) : Measurable (fun x => Q (T^[k+1] x)) :=
      (comap_measurable _).iSup' k
    have hm : Measurable (futureLabelBlock T Q N) :=
      (measurable_of_countable (Encodable.encode : (Fin N → ℕ) → ℕ)).comp
        (measurable_pi_iff.mpr fun i => hQ i.val)
    exact hm.comap_le
  · apply iSup_le
    intro k
    apply le_trans _ (le_iSup (fun N => observationSigma (futureLabelBlock T Q N)) (k+1))
    apply observationSigma_le_of_fiber_refinement
    intro x y hxy
    exact (futureLabelBlock_eq_iff T Q (k+1) x y).mp hxy ⟨k,Nat.lt_succ_self k⟩

lemma futureLabelBlock_eq_iff_predecessor_symbols {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) (x y : Y) :
    futureLabelBlock T Q (N+1) x=futureLabelBlock T Q (N+1) y ↔
      Q (T^[N+1] x)=Q (T^[N+1] y) ∧
        futureName T B N x=futureName T B N y := by
  rw [futureLabelBlock_eq_iff]
  constructor
  · intro h
    refine ⟨h ⟨N,Nat.lt_succ_self N⟩,?_⟩
    funext i
    change B (T^[i.val] (T x))=B (T^[i.val] (T y))
    apply href
    · simpa only [←Function.iterate_succ_apply] using h ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩
    · simpa only [←Function.iterate_succ_apply,←Function.iterate_succ_apply'] using
        h ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩
  · rintro ⟨ht,hb⟩
    have ht' : Q (T^[N] (T x))=Q (T^[N] (T y)) := by
      simpa only [←Function.iterate_succ_apply] using ht
    have hh := predecessor_word_recovers T Q B decode hdecode ht'
      (fun k hk => congrFun hb ⟨k,hk⟩)
    intro i
    simpa only [←Function.iterate_succ_apply] using hh i.val (by omega)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorEntropySum
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy increments for finite predecessor symbols -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma orbitName_eq_iff_head_future {Y α : Type*} (T : Y → Y) (B : Y → α)
    (N : ℕ) (x y : Y) :
    orbitName T B (N+1) x=orbitName T B (N+1) y ↔
      B x=B y ∧ futureName T B N x=futureName T B N y := by
  constructor
  · intro h
    constructor
    · simpa only [orbitName,Fin.val_zero,Function.iterate_zero_apply] using
        congrFun h (0 : Fin (N+1))
    · funext i
      simpa only [futureName,orbitName,Fin.val_succ,Function.iterate_succ_apply] using
        congrFun h i.succ
  · rintro ⟨hh,ht⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [orbitName,Fin.val_zero,Function.iterate_zero_apply] using hh
    · simpa only [futureName,orbitName,Fin.val_succ,Function.iterate_succ_apply] using
        congrFun ht j

theorem predecessor_word_conditional_increment
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B (N+1))
        (MeasurableSpace.comap (Q ∘ T^[N+1]) inferInstance) =
      conditionalSigmaEntropy μ (orbitName T B N)
        (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) +
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (futureLabelBlock T Q (N+1)) inferInstance) := by
  let F := Q ∘ T^[N+1]
  let W := futureName T B N
  have hF : Measurable F := hQ.comp (hT.measurable.iterate (N+1))
  have hW : Measurable W := measurable_pi_iff.mpr fun i =>
    hB.comp ((hT.measurable.iterate i.val).comp hT.measurable)
  have hV : Measurable (orbitName T B (N+1)) := measurable_pi_iff.mpr fun i =>
    hB.comp (hT.measurable.iterate i.val)
  have hpair : Measurable (fun y => (W y,B y)) := hW.prodMk hB
  have he : conditionalSigmaEntropy μ (orbitName T B (N+1))
        (MeasurableSpace.comap F inferInstance) =
      conditionalSigmaEntropy μ (fun y => (W y,B y))
        (MeasurableSpace.comap F inferInstance) := by
    apply le_antisymm
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ F hF _ hV _ hpair
      intro x y _ hxy
      exact (orbitName_eq_iff_head_future T B N x y).mpr
        ⟨(congrArg Prod.snd hxy),(congrArg Prod.fst hxy)⟩
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ F hF _ hpair _ hV
      intro x y _ hxy
      have hh := (orbitName_eq_iff_head_future T B N x y).mp hxy
      exact Prod.ext hh.2 hh.1
  rw [he,conditionalSigmaEntropy_chain_nat μ W
    (fun w => hW (measurableSet_singleton w)) B
    (fun b => hB (measurableSet_singleton b)) F hF]
  congr 1
  · have hVN : Measurable (orbitName T B N) := measurable_pi_iff.mpr fun i =>
      hB.comp (hT.measurable.iterate i.val)
    have h := conditionalSigmaEntropy_comp_preserving_nat μ hT (orbitName T B N)
      (fun w => hVN (measurableSet_singleton w))
      (Q ∘ T^[N]) (hQ.comp (hT.measurable.iterate N))
    change conditionalSigmaEntropy μ (futureName T B N)
      (MeasurableSpace.comap (Q ∘ T^[N+1]) inferInstance) = _
    have hshift : (Q ∘ T^[N]) ∘ T = Q ∘ T^[N+1] := by
      funext x
      exact congrArg Q (Function.iterate_succ_apply T N x).symm
    rw [hshift] at h
    exact h
  · congr 1
    have hs : observationSigma (fun x => (F x,W x))=
        observationSigma (futureLabelBlock T Q (N+1)) := by
      apply le_antisymm
      · apply observationSigma_le_of_fiber_refinement
        intro x y hxy
        have hh := (futureLabelBlock_eq_iff_predecessor_symbols T Q B href decode hdecode N x y).mp hxy
        exact Prod.ext hh.1 hh.2
      · apply observationSigma_le_of_fiber_refinement
        intro x y hxy
        exact (futureLabelBlock_eq_iff_predecessor_symbols T Q B href decode hdecode N x y).mpr
          (Prod.mk.inj hxy)
    rw [observationSigma_pair_eq] at hs
    exact hs

theorem predecessor_word_conditional_sum
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B N)
        (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) =
      ∑ k ∈ Finset.range N, conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (futureLabelBlock T Q (k+1)) inferInstance) := by
  induction N with
  | zero =>
      simp only [Finset.range_zero,Finset.sum_empty]
      apply le_antisymm
      · have h := conditional_countable_le_observationEntropy μ (orbitName T B 0)
          (orbitName_measurable_fiber hT.measurable
            (fun b => hB (measurableSet_singleton b)) 0) (Q ∘ T^[0])
          (hQ.comp (hT.measurable.iterate 0))
        simpa only [observationEntropy_unique] using h
      · exact conditionalSigmaEntropy_comap_nonneg μ (Q ∘ T^[0])
          (hQ.comp (hT.measurable.iterate 0)) _
          (orbitName_measurable_fiber hT.measurable
            (fun b => hB (measurableSet_singleton b)) 0)
  | succ N ih =>
      rw [predecessor_word_conditional_increment μ hT Q hQ B hB href decode hdecode N,
        ih,Finset.sum_range_succ]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorEntropyLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entropy upper bound from finite predecessor symbols

The countable terminal label has sublinear information cost. A finite
conditional chain rule and Cesaro convergence control every clipped rate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_word_conditional_rate
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x) :
    Tendsto (fun N : ℕ => conditionalSigmaEntropy μ (orbitName T B N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) / N) atTop
      (𝓝 (conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance))) := by
  have hL := conditionalSigmaEntropy_tendsto_iSup μ B
    (fun N => observationSigma (futureLabelBlock T Q N))
    (futureLabelBlock_sigma_monotone T Q)
    (fun N => (futureLabelBlock_measurable hT.measurable hQ N).comap_le)
  rw [futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap] at hL
  have hs := hL.comp (tendsto_add_atTop_nat 1)
  have hc := hs.cesaro
  apply hc.congr
  intro N
  rw [predecessor_word_conditional_sum μ hT Q hQ B hB href decode hdecode]
  simp only [Function.comp_def,div_eq_mul_inv]
  rw [mul_comm]
  rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_IncreasingConditioningChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite chain rule after increasing countable conditioning

This form applies to the actual whole-future sigma algebra by using the
finite encoded future blocks. It never assumes that the countable labels
have finite Shannon entropy.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_chain_iSup_nat
    {Y α β : Type*} [mY : MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b})
    (F : ℕ → Y → ℕ) (hF : ∀ N, Measurable (F N))
    (hmono : Monotone (fun N => observationSigma (F N))) :
    conditionalSigmaEntropy (mY := mY) μ (fun y => (P y,R y))
        (⨆ N, observationSigma (F N)) =
      conditionalSigmaEntropy (mY := mY) μ P (⨆ N, observationSigma (F N)) +
        conditionalSigmaEntropy (mY := mY) μ R
          ((⨆ N, observationSigma (F N)) ⊔ observationSigma P) := by
  have hle (N : ℕ) : observationSigma (F N) ≤ mY := (hF N).comap_le
  have hpairmono : Monotone (fun N => observationSigma (F N) ⊔ observationSigma P) :=
    fun _ _ h => sup_le_sup_right (hmono h) _
  have hpairle (N : ℕ) : observationSigma (F N) ⊔ observationSigma P ≤ mY :=
    sup_le (hle N) (observationSigma_le P hP)
  have h₁ := conditionalSigmaEntropy_tendsto_iSup μ (fun y => (P y,R y)) _ hmono hle
  have h₂ := conditionalSigmaEntropy_tendsto_iSup μ P _ hmono hle
  have h₃ := conditionalSigmaEntropy_tendsto_iSup μ R _ hpairmono hpairle
  rw [iSup_sup_eq,iSup_const] at h₃
  apply tendsto_nhds_unique h₁
  apply (h₂.add h₃).congr
  intro N
  exact (conditionalSigmaEntropy_chain_nat μ P hP R hR (F N) (hF N)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chain rules with the actual entire future -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_chain_wholeFuture
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b}) :
    conditionalSigmaEntropy μ (fun y => (P y,R y))
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) =
      conditionalSigmaEntropy μ P
          (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) +
        conditionalSigmaEntropy μ R
          (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance ⊔ observationSigma P) := by
  have H := conditionalSigmaEntropy_chain_iSup_nat μ P hP R hR
    (futureLabelBlock T Q) (futureLabelBlock_measurable hT hQ)
    (futureLabelBlock_sigma_monotone T Q)
  simpa only [futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_AuxiliaryPredecessorEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite auxiliary observations in the predecessor entropy bound -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_factor_entropyRate_le
    {Y α : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (P : Y → α) (hP : Measurable P)
    (hfactor : ∀ x y, Q x=Q y → P x=P y) :
    observationEntropyRate μ T P ≤ conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  apply le_of_tendsto_of_tendsto
    (conditional_boundary_entropy_rate μ hT P
      (fun a => hP (measurableSet_singleton a)) Q hQ)
    (predecessor_word_conditional_rate μ hT Q hQ B hB href decode hdecode)
  apply Eventually.of_forall
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply conditionalSigmaEntropy_le_of_fiber_refinement μ (Q ∘ T^[N])
    (hQ.comp (hT.measurable.iterate N)) (orbitName T P N)
    (measurable_pi_iff.mpr fun i => hP.comp (hT.measurable.iterate i.val)) (orbitName T B N)
    (measurable_pi_iff.mpr fun i => hB.comp (hT.measurable.iterate i.val))
  intro x y hterm hword
  have hh := predecessor_word_recovers T Q B decode hdecode hterm
    (fun k hk => congrFun hword ⟨k,hk⟩)
  funext i
  exact hfactor _ _ (hh i.val i.isLt.le)

lemma conditionalSigmaEntropy_wholeFuture_le_observationEntropy
    {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalSigmaEntropy μ P
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) ≤
        observationEntropy μ P := by
  have hlim := conditionalSigmaEntropy_tendsto_iSup μ P
    (fun N => observationSigma (futureLabelBlock T Q N))
    (futureLabelBlock_sigma_monotone T Q)
    (fun N => (futureLabelBlock_measurable hT hQ N).comap_le)
  rw [futureLabelBlock_sigma_generate,countableFutureSigma_eq_comap] at hlim
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun N => conditional_countable_le_observationEntropy
    μ P hP (futureLabelBlock T Q N) (futureLabelBlock_measurable hT hQ N)

/-- The finite auxiliary label contributes only its one-step Shannon
entropy; the main term is conditioned on the combined entire future. -/
theorem predecessor_auxiliary_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    {L : ℕ} (R : Y → Fin (L+1)) (hR : Measurable R) (K : ℕ) :
    observationEntropyRate μ T (heightClip Q K) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap
          (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance) +
      observationEntropy μ R := by
  classical
  let W : Y → ℕ := fun x => Encodable.encode (Q x,R x)
  have hW : Measurable W := (measurable_of_countable Encodable.encode).comp (hQ.prodMk hR)
  let e := Fintype.equivFin (Fin (M+1) × Fin (L+1))
  let C : Y → Fin (Fintype.card (Fin (M+1) × Fin (L+1))+1) :=
    fun x => (e (B x,R x)).castSucc
  have hC : Measurable C := (measurable_of_finite (fun p => (e p).castSucc)).comp
    (hB.prodMk hR)
  have hparts {x y : Y} (h : W x=W y) : Q x=Q y ∧ R x=R y :=
    Prod.mk.inj (Encodable.encode_injective h)
  have hrefC : ∀ x y, W x=W y → W (T x)=W (T y) → C x=C y := by
    intro x y hxy hTxy
    have hh := hparts hxy
    dsimp only [C]
    rw [href x y hh.1 (hparts hTxy).1,hh.2]
  let dec : ℕ → Fin (Fintype.card (Fin (M+1) × Fin (L+1))+1) → ℕ := fun q b =>
    let p := Fin.lastCases (motive := fun _ => Fin (M+1) × Fin (L+1)) (0,0) e.symm b
    Encodable.encode (decode ((Encodable.decode (α := ℕ × Fin (L+1)) q).getD (0,0)).1 p.1,p.2)
  have hdec (x : Y) : dec (W (T x)) (C x)=W x := by
    simp only [dec,W,C,Fin.lastCases_castSucc,Equiv.symm_apply_apply,
      Encodable.encodek,Option.getD_some,hdecode]
  have hfirst := predecessor_factor_entropyRate_le μ hT W hW C hC hrefC dec hdec
    (heightClip Q K) (heightClip_measurable hQ K) (fun x y h => by
      apply Fin.ext
      change min (Q x) K=min (Q y) K
      rw [(hparts h).1])
  have hpair : Measurable (fun x => (B x,R x)) := hB.prodMk hR
  have hrec := conditionalSigmaEntropy_le_of_fiber_refinement μ
    (entireFutureObservation T W) (entireFutureObservation_measurable hT.measurable hW)
    C hC (fun x => (B x,R x)) hpair (fun x y _ h => by
      dsimp only [C]
      rw [h])
  have hchain := conditionalSigmaEntropy_chain_wholeFuture μ hT.measurable W hW
    B (fun a => hB (measurableSet_singleton a))
    R (fun a => hR (measurableSet_singleton a))
  have hcond := conditionalSigmaEntropy_antitone μ R
    (fun a => hR (measurableSet_singleton a))
    (m := MeasurableSpace.comap (entireFutureObservation T W) inferInstance)
    (n := MeasurableSpace.comap (entireFutureObservation T W) inferInstance ⊔ observationSigma B)
    le_sup_left (sup_le (entireFutureObservation_measurable hT.measurable hW).comap_le
      (observationSigma_le B (fun a => hB (measurableSet_singleton a))))
  have hobs := conditionalSigmaEntropy_wholeFuture_le_observationEntropy μ hT.measurable W hW
    R (fun a => hR (measurableSet_singleton a))
  exact hfirst.trans (hrec.trans (hchain.le.trans (add_le_add le_rfl (hcond.trans hobs))))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableAuxiliaryEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable auxiliary observations with finite Shannon entropy

Increasing finite clippings recover the exact combined future sigma
algebra. The entropy cost is bounded by the full countable Shannon sum.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma observationSigma_encoded_pair {Y α β : Type*} [Encodable α] [Encodable β]
    (P : Y → α) (Q : Y → β) :
    observationSigma (fun x => Encodable.encode (P x,Q x)) =
      observationSigma P ⊔ observationSigma Q := by
  rw [←observationSigma_pair_eq]
  apply le_antisymm
  · apply observationSigma_le_of_fiber_refinement
    intro x y h
    exact congrArg Encodable.encode h
  · apply observationSigma_le_of_fiber_refinement
    intro x y h
    exact Encodable.encode_injective h

lemma auxiliaryFutureSigma_eq {Y : Type*} (T : Y → Y) (Q R : Y → ℕ) (L : ℕ) :
    MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
      inferInstance =
    ⨆ k : ℕ, observationSigma (fun x => Q (T^[k+1] x)) ⊔
      observationSigma (heightClip (fun x => R (T^[k+1] x)) L) := by
  rw [←countableFutureSigma_eq_comap]
  congr 1
  funext k
  exact observationSigma_encoded_pair _ _

lemma auxiliaryFutureSigma_monotone {Y : Type*} (T : Y → Y) (Q R : Y → ℕ) :
    Monotone (fun L => MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
      inferInstance) := by
  intro L J hLJ
  dsimp only
  rw [auxiliaryFutureSigma_eq,auxiliaryFutureSigma_eq]
  exact iSup_mono (fun k => sup_le_sup_left (heightClip_sigma_monotone _ hLJ) _)

lemma auxiliaryFutureSigma_generate {Y : Type*} (T : Y → Y) (Q R : Y → ℕ) :
    (⨆ L, MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
      inferInstance) =
    MeasurableSpace.comap
      (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance := by
  simp_rw [auxiliaryFutureSigma_eq]
  rw [iSup_comm]
  simp_rw [iSup_sup_eq,iSup_const,heightClip_sigma_generate]
  rw [←countableFutureSigma_eq_comap]
  simp_rw [observationSigma_encoded_pair]
  rw [iSup_sup_eq]
  rfl

/-- A finite-entropy auxiliary observation may be adjoined at a cost of
its Shannon entropy, even when the main countable observation has
infinite Shannon entropy. -/
theorem predecessor_countable_auxiliary_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (R : Y → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (K : ℕ) :
    observationEntropyRate μ T (heightClip Q K) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap
          (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  let m := fun L => MeasurableSpace.comap
    (entireFutureObservation T (fun x => Encodable.encode (Q x,heightClip R L x)))
    (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hm (L : ℕ) : m L ≤ ‹MeasurableSpace Y› :=
    (entireFutureObservation_measurable hT.measurable
      ((measurable_of_countable Encodable.encode).comp
        (hQ.prodMk (heightClip_measurable hR L)))).comap_le
  have hlim := conditionalSigmaEntropy_tendsto_iSup μ B m
    (auxiliaryFutureSigma_monotone T Q R) hm
  rw [auxiliaryFutureSigma_generate] at hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim.add_const _)
  apply Eventually.of_forall
  intro L
  have H := predecessor_auxiliary_entropyRate_le μ hT Q hQ B hB href decode hdecode
    (heightClip R L) (heightClip_measurable hR L) K
  have hc := finite_recode_entropy_le_countable_information μ R
    (fun n => hR (measurableSet_singleton n)) hfinite
    (heightClip (id : ℕ → ℕ) L)
    (fun a => heightClip_measurable hR L (measurableSet_singleton a))
  exact H.trans (add_le_add le_rfl hc)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_AuxiliaryKernelEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The auxiliary-future upper bound in terms of the actual kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma combined_future_kernel_entropy_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T)
    (Q R : Y → ℕ) (hQ : Measurable Q) (hR : Measurable R)
    (κ : Kernel Y Y) (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) → κ x=κ y)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B) :
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap
        (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance) ≤
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (fun x => (κ x,entireFutureObservation T Q x)) inferInstance) := by
  have hQR : Measurable (fun x => Encodable.encode (Q x,R x)) :=
    (measurable_of_countable Encodable.encode).comp (hQ.prodMk hR)
  apply conditionalSigmaEntropy_le_of_conull_fibers μ
    (entireFutureObservation T (fun x => Encodable.encode (Q x,R x)))
    (entireFutureObservation_measurable hT hQR)
    (fun x => (κ x,entireFutureObservation T Q x))
    (κ.measurable.prodMk (entireFutureObservation_measurable hT hQ)) E hE _ B
    (fun b => hB (measurableSet_singleton b))
  intro x hx y hy hxy
  have hnames (k : ℕ) : Q (T^[k+1] x)=Q (T^[k+1] y) ∧
      R (T^[k+1] x)=R (T^[k+1] y) :=
    Prod.mk.inj (Encodable.encode_injective (congrFun hxy k))
  exact Prod.ext (hconst x hx y hy (fun k => (hnames k).1.symm)
    (fun k => (hnames k).2.symm)) (funext fun k => (hnames k).1)

theorem predecessor_auxiliary_kernel_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (R : Y → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (κ : Kernel Y Y) (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) → κ x=κ y)
    (K : ℕ) :
    observationEntropyRate μ T (heightClip Q K) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (fun x => (κ x,entireFutureObservation T Q x)) inferInstance) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  exact (predecessor_countable_auxiliary_entropyRate_le μ hT Q hQ B hB href decode hdecode
    R hR hfinite K).trans (add_le_add
      (combined_future_kernel_entropy_le μ hT.measurable Q R hQ hR κ E hE hconst B hB)
      le_rfl)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixIntrinsicCandidates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From intrinsic long-box leaves to an actual regional conditional kernel -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n)

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
theorem timeParam_injective_of_free_at_coordinate
    (z : (UpperRootTransverse n × T) × c.Time)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (C.timeParam c hP hf g z) v = C.timeParam c hP hf g z → v = 1) :
    Function.Injective (fun t => C.timeParam c hP hf g (z.1,t)) := by
  apply C.timeParam_injective_of_free c hP hf g z.1
  apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots n))
    (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) (c.word z.2)
    (positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hf z.2))
  simpa only [C.timeParam_eq_action] using hfree

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixFutureMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing the actual intrinsic masses in a root box -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma uncenteredIntrinsicProduct_eq_rebase_map
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    B.uncenteredIntrinsicProduct μ z =
      (c.remainingTimeProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map
        (c.remainingRebase hP₀ hf z.2).symm := by
  let W := c.remainingWordHomeomorph hP₀ hf
  let E := c.remainingRebase hP₀ hf z.2
  change ((c.remainingIntrinsicProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map
    (Homeomorph.mulLeft (W z.2))).map W.symm =
    ((c.remainingIntrinsicProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map W.symm).map E.symm
  rw [Measure.map_map W.symm.measurable (Homeomorph.mulLeft (W z.2)).measurable,
    Measure.map_map E.symm.measurable W.symm.measurable]
  congr 1
  funext v
  apply E.injective
  rw [Function.comp_apply, Function.comp_apply, E.apply_symm_apply]
  apply W.injective
  rw [c.remainingRebase_word hP₀ hf, W.apply_symm_apply, W.apply_symm_apply]
  exact inv_mul_cancel_left (W z.2) v

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma rebase_image_futureFiber
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (m : ℕ) (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    (c.remainingRebase hP₀ hf z.2) ''
      {t | ∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g (z.1,t))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g z))} =
      c.remainingFutureAtom ell hell Q m (C.timeParam c hP₀ hf g z) := by
  let E := c.remainingRebase hP₀ hf z.2
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩ k
    rw [← C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
    exact ht k
  · intro hu
    refine ⟨E.symm u, ?_, E.apply_symm_apply u⟩
    intro k
    rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 (E.symm u)]
    change Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
      (rightAction (C.timeParam c hP₀ hf g z) (c.word (E (E.symm u))))) = _
    rw [E.apply_symm_apply]
    exact hu k

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixAmbientFuture
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matching box future conditionals with ambient root-orbit measures -/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_map_equiv {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (e : Y ≃ᵐ Z) (A : Set Y) :
    ((anchorNormalize ν A).restrict A).map e =
      (anchorNormalize (ν.map e) (e '' A)).restrict (e '' A) := by
  rw [anchorNormalize_map_equiv, e.measurableEmbedding.restrict_map,
    e.preimage_image]

namespace RootPrefixBox
variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
/-- The box expression, once unrestricted, is exactly the intrinsic
whole-future measure pushed along the actual root orbit through its sample. -/
lemma map_uncentered_future_eq_ambient
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (m : ℕ) (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP₀ hf g
    let A := {t | ∀ k : ℕ, Q (T^[k+m] (F (z.1,t)))=Q (T^[k+m] (F z))}
    ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) A).restrict A).map
        (fun t => F (z.1,t)) =
      ((anchorNormalize (c.remainingTimeProduct hP₀ hf μ (F z))
        (c.remainingFutureAtom ell hell Q m (F z))).restrict
        (c.remainingFutureAtom ell hell Q m (F z))).map
        (fun u => rightAction (F z) (c.word u)) := by
  let F := C.timeParam c hP₀ hf g
  let E := (c.remainingRebase hP₀ hf z.2).toMeasurableEquiv
  let A := {t | ∀ k : ℕ,
    Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m] (F (z.1,t))) =
    Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m] (F z))}
  let W := fun u => rightAction (F z) (c.word u)
  have hW : Measurable W :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hF : (fun t => F (z.1,t)) = W ∘ E := by
    funext t
    exact C.timeParam_rebased c hP₀ hf g z.1 z.2 t
  have hM : (B.uncenteredIntrinsicProduct μ z).map E =
      c.remainingTimeProduct hP₀ hf μ (F z) := by
    rw [B.uncenteredIntrinsicProduct_eq_rebase_map μ z]
    exact E.map_map_symm
  change ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) A).restrict A).map
    (fun t => F (z.1,t)) = _
  rw [hF, ←Measure.map_map hW E.measurable,
    normalized_restriction_map_equiv, hM]
  rw [show E '' A = c.remainingFutureAtom ell hell Q m (F z) from
    rebase_image_futureFiber ell hell Q m z]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LocalFutureKernelConstancy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise constancy of the actual future kernel on a conull chart

The normalized leaf measure depends only on the transverse coordinate.
After removing one null set, equal transverse coordinates and equal
complete future names therefore give exactly the same ambient kernel.
This is stronger than constancy for almost every pair sampled from that
kernel, and is the local input for the refined-future entropy comparison.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries=allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

lemma ae_coordinates_mem_of_ae_coordinateMeasure
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X (d+1)))
    (E : Set ((UpperRootTransverse (d+1) × V) × c.Time))
    (hE : ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ E) :
    ∀ᵐ x ∂μ, ∀ z ∈ B.domain, C.timeParam c hP hf g z=x → z ∈ E := by
  have hsub : ∀ᵐ z ∂μ.comap B.param, z.val ∈ E :=
    ae_of_ae_map measurable_subtype_coe.aemeasurable hE
  have H : ∀ᵐ x ∂(μ.comap B.param).map B.param,
      ∀ z : B.domain, B.param z=x → z.val ∈ E := by
    apply B.embedding.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hsub] with z hz w hw
    have he : w=z := B.embedding.injective hw
    simpa only [he] using hz
  rw [B.embedding.measurableEmbedding.map_comap] at H
  have H' := (ae_restrict_iff' B.range_open.measurableSet).mp H
  filter_upwards [H'] with x hx
  intro z hz hzx
  exact hx ⟨⟨z,hz⟩,hzx⟩ ⟨z,hz⟩ hzx

theorem exists_conull_futureKernel_coordinate_constancy
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v=x → v=1)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (κ : Kernel (X (d+1)) (X (d+1)))
    (hκ : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP hf g
    ∃ E : Set ((UpperRootTransverse (d+1) × V) × c.Time),
      (∀ᵐ z ∂B.coordinateMeasure μ, z ∈ E) ∧
      ∀ z ∈ E, ∀ w ∈ E, z.1=w.1 →
        (∀ k : ℕ, Q (T^[k+1] (F z))=Q (T^[k+1] (F w))) →
        κ (F z)=κ (F w) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP hf g
  let K := B.regularLeafKernel R hBR μ hfree
  let L := fun z : (UpperRootTransverse (d+1) × V) × c.Time =>
    ((anchorNormalize (K z.1) (countableFutureFiber T Q F z)).restrict
      (countableFutureFiber T Q F z)).map (fun t => F (z.1,t))
  have hspec : ∀ᵐ z ∂B.coordinateMeasure μ, κ (F z)=L z := by
    filter_upwards [B.ae_coordinate_of_ambient μ hκ,
      B.ae_normalized_uncentered_eq_regularLeaf R hBR μ hfree] with z hz hn
    rw [hz,←B.map_uncentered_future_eq_ambient μ ell hell Q 1 z]
    change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
      (countableFutureFiber T Q F z)).restrict
      (countableFutureFiber T Q F z)).map (fun t => F (z.1,t)))=L z
    rw [hn]
  refine ⟨{z | κ (F z)=L z},hspec,?_⟩
  intro z hz w hw hzw hname
  have hfiber : countableFutureFiber T Q F z=countableFutureFiber T Q F w := by
    ext t
    simp only [countableFutureFiber,mem_ofPred_eq]
    rw [hzw]
    exact forall_congr' (fun k => by rw [hname k])
  rw [hz,hw]
  change ((anchorNormalize (K z.1) (countableFutureFiber T Q F z)).restrict
      (countableFutureFiber T Q F z)).map (fun t => F (z.1,t)) = _
  rw [hzw,hfiber]

/-- One ambient conull set works for every pair of coordinates in this
actual injective box, rather than merely for almost every sampled pair. -/
theorem exists_conull_futureKernel_chart_constancy
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v=x → v=1)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (κ : Kernel (X (d+1)) (X (d+1)))
    (hκ : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP hf g
    ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
      ∀ z ∈ B.domain, ∀ w ∈ B.domain, F z ∈ E → F w ∈ E → z.1=w.1 →
        (∀ k : ℕ, Q (T^[k+1] (F z))=Q (T^[k+1] (F w))) →
        κ (F z)=κ (F w) := by
  obtain ⟨E,hE,hconst⟩ := B.exists_conull_futureKernel_coordinate_constancy
    R hBR μ hfree ell hell Q κ hκ
  let F := C.timeParam c hP hf g
  let A := {x | ∀ z ∈ B.domain, F z=x → z ∈ E}
  refine ⟨A,B.ae_coordinates_mem_of_ae_coordinateMeasure μ E hE,?_⟩
  intro z hz w hw hzA hwA hzw hname
  exact hconst z (hzA z hz rfl) w (hwA w hw rfl) hzw hname

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureCountableCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable family of boxes containing complete future fibers

The family is chosen before the sample. Bounded future fibers, transported
to the sampled coordinates, fit into one member of this fixed family.
This is the countability needed for gluing the local future laws.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]

theorem exists_countable_box_containing_futureFiber
    (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    (s : UpperRootTransverse n × V) (t : c.Time)
    (hinj : Function.Injective (fun u => C.timeParam c hP hf g (s,u)))
    (T : X n → X n) (Q : X n → ℕ) (m : ℕ) (R : ℝ)
    (hbound : ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+m] (rightAction (C.timeParam c hP hf g (s,t)) (c.word v))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))) → v ∈ c.cube R) :
    ∃ B ∈ C.wholeFutureBoxFamily c hP hf g,
      s ∈ B.transverse ∧ t ∈ B.time ∧
      ∃ j : ℕ, B.time = c.cube (1+j) ∧
      {u | ∀ k : ℕ, Q (T^[k+m] (C.timeParam c hP hf g (s,u))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))} ⊆ B.time := by
  let E := c.remainingRebase hP hf t
  let K : Set c.Time := {t} ∪ E.symm '' c.closedCube R
  have hK : IsCompact K := isCompact_singleton.union
    ((c.closedCube_compact R).image E.symm.continuous)
  obtain ⟨j,hj⟩ := hK.elim_directed_cover (c.remainingWindow 1)
    (c.remainingWindow_open 1) (by rw [c.remainingWindow_cover]; exact subset_univ K)
    (c.remainingWindow_mono 1).directed_le
  obtain ⟨B,hB,hs⟩ := C.longBoxFamily_covers c hP hf g 1 j s hinj
  have htime := C.longBoxFamily_time c hP hf g 1 j B hB
  refine ⟨B, mem_iUnion.mpr ⟨j,hB⟩, hs, ?_, j, htime, ?_⟩
  · rw [htime]
    exact hj (Or.inl rfl)
  · intro u hu
    rw [htime]
    apply hj
    have hv : E u ∈ c.cube R := by
      apply hbound
      intro k
      rw [← C.timeParam_rebased c hP hf g s t u]
      exact hu k
    exact Or.inr ⟨E u,c.cube_subset_closedCube R hv,E.symm_apply_apply u⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixCountableAtlas
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countably many translated root charts cover the quotient -/

noncomputable section
open Set TopologicalSpace

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V]

theorem exists_countable_translates_cover (C : RootPrefixCoordinates n P V)
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n)
    (z₀ : (UpperRootTransverse n × V) × c.Time) :
    ∃ S : Set (G n), S.Countable ∧
      (⋃ g ∈ S, range (C.timeParam c hP hf g)) = univ := by
  have hopen g : IsOpen (range (C.timeParam c hP hf g)) :=
    (C.timeParam_localHomeomorph c hP hf g).isOpenMap.isOpen_range
  obtain ⟨S,_,hS,heq⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => range (C.timeParam c hP hf g)) (fun g _ => hopen g)
  refine ⟨S,hS,heq.trans ?_⟩
  apply eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | _ a =>
    let b := C.groupParam (z₀.1.1,(z₀.1.2,c.remainingWordHomeomorph hP hf z₀.2))
    refine mem_iUnion.mpr ⟨a*b⁻¹,mem_iUnion.mpr ⟨mem_univ _,z₀,?_⟩⟩
    change Quotient.mk _ ((a*b⁻¹)*b) = Quotient.mk _ a
    simp only [inv_mul_cancel_right]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_GlobalFutureKernelConstancy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual future kernel is constant on conull leaf-future fibers

A fixed countable atlas of long root boxes lets the pointwise local
statement hold on one ambient conull set. Any bounded root-future fiber
fits into one of these boxes, so two good points on the same root orbit
with the same future names have identical ambient kernels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]

theorem exists_conull_leafFutureKernel_constancy
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ)
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
        (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
    (κ : Kernel (X (d+1)) (X (d+1)))
    (hκ : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    ∃ E : Set (X (d+1)), (∀ᵐ x ∂μ, x ∈ E) ∧
      ∀ x ∈ E, ∀ y ∈ E, (∃ u : c.Time, rightAction x (c.word u)=y) →
        (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) → κ x=κ y := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree := ae_upperRoot_stabilizer_trivial d μ hA
  obtain ⟨S,hS,hcover⟩ := C.exists_countable_translates_cover c hP hf z₀
  let : Countable S := hS.to_subtype
  let (g : S) (j : ℕ) : Countable
      {B : RootPrefixBox C c hP hf g.val // B ∈ C.longBoxFamily c hP hf g.val 1 j} :=
    (C.longBoxFamily_countable c hP hf g.val 1 j).to_subtype
  let I := Σ g : S, Σ j : ℕ,
    {B : RootPrefixBox C c hP hf g.val // B ∈ C.longBoxFamily c hP hf g.val 1 j}
  let B (i : I) := i.2.2.val
  have hBR (i : I) : (B i).time ⊆ c.remainingWindow (1+i.2.1) 0 := by
    rw [C.longBoxFamily_time c hP hf i.1.val 1 i.2.1 (B i) i.2.2.prop]
    simp only [EliminationChain.remainingWindow,Nat.cast_zero,add_zero,subset_refl]
  choose E hE hconst using fun i : I =>
    (B i).exists_conull_futureKernel_chart_constancy (1+i.2.1) (hBR i)
      μ hfree ell hell Q κ hκ
  let A := {x | (∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v=x → v=1) ∧
    (∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+1] (rightAction x (c.word v)))=Q (T^[k+1] x)) →
        v ∈ c.cube R) ∧ ∀ i : I, x ∈ E i}
  have hAgood : ∀ᵐ x ∂μ, x ∈ A := by
    filter_upwards [hfree,hbound,ae_all_iff.mpr hE] with x hx hb he
    exact ⟨hx,hb,he⟩
  refine ⟨A,hAgood,?_⟩
  intro x hx y hy hrel hname
  obtain ⟨u,hu⟩ := hrel
  have hxc : x ∈ ⋃ g ∈ S, range (C.timeParam c hP hf g) := by rw [hcover]; trivial
  obtain ⟨g,hg,z,hz⟩ := by simpa only [mem_iUnion,mem_range] using hxc
  have hi := C.timeParam_injective_of_free_at_coordinate c hP hf g z
    (by simpa only [hz] using hx.1)
  obtain ⟨R,hR⟩ := hx.2.1
  obtain ⟨B',hB',hs,ht,j,hj,hfuture⟩ := C.exists_countable_box_containing_futureFiber
    c hP hf g z.1 z.2 hi T Q 1 R (by simpa only [hz] using hR)
  obtain ⟨j',hj'⟩ := mem_iUnion.mp hB'
  let i : I := ⟨⟨g,hg⟩,j',⟨B',hj'⟩⟩
  let w : (UpperRootTransverse (d+1) × V) × c.Time :=
    (z.1,(c.remainingRebase hP hf z.2).symm u)
  have hw : C.timeParam c hP hf g w=y := by
    dsimp only [w]
    rw [C.timeParam_rebased c hP hf g z.1 z.2,
      (c.remainingRebase hP hf z.2).apply_symm_apply,hz,hu]
  have hwt : w.2 ∈ B'.time := by
    apply hfuture
    intro k
    change Q (T^[k+1] (C.timeParam c hP hf g w))=
      Q (T^[k+1] (C.timeParam c hP hf g z))
    rw [hw,hz]
    exact hname k
  have H := hconst i z ⟨hs,ht⟩ w ⟨hs,hwt⟩
    (by simpa only [i,B,hz] using hx.2.2 i)
    (by simpa only [i,B,hw] using hy.2.2 i) rfl
    (fun k => by simpa only [i,B,hz,hw] using (hname k).symm)
  simpa only [i,B,hz,hw] using H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_AuxiliaryRootInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual root information bounds from auxiliary recurrent fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

/-- Once the recurrent auxiliary observation removes the transverse
coordinates, its only entropy cost is its countable Shannon sum. All
kernel terms here are the intrinsic root-future measures. -/
theorem predecessor_entropyRate_le_root_information_add_auxiliary_oai
    {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
        (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    {M : ℕ} (B : X (d+1) → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y →
      Q (rightAction x (diagonalOneParameter ell hell (-1)))=
        Q (rightAction y (diagonalOneParameter ell hell (-1))) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ)
    (hdecode : ∀ x, decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x)
    (R : X (d+1) → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (E : Set (X (d+1))) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hrelative : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      (∀ k : ℕ, R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        R ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      ∃ u : c.Time, rightAction x (c.word u)=y)
    (L : ℕ) :
    observationEntropyRate μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
      (heightClip Q L) ≤
      (∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨F,hF,hconst⟩ := C.exists_conull_leafFutureKernel_constancy c hP hf z₀
    μ ell hell Q hbound κ hversion
  have hEF : ∀ᵐ x ∂μ, x ∈ F ∩ E := hF.and hE
  have hk : ∀ x ∈ F ∩ E, ∀ y ∈ F ∩ E,
      (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) → κ x=κ y := by
    intro x hx y hy hq hr
    exact hconst x hx.1 y hy.1 (hrelative x hx.2 y hy.2 hq hr) hq
  have H := predecessor_auxiliary_kernel_entropyRate_le μ hT Q hQ B hB href
    decode hdecode R hR hfinite κ (F ∩ E) hEF hk L
  have HI := c.predecessor_root_information d hP hf μ hA ell hell Q hQ κ
    hstat hself hversion hmass B hB href decode hdecode
  rw [HI] at H
  exact H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary_oai.{u_1} := @OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary_oai.{u_1}
