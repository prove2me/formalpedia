-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:47:38.053078+00:00
-- url     : https://prove2.me/submissions/83104221-ae43-46c7-9777-ac05b6fa43ac

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke018
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_exists_branching_cover_future_observation

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets

lemma matrixBall_mono {n : ℕ} {r s : ℝ} (hrs : r ≤ s) :
    matrixBall n r ⊆ matrixBall n s := by
  intro g hg i j
  exact (hg i j).trans_le hrs



end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
namespace PrimeDegreePackets

lemma matrixBall_nhds_basis {n : ℕ} {U : Set (G n)} (hU : U ∈ 𝓝 (1 : G n)) :
    ∃ r : ℝ, 0 < r ∧ matrixBall n r ⊆ U := by
  have hv : Topology.IsInducing (fun g : G n => g.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [hv.nhds_eq_comap] at hU
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r,hr,fun g hg => hVU (hsub ?_)⟩
  change dist g.1 (1 : G n).1 < r
  rw [dist_eq_norm]
  exact (Matrix.norm_lt_iff hr).mpr hg

 

lemma local_uniform_chart_injective {n : ℕ} (x : X n) :
    ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧ ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ U, Set.InjOn (fun g => rightAction y g) (matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨V,hVo,hgV,hVi⟩ :=
      (quotient_covering n).isLocalHomeomorph.isLocallyInjective g
    have hpre : (fun u : G n => g*u) ⁻¹' V ∈ 𝓝 (1 : G n) := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      simpa using hVo.mem_nhds hgV
    obtain ⟨W,hWo,h1W,hWW⟩ := exists_open_nhds_one_mul_subset hpre
    obtain ⟨r,hr,hrW⟩ := matrixBall_nhds_basis (hWo.mem_nhds h1W)
    refine ⟨(fun u => Quotient.mk _ (g*u)) '' W, ?_, ?_, r,hr,?_⟩
    · rw [← Set.image_image]
      exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft g).isOpenMap _ hWo)
    · exact ⟨1,h1W,by simp⟩
    · rintro y ⟨u,hu,rfl⟩ v hv w hw heq
      have hgv : g*(u*v) ∈ V := hWW (Set.mul_mem_mul hu (hrW hv))
      have hgw : g*(u*w) ∈ V := hWW (Set.mul_mem_mul hu (hrW hw))
      have He : g*(u*v) = g*(u*w) := hVi hgv hgw (by
        change Quotient.mk _ ((g*u)*v) = Quotient.mk _ ((g*u)*w) at heq
        simpa only [mul_assoc] using heq)
      exact mul_left_cancel (mul_left_cancel He)


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationCovers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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



lemma diagonal_conjugation_expansion {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ r : ℝ, 0 < r →
      (MulAut.conj (diagonalOneParameter ell hell (-1))) '' matrixBall n r ⊆ matrixBall n (L*r) := by
  let L : ℝ := 1 + ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i)
  have hsum : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
  refine ⟨L,by dsimp [L] <;> linarith,?_⟩
  rintro r hr g ⟨h,hh,rfl⟩ i j
  have he : (MulAut.conj (diagonalOneParameter ell hell (-1)) h).1 i j =
      Real.exp (ell j-ell i)*h.1 i j := by
    change (diagonalOneParameter ell hell (-1)*h*(diagonalOneParameter ell hell (-1))⁻¹).1 i j = _
    rw [← diagonalOneParameter_neg]
    convert conjugation_entry ell hell h (-1) i j using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  have hLij : Real.exp (ell j-ell i) ≤ L := by
    have H : Real.exp (ell j-ell i) ≤ ∑ i : Fin n, ∑ j : Fin n, Real.exp (ell j-ell i) :=
      (Finset.single_le_sum (f := fun k : Fin n => Real.exp (ell k-ell i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, Real.exp (ell l-ell k))
          (fun _ _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (Finset.mem_univ i))
    dsimp [L]
    linarith
  change |(MulAut.conj (diagonalOneParameter ell hell (-1)) h).1 i j -
    (1 : Matrix (Fin n) (Fin n) ℝ) i j| < L*r
  rw [he]
  by_cases hij : i = j
  · subst j
    simpa only [sub_self,Real.exp_zero,one_mul] using (hh i i).trans_le
      (le_mul_of_one_le_left hr.le (by dsimp [L] <;> linarith))
  · have Hh : |h.1 i j| < r := by simpa only [Matrix.one_apply_ne hij,sub_zero] using hh i j
    simp only [Matrix.one_apply_ne hij,sub_zero]
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact (mul_lt_mul_of_pos_left Hh (Real.exp_pos _)).trans_le
      (mul_le_mul_of_nonneg_right hLij hr.le)

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rightAction_conjugation {n : ℕ} (a : G n) (x : X n) (g : G n) :
    rightAction (rightAction x g) a =
      rightAction (rightAction x a) (MulAut.conj a⁻¹ g) := by
  simp only [rightAction_mul,MulAut.conj_apply,inv_inv]
  congr 1
  group

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma conjugation_iterate {H : Type*} [Group H] (a g : H) (j : ℕ) :
    (MulAut.conj a⁻¹)^[j] g = (a^j)⁻¹*g*a^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [MulAut.conj_apply,inv_inv,pow_succ,_root_.mul_inv_rev]
    group



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerContraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded diagonal returns in a root centralizer

A matrix centralizing one root can have entries outside the opposite-root
centralizer only in expanding directions of a suitable diagonal flow.
Bounded conjugates along arbitrarily late times therefore centralize both
roots. This is the matrix step in EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma eq_zero_of_bounded_exp_mul
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop)
    {c : ℝ} (hc : 0 < c) (a B : ℝ)
    (hb : ∀ᶠ k in atTop, |Real.exp (c * t k) * a| ≤ B) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.mpr ha
  have he := Real.tendsto_exp_atTop.comp (ht.const_mul_atTop hc)
  have hexp : Tendsto (fun k => |Real.exp (c * t k) * a|) atTop atTop := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _), Function.comp_apply] using he.atTop_mul_const ha'
  exact (not_isBoundedUnder_of_tendsto_atTop hexp) ⟨B, eventually_map.mpr hb⟩

/-- Each strictly expanding matrix entry must vanish if the conjugates
remain bounded along a sequence of times tending to infinity. -/
lemma conjugation_expanding_entry_eq_zero {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (g : G n)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (B : ℝ)
    (hb : ∀ᶠ k in atTop, ∀ r s,
      |(diagonalOneParameter ell hell (t k) * g *
        diagonalOneParameter ell hell (-t k)).val r s| ≤ B)
    {r s : Fin n} (hrs : ell s < ell r) : g.val r s = 0 := by
  apply eq_zero_of_bounded_exp_mul ht (sub_pos.mpr hrs) _ B
  filter_upwards [hb] with k hk
  simpa only [conjugation_entry] using hk r s

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_GenericLatticeStabilizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SummablePartitionBoundaries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instLocallyCompactSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing partition cuts with summable boundary returns

Almost every real cut of a measurable real-valued function has summable
strip masses for any summable sequence of widths. Invariant dynamics
therefore avoid those shrinking strips eventually almost everywhere.
This supplies the boundary control for partitions subordinate to
contracting root leaves.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

lemma measurable_realBoundaryStrip_mass (μ : Measure Y) [SFinite μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    Measurable (fun r => μ (realBoundaryStrip f r ε)) := by
  have hs : MeasurableSet {z : ℝ × Y | |f z.2-z.1| ≤ ε} := by
    simp only [abs_le]
    exact (measurableSet_le measurable_const ((hf.comp measurable_snd).sub measurable_fst)).inter
      (measurableSet_le ((hf.comp measurable_snd).sub measurable_fst) measurable_const)
  exact measurable_measure_prodMk_left hs

lemma lintegral_realBoundaryStrip_mass (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    (∫⁻ r : ℝ, μ (realBoundaryStrip f r ε)) = ENNReal.ofReal (2*ε) := by
  let S : Set (ℝ × Y) := {z | |f z.2-z.1| ≤ ε}
  have hS : MeasurableSet S := by
    simp only [S,abs_le]
    exact (measurableSet_le measurable_const ((hf.comp measurable_snd).sub measurable_fst)).inter
      (measurableSet_le ((hf.comp measurable_snd).sub measurable_fst) measurable_const)
  change (∫⁻ r : ℝ, μ (Prod.mk r ⁻¹' S)) = _
  rw [←Measure.prod_apply hS,Measure.prod_apply_symm hS]
  have hsection (x : Y) : (fun r : ℝ => (r,x)) ⁻¹' S = Icc (f x-ε) (f x+ε) := by
    ext r
    change |f x-r| ≤ ε ↔ f x-ε ≤ r ∧ r ≤ f x+ε
    rw [abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp_rw [hsection,Real.volume_Icc,show ∀ x : Y, f x+ε-(f x-ε)=2*ε by intro x; ring]
  simp only [lintegral_const,measure_univ,mul_one]

lemma fiber_null_of_summable_realBoundaryStrip_mass
    (μ : Measure Y) {f : Y → ℝ} (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (r : ℝ)
    (hr : (∑' n, μ (realBoundaryStrip f r (ε n))) ≠ ∞) :
    μ {x | f x=r} = 0 := by
  by_contra h
  have hle : (∑' _ : ℕ, μ {x | f x=r}) ≤ ∑' n, μ (realBoundaryStrip f r (ε n)) := by
    apply ENNReal.tsum_le_tsum
    intro n
    apply measure_mono
    intro x hx
    change |f x-r| ≤ ε n
    rw [hx,sub_self,abs_zero]
    exact hε n
  rw [ENNReal.tsum_const_eq_top_of_ne_zero h] at hle
  exact hr (top_le_iff.mp hle)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_QuantitativeCutAverage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative selection of a real cut

A nonnegative cost with bounded total integral has a cut in any given
interval with cost at most twice the interval average. This will control
all dyadic boundary widths at once.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

theorem exists_cut_cost_le
    (F : ℝ → ℝ≥0∞) {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hI : (∫⁻ r, F r) ≤ ENNReal.ofReal C) :
    ∃ r ∈ Ioo a b, F r ≤ ENNReal.ofReal (2*C/(b-a)) := by
  by_contra h
  have hall : ∀ r ∈ Ioo a b, ENNReal.ofReal (2*C/(b-a)) ≤ F r := by
    intro r hr
    exact (lt_of_not_ge (fun hle => h ⟨r,hr,hle⟩)).le
  have hlower : ENNReal.ofReal (2*C/(b-a))*volume (Ioo a b) ≤
      ∫⁻ r in Ioo a b, F r := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hall r hr
  have hbound : ENNReal.ofReal (2*C) ≤ ENNReal.ofReal C := by
    have he : ENNReal.ofReal (2*C/(b-a))*volume (Ioo a b) = ENNReal.ofReal (2*C) := by
      rw [Real.volume_Ioo,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [(sub_pos.mpr hab).ne']
    rw [he] at hlower
    exact hlower.trans ((lintegral_mono' Measure.restrict_le_self le_rfl).trans hI)
  have := (ENNReal.ofReal_le_ofReal_iff hC.le).mp hbound
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TriangularStabilizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A trace gap for positive triangular lattice stabilizers

The trace of an actual lattice stabilizer is an integer.  A positive
triangular stabilizer of determinant one whose trace is less than `n+1`
therefore has all diagonal entries equal to one.  At the generic lattices
used in the entropy argument it is the identity.
-/

noncomputable section
open Matrix Set
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma sum_ge_card_of_pos_prod_one {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (hp : ∏ i, a i = 1) :
    (Fintype.card ι : ℝ) ≤ ∑ i, a i := by
  have hlog : ∑ i, Real.log (a i) = 0 := by
    rw [← Real.log_prod (fun i _ => (ha i).ne'), hp, Real.log_one]
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Real.log_le_sub_one_of_pos (ha i)
  simpa only [hlog, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sub_nonneg] using h

lemma eq_one_of_pos_prod_one_sum_card {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (hp : ∏ i, a i = 1)
    (hs : ∑ i, a i = Fintype.card ι) : ∀ i, a i = 1 := by
  classical
  intro j
  by_contra hj
  have hlog : ∑ i, Real.log (a i) = 0 := by
    rw [← Real.log_prod (fun i _ => (ha i).ne'), hp, Real.log_one]
  have h := Finset.sum_lt_sum
    (fun i (_ : i ∈ Finset.univ) => Real.log_le_sub_one_of_pos (ha i))
    ⟨j, Finset.mem_univ j, Real.log_lt_sub_one_of_pos (ha j) hj⟩
  simp only [hlog, Finset.sum_sub_distrib, hs, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sub_self, lt_self_iff_false] at h

/-- Actual lattice stabilizers have integral trace, by conjugating them
back to the integer special linear group. -/
theorem stabilizer_trace_integral {n : ℕ} (x : X n) (g : G n)
    (hfix : rightAction x g = x) : ∃ z : ℤ, g.val.trace = z := by
  obtain ⟨q, rfl⟩ := Quotient.exists_rep x
  have heq : Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (q * g) =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) q := hfix
  have hΓ : q * g * q⁻¹ ∈ integralGroup n :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact heq.symm)
  obtain ⟨γ, hγ⟩ := hΓ
  refine ⟨γ.val.trace, ?_⟩
  have ht : (q * g * q⁻¹).val.trace = g.val.trace := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  rw [← ht, ← hγ]
  change (γ.val.map (Int.castRingHom ℝ)).trace = _
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, Int.cast_sum]
  rfl

/-- Positivity and the integral trace gap force the diagonal to be one. -/
theorem triangular_stabilizer_diagonal_eq_one {n : ℕ} (x : X n) (g : G n)
    (hfix : rightAction x g = x) (htri : g.val.IsUpperTriangular)
    (hpos : ∀ i, 0 < g.val i i) (htrace : g.val.trace < n + 1) :
    ∀ i, g.val i i = 1 := by
  have hp : ∏ i, g.val i i = 1 :=
    (Matrix.det_of_isUpperTriangular htri).symm.trans g.property
  have hlo : (n : ℝ) ≤ g.val.trace := by
    simpa only [Fintype.card_fin, Matrix.trace, Matrix.diag] using
      sum_ge_card_of_pos_prod_one (fun i => g.val i i) hpos hp
  obtain ⟨z, hz⟩ := stabilizer_trace_integral x g hfix
  have hzlo : (n : ℤ) ≤ z := by exact_mod_cast hz ▸ hlo
  have hzhi : z < (n : ℤ) + 1 := by exact_mod_cast hz ▸ htrace
  have hzn : z = n := by omega
  apply eq_one_of_pos_prod_one_sum_card (fun i => g.val i i) hpos hp
  simp only [Fintype.card_fin]
  change g.val.trace = (n : ℝ)
  rw [hz, hzn]
  simp

/-- In the generic locus a positive triangular stabilizer below the first
possible nonunipotent integral trace is trivial. -/
theorem triangular_stabilizer_eq_one {d : ℕ} (x : X (d+1))
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (g : G (d+1)) (hfix : rightAction x g = x)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i)
    (htrace : g.val.trace < (d+1 : ℕ) + 1) : g = 1 := by
  have hdiag := triangular_stabilizer_diagonal_eq_one x g hfix htri hpos htrace
  apply stabilizer_trivial_of_identity_column x hx g hfix 0
  intro r
  by_cases hr : r = 0
  · subst r
    simpa only [Matrix.one_apply_eq] using hdiag 0
  · have hlt : (0 : Fin (d+1)) < r := Fin.pos_iff_ne_zero.mpr hr
    rw [htri hlt, Matrix.one_apply_ne hr]

lemma upperTriangular_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  change (∑ j, A i j * B j i) = _
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

lemma specialLinear_upperTriangular_inv {n : ℕ} (g : G n)
    (htri : g.val.IsUpperTriangular) : (g⁻¹).val.IsUpperTriangular := by
  let : Invertible g.val := Matrix.invertibleOfIsUnitDet g.val
    (g.property.symm ▸ isUnit_one)
  have he : (g⁻¹).val = g.val⁻¹ := by
    rw [Matrix.inv_def, g.property, Ring.inverse_one, one_smul]
    rfl
  rw [he]
  exact Matrix.blockTriangular_inv_of_blockTriangular htri

/-- A sufficiently small triangular lift along a positive unipotent leaf
is the leaf element itself. The radius is independent of the lattice. -/
theorem exists_uniform_triangular_lift_radius (d : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : X (d+1)),
      (∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) →
      ∀ (u g : G (d+1)), u.val.IsUpperTriangular → (∀ i, u.val i i = 1) →
      g ∈ matrixBall (d+1) r → g.val.IsUpperTriangular →
      rightAction x u = rightAction x g → u = g := by
  let V : Set (G (d+1)) := {g | (∀ i, 0 < (g⁻¹).val i i) ∧
    (g⁻¹).val.trace < (d+1 : ℕ) + 1}
  have htr : Continuous (fun g : G (d+1) => (g⁻¹).val.trace) := by
    change Continuous (fun g : G (d+1) => ∑ i, (g⁻¹).val i i)
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hV : V ∈ 𝓝 (1 : G (d+1)) := by
    apply IsOpen.mem_nhds
    · apply IsOpen.inter
      · change IsOpen {g : G (d+1) | ∀ i, 0 < (g⁻¹).val i i}
        simp only [Set.ofPred_forall]
        apply isOpen_iInter_of_finite
        intro i
        exact isOpen_lt continuous_const (by fun_prop)
      · exact isOpen_lt htr continuous_const
    · constructor
      · intro i
        simp
      · simp [Matrix.trace, Matrix.diag]
  obtain ⟨r, hr, hrV⟩ := matrixBall_nhds_basis hV
  refine ⟨r, hr, ?_⟩
  intro x hx u g hu hdu hg hgt heq
  have hginv := specialLinear_upperTriangular_inv g hgt
  have hv := hrV hg
  let a := u * g⁻¹
  have hfix : rightAction x a = x := by
    dsimp [a]
    rw [← rightAction_mul, heq, rightAction_mul, mul_inv_cancel, rightAction_one]
  have hdiag (i : Fin (d+1)) : a.val i i = (g⁻¹).val i i := by
    change (u.val * (g⁻¹).val) i i = _
    rw [upperTriangular_mul_diag _ _ hu hginv, hdu, one_mul]
  have hat : a.val.IsUpperTriangular := hu.mul hginv
  have htrace : a.val.trace = (g⁻¹).val.trace := by
    apply Finset.sum_congr rfl
    intro i _
    exact hdiag i
  have ha : a = 1 := triangular_stabilizer_eq_one x hx a hfix hat
    (fun i => (hdiag i).symm ▸ hv.1 i) (htrace.symm ▸ hv.2)
  exact mul_inv_eq_one.mp ha

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixLogLength
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete subadditive length on the real special linear group

The logarithmic matrix length is symmetric under inversion and controls
small matrix displacements. It is used to construct observables with
uniform control along right root translations.
-/

noncomputable section
open Matrix Set Filter
open scoped Matrix.Norms.Operator Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrixLogLength_nonneg {n : ℕ} (g : G n) : 0 ≤ matrixLogLength g := by
  exact add_nonneg (Real.log_nonneg (by linarith [norm_nonneg (g.val-1)]))
    (Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)]))

private lemma log_norm_mul_sub_one_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Real.log (1+‖A*B-1‖) ≤ Real.log (1+‖A-1‖)+Real.log (1+‖B-1‖) := by
  have he : A*B-1 = (A-1)*(B-1)+(A-1)+(B-1) := by noncomm_ring
  have hn : ‖A*B-1‖ ≤ ‖A-1‖*‖B-1‖+‖A-1‖+‖B-1‖ := by
    rw [he]
    have h₁ := norm_add_le ((A-1)*(B-1)+(A-1)) (B-1)
    have h₂ := norm_add_le ((A-1)*(B-1)) (A-1)
    have h₃ := norm_mul_le (A-1) (B-1)
    linarith
  have H := Real.log_le_log (by positivity : 0 < 1+‖A*B-1‖)
    (show 1+‖A*B-1‖ ≤ (1+‖A-1‖)*(1+‖B-1‖) by nlinarith)
  rwa [Real.log_mul (by positivity) (by positivity)] at H

lemma matrixLogLength_mul_le {n : ℕ} (g h : G n) :
    matrixLogLength (g*h) ≤ matrixLogLength g+matrixLogLength h := by
  have h₁ := log_norm_mul_sub_one_le g.val h.val
  have h₂ := log_norm_mul_sub_one_le (h⁻¹).val (g⁻¹).val
  change Real.log (1+‖g.val*h.val-1‖)+Real.log (1+‖((g*h)⁻¹).val-1‖) ≤ _
  rw [_root_.mul_inv_rev]
  change Real.log (1+‖g.val*h.val-1‖)+Real.log (1+‖(h⁻¹).val*(g⁻¹).val-1‖) ≤ _
  unfold matrixLogLength
  linarith

theorem continuous_matrixLogLength (n : ℕ) : Continuous (matrixLogLength : G n → ℝ) := by
  have hinv : Continuous (fun g : G n => (g⁻¹).val) := by
    change Continuous (fun g : G n => Matrix.adjugate g.val)
    exact continuous_subtype_val.matrix_adjugate
  unfold matrixLogLength
  apply Continuous.add
  · exact (continuous_const.add (continuous_subtype_val.sub continuous_const).norm).log
      (fun g => (show 0 < 1+‖g.val-1‖ by positivity).ne')
  · exact (continuous_const.add (hinv.sub continuous_const).norm).log
      (fun g => (show 0 < 1+‖(g⁻¹).val-1‖ by positivity).ne')

lemma norm_sub_one_le_exp_matrixLogLength {n : ℕ} (g : G n) :
    ‖g.val-1‖ ≤ Real.exp (matrixLogLength g)-1 := by
  have hi : 0 ≤ Real.log (1+‖(g⁻¹).val-1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)])
  have he := Real.exp_le_exp.mpr (show Real.log (1+‖g.val-1‖) ≤ matrixLogLength g by
    unfold matrixLogLength
    linarith)
  rw [Real.exp_log (by positivity)] at he
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogDistance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic displacement distance on the lattice quotient

Taking the infimum over actual right translations gives a distance
independent of a representative. Its triangle inequality and translation
bound provide uniformly controlled real observables on the quotient.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_rightAction_eq {n : ℕ} (x y : X n) : ∃ g : G n, rightAction x g=y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      refine ⟨a⁻¹*b,?_⟩
      change Quotient.mk _ (a*(a⁻¹*b))=Quotient.mk _ b
      simp

lemma rightDisplacementLengths_nonempty {n : ℕ} (x y : X n) :
    (rightDisplacementLengths x y).Nonempty := by
  obtain ⟨g,hg⟩ := exists_rightAction_eq x y
  exact ⟨matrixLogLength g,g,hg,rfl⟩

lemma rightDisplacementLengths_bddBelow {n : ℕ} (x y : X n) :
    BddBelow (rightDisplacementLengths x y) := by
  refine ⟨0,?_⟩
  rintro r ⟨g,_,rfl⟩
  exact matrixLogLength_nonneg g

lemma quotientLogDistance_le_length {n : ℕ} (x y : X n) (g : G n)
    (hg : rightAction x g=y) : quotientLogDistance x y ≤ matrixLogLength g :=
  csInf_le (rightDisplacementLengths_bddBelow x y) ⟨g,hg,rfl⟩

lemma quotientLogDistance_triangle {n : ℕ} (x y z : X n) :
    quotientLogDistance x z ≤ quotientLogDistance x y+quotientLogDistance y z := by
  have H (g : G n) (hg : rightAction x g=y) :
      quotientLogDistance x z ≤ matrixLogLength g+quotientLogDistance y z := by
    have hle : quotientLogDistance x z-matrixLogLength g ≤ quotientLogDistance y z := by
      apply le_csInf (rightDisplacementLengths_nonempty y z)
      rintro r ⟨h,hh,rfl⟩
      have hpath : rightAction x (g*h)=z := by rw [←rightAction_mul,hg,hh]
      have h₁ := quotientLogDistance_le_length x z (g*h) hpath
      have h₂ := matrixLogLength_mul_le g h
      linarith
    linarith
  have hle : quotientLogDistance x z-quotientLogDistance y z ≤ quotientLogDistance x y := by
    apply le_csInf (rightDisplacementLengths_nonempty x y)
    rintro r ⟨g,hg,rfl⟩
    linarith [H g hg]
  linarith

lemma quotientLogDistance_symm {n : ℕ} (x y : X n) : quotientLogDistance x y=quotientLogDistance y x := by
  suffices H : ∀ x y : X n, quotientLogDistance y x ≤ quotientLogDistance x y from
    le_antisymm (H y x) (H x y)
  intro x y
  apply le_csInf (rightDisplacementLengths_nonempty x y)
  rintro r ⟨g,hg,rfl⟩
  have hback : rightAction y g⁻¹=x := by rw [←hg,rightAction_mul,mul_inv_cancel,rightAction_one]
  simpa only [matrixLogLength_inv] using quotientLogDistance_le_length y x g⁻¹ hback

/-- The distance from a fixed point changes by at most the length of a
right translation, uniformly in the point being translated. -/
theorem quotientLogDistance_right_bound {n : ℕ} (x y : X n) (g : G n) :
    |quotientLogDistance x (rightAction y g)-quotientLogDistance x y| ≤ matrixLogLength g := by
  have h₁ := quotientLogDistance_triangle x y (rightAction y g)
  have h₂ := quotientLogDistance_triangle x (rightAction y g) y
  have h₃ := quotientLogDistance_le_length y (rightAction y g) g rfl
  rw [quotientLogDistance_symm (rightAction y g) y] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma exists_rightAction_length_lt {n : ℕ} (x y : X n) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : G n, rightAction x g=y ∧ matrixLogLength g < quotientLogDistance x y+ε := by
  obtain ⟨r,⟨g,hg,hgr⟩,hr⟩ := exists_lt_of_csInf_lt (rightDisplacementLengths_nonempty x y)
    (show sInf (rightDisplacementLengths x y) < quotientLogDistance x y+ε by
      exact lt_add_of_pos_right _ hε)
  exact ⟨g,hg,by rwa [hgr]⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation and continuity of logarithmic quotient distance -/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_rightOrbit (n : ℕ) (x : X n) : Continuous (fun g : G n => rightAction x g) := by
  induction x using Quotient.inductionOn with
  | h a =>
      change Continuous (fun g : G n => Quotient.mk _ (a*g))
      exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

theorem continuous_quotientLogDistance (n : ℕ) (x : X n) :
    Continuous (quotientLogDistance x) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  apply continuous_iff_continuousAt.mpr
  intro g
  have hlen : Tendsto (fun h : G n => matrixLogLength (g⁻¹*h)) (𝓝 g) (𝓝 0) := by
    have H := ((continuous_matrixLogLength n).comp
      ((continuous_const : Continuous (fun _ : G n => g⁻¹)).mul continuous_id)).tendsto g
    simpa only [Function.comp_def,Pi.mul_apply,id_eq,inv_mul_cancel,matrixLogLength_one] using H
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlen.eventually (gt_mem_nhds hε)] with h hh
  have H := quotientLogDistance_right_bound x (Quotient.mk _ g) (g⁻¹*h)
  have he : rightAction (Quotient.mk _ g) (g⁻¹*h)=Quotient.mk _ h := by
    change Quotient.mk _ (g*(g⁻¹*h))=Quotient.mk _ h
    simp
  rw [he] at H
  change |quotientLogDistance x (Quotient.mk _ h)-quotientLogDistance x (Quotient.mk _ g)| < ε
  exact H.trans_lt hh

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootBasedMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full upper-root measures normalized at their current point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
lemma zeroTime_mem_cube {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) {R : ℝ} (hR : 0 < R) : c.zeroTime ∈ c.cube R := by
  induction c with
  | done => exact mem_univ _
  | step a b hab hP hb tail ih =>
      change (tail.zeroTime, (0 : ℝ)) ∈ tail.cube R ×ˢ Ioo (-R) R
      exact ⟨ih, by constructor <;> linarith⟩
end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalShannon
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

/-- Subadditivity for a nonnegative finite measure; its total mass need not be one. -/
theorem finiteShannon_joint_mass_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon p + Real.negMulLog (∑ z, p z) ≤
      finiteShannon (fun a => ∑ b, p (a,b)) +
      finiteShannon (fun b => ∑ a, p (a,b)) := by
  classical
  let r := ∑ z, p z
  have hr0 : 0 ≤ r := Finset.sum_nonneg (fun z _ => hp z)
  by_cases hr : r = 0
  · have hp0 : ∀ z, p z = 0 := by
      intro z
      have h := Finset.single_le_sum (fun w _ => hp w) (Finset.mem_univ z)
      change p z ≤ r at h
      exact le_antisymm (hr ▸ h) (hp z)
    simp [hp0, finiteShannon]
  have hnorm : ∑ z, p z / r = 1 := by rw [← Finset.sum_div]; exact div_self hr
  have H := mul_le_mul_of_nonneg_left
    (finiteShannon_joint_le (p := fun z => p z / r)
      (fun z => div_nonneg (hp z) hr0) hnorm) hr0
  have hrow : (∑ a, ∑ b, p (a,b)) = r := by simp only [r, Fintype.sum_prod_type]
  have hcol : (∑ b, ∑ a, p (a,b)) = r := by rw [Finset.sum_comm]; exact hrow
  have h1 := finiteShannon_mass_decomposition p hp
  have h2 := finiteShannon_mass_decomposition (fun a => ∑ b, p (a,b))
    (fun a => Finset.sum_nonneg (fun b _ => hp (a,b)))
  have h3 := finiteShannon_mass_decomposition (fun b => ∑ a, p (a,b))
    (fun b => Finset.sum_nonneg (fun a _ => hp (a,b)))
  simp only [hrow] at h2
  simp only [hcol] at h3
  simp only [← Finset.sum_div] at H
  change finiteShannon p = Real.negMulLog r + r * _ at h1
  linarith

/-- The finite entropy submodularity inequality `H(ABC)+H(A) ≤ H(AB)+H(AC)`. -/
theorem finiteShannon_submodular {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × (β × γ) → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon p + finiteShannon (fun a => ∑ z : β × γ, p (a,z)) ≤
      finiteShannon (fun z : α × β => ∑ c, p (z.1,(z.2,c))) +
      finiteShannon (fun z : α × γ => ∑ b, p (z.1,(b,z.2))) := by
  have H := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    finiteShannon_joint_mass_le (fun z : β × γ => p (a,z)) (fun z => hp (a,z)))
  simpa only [finiteShannon, Fintype.sum_prod_type, Finset.sum_add_distrib] using H

lemma finiteShannon_fst_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon (fun a => ∑ b, p (a,b)) ≤ finiteShannon p := by
  simpa only [finiteShannon, Fintype.sum_prod_type] using
    Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      negMulLog_sum_le (fun b => p (a,b)) (fun b => hp (a,b)))

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalObservations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem observationEntropy_submodular [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (Q : Y → α) (P : Y → β) (R : Y → γ)
    (hQ : ∀ a, MeasurableSet {y | Q y = a})
    (hP : ∀ b, MeasurableSet {y | P y = b})
    (hR : ∀ c, MeasurableSet {y | R y = c}) :
    observationEntropy μ (fun y => (Q y,(P y,R y))) + observationEntropy μ Q ≤
      observationEntropy μ (fun y => (Q y,P y)) +
      observationEntropy μ (fun y => (Q y,R y)) := by
  let p : α × (β × γ) → ℝ := fun z => μ.real {y | (Q y,(P y,R y)) = z}
  have hrow a : ∑ z : β × γ, p (a,z) = μ.real {y | Q y = a} :=
    observation_joint_row μ Q (fun y => (P y,R y)) hQ
      (observationPair_measurable_fiber P R hP hR) a
  have hleft (z : α × β) : ∑ c, p (z.1,(z.2,c)) = μ.real {y | (Q y,P y) = z} := by
    rcases z with ⟨a,b⟩
    convert observation_joint_row μ (fun y => (Q y,P y)) R
      (observationPair_measurable_fiber Q P hQ hP) hR (a,b) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro c _
    apply congrArg μ.real
    ext y
    simp only [Prod.mk.injEq, Set.mem_ofPred_eq]
    tauto
  have hright (z : α × γ) : ∑ b, p (z.1,(b,z.2)) = μ.real {y | (Q y,R y) = z} := by
    rcases z with ⟨a,c⟩
    convert observation_joint_row μ (fun y => (Q y,R y)) P
      (observationPair_measurable_fiber Q R hQ hR) hP (a,c) using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro b _
    apply congrArg μ.real
    ext y
    simp only [Prod.mk.injEq, Set.mem_ofPred_eq]
    tauto
  have H := finiteShannon_submodular p (fun _ => measureReal_nonneg)
  simpa only [hrow, hleft, hright, observationEntropy] using H

theorem conditionalObservationEntropy_conditioning_le
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β) (R : Y → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b})
    (hR : ∀ c, MeasurableSet {y | R y = c}) :
    conditionalObservationEntropy μ P (fun y => (Q y,R y)) ≤
      conditionalObservationEntropy μ P Q := by
  have H := observationEntropy_submodular μ Q R P hQ hR hP
  unfold conditionalObservationEntropy
  rw [observationEntropy_assoc]
  linarith

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationRefinement
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

lemma observationEntropy_injective [Fintype α] [Fintype β]
    (μ : Measure Y) (P : Y → α) (f : α → β) (hf : Function.Injective f) :
    observationEntropy μ (fun y => f (P y)) = observationEntropy μ P := by
  classical
  unfold observationEntropy finiteShannon
  symm
  apply Fintype.sum_of_injective f hf
  · intro b hb
    have hset : {y | f (P y) = b} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hb ⟨P y,h⟩
    simp [hset]
  · intro a
    simp only [hf.eq_iff]

lemma conditionalObservationEntropy_injective
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (μ : Measure Y) (P : Y → α) (Q : Y → β)
    (f : α → γ) (g : β → δ) (hf : Function.Injective f) (hg : Function.Injective g) :
    conditionalObservationEntropy μ (fun y => f (P y)) (fun y => g (Q y)) =
      conditionalObservationEntropy μ P Q := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_injective μ Q g hg]
  have hi : Function.Injective (fun z : β × α => (g z.1,f z.2)) := by
    intro x y h
    exact Prod.ext (hg (congrArg Prod.fst h)) (hf (congrArg Prod.snd h))
  rw [observationEntropy_injective μ (fun y => (Q y,P y)) _ hi]

theorem conditionalObservationEntropy_coarsening_le
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (Q : Y → β) (f : β → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    conditionalObservationEntropy μ P Q ≤
      conditionalObservationEntropy μ P (fun y => f (Q y)) := by
  have hfQ c : MeasurableSet {y | f (Q y) = c} := by
    have heq : {y | f (Q y) = c} = ⋃ b : {b // f b = c}, {y | Q y = b.val} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun h => ⟨⟨Q y,h⟩,rfl⟩, fun ⟨b,h⟩ => h ▸ b.property⟩
    rw [heq]
    exact MeasurableSet.iUnion (fun b => hQ b.val)
  have H := conditionalObservationEntropy_conditioning_le μ P (fun y => f (Q y)) Q
    hP hfQ hQ
  have hi : Function.Injective (fun b : β => (f b,b)) := by
    intro a b h
    exact congrArg Prod.snd h
  have heq := conditionalObservationEntropy_injective μ P Q id (fun b => (f b,b))
    Function.injective_id hi
  change conditionalObservationEntropy μ P (fun y => (f (Q y),Q y)) =
    conditionalObservationEntropy μ P Q at heq
  rw [heq] at H
  exact H

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalOrbitEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

omit [MeasurableSpace Y] in
lemma orbitName_one (T : Y → Y) (P : Y → α) :
    orbitName T P 1 = fun y (_ : Fin 1) => P y := by
  funext y j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_FutureEntropyIncrements
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional entropy increments of stationary finite observations -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace PrimeDegreePackets

variable {Y α : Type*} [MeasurableSpace Y] [Fintype α]

omit [Fintype α] in
lemma futureName_measurable_fiber {T : Y → Y} (hT : Measurable T) {P : Y → α}
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) (a : Fin N → α) :
    MeasurableSet {y | futureName T P N y = a} :=
  (orbitName_measurable_fiber hT hP N a).preimage hT

lemma orbitEntropy_succ_head (μ : Measure Y) (T : Y → Y) (P : Y → α) (N : ℕ) :
    observationEntropy μ (orbitName T P (N+1)) =
      observationEntropy μ (fun y => (P y,futureName T P N y)) := by
  rw [Nat.add_comm N 1, orbitName_add T P 1 N, observationEntropy_equiv, orbitName_one]
  have hi : Function.Injective
      (fun z : α × (Fin N → α) => ((fun _ : Fin 1 => z.1),z.2)) := by
    intro x y h
    have hfst : (fun _ : Fin 1 => x.1) = (fun _ : Fin 1 => y.1) :=
      congrArg (fun z : (Fin 1 → α) × (Fin N → α) => z.1) h
    have hsnd : x.2 = y.2 := congrArg (fun z : (Fin 1 → α) × (Fin N → α) => z.2) h
    exact Prod.ext (congrFun hfst 0) hsnd
  exact observationEntropy_injective μ (fun y => (P y,futureName T P N y)) _ hi

lemma futureConditionalEntropy_eq_sub
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    conditionalObservationEntropy μ P (futureName T P N) =
      observationEntropy μ (orbitName T P (N+1)) -
      observationEntropy μ (orbitName T P N) := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_swap μ (futureName T P N) P, ← orbitEntropy_succ_head]
  rw [show futureName T P N = fun y => orbitName T P N (T y) from rfl,
    observationEntropy_comp_preserving μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) hT]

lemma futureConditionalEntropy_antitone
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : Measurable T) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Antitone (fun N => conditionalObservationEntropy μ P (futureName T P N)) := by
  apply antitone_nat_of_succ_le
  intro N
  exact conditionalObservationEntropy_coarsening_le μ P (futureName T P (N+1))
    (fun v (i : Fin N) => v i.castSucc) hP (futureName_measurable_fiber hT hP (N+1))

lemma sum_futureConditionalEntropy
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    (∑ n ∈ Finset.range N, conditionalObservationEntropy μ P (futureName T P n)) =
      observationEntropy μ (orbitName T P N) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, observationEntropy_unique]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, futureConditionalEntropy_eq_sub μ hT P hP]
      ring

theorem futureConditionalEntropy_tendsto_rate
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    Tendsto (fun N => conditionalObservationEntropy μ P (futureName T P N)) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  let a := fun N => conditionalObservationEntropy μ P (futureName T P N)
  have hanti : Antitone a := futureConditionalEntropy_antitone μ hT.measurable P hP
  have hbdd : BddBelow (Set.range a) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨N,rfl⟩
    exact conditionalObservationEntropy_nonneg μ P _ hP
      (futureName_measurable_fiber hT.measurable hP N)
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hc := hlim.cesaro
  have hc' : Tendsto (fun N => observationEntropy μ (orbitName T P N) / (N : ℝ))
      atTop (𝓝 (⨅ n, a n)) := by
    simpa only [a, sum_futureConditionalEntropy μ hT P hP, div_eq_inv_mul] using hc
  have heq := tendsto_nhds_unique hc' (tendsto_observationEntropyRate μ hT P hP)
  rwa [heq] at hlim

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_DiagonalEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entropy symmetry for the actual diagonal action

The time-reversal theorem applies to right translations by diagonal
matrices. The final lemma combines it with the precise positive-root
entropy formula of EKL (2006), Proposition 3.1(3). That formula remains
an explicit hypothesis here; time reversal and the coefficient balance
are proved.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonalOneParameter_neg_weights {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter (fun i => -ell i)
      (by simp only [Finset.sum_neg_distrib, hell, neg_zero]) t =
      diagonalOneParameter ell hell (-t) := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => Real.exp (-ell i * t)) =
    Matrix.diagonal (fun i => Real.exp (ell i * -t))
  congr 1
  funext i
  congr 1
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_AdaptiveFutureLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable future observations with locally controlled lifts

The observation cells adapt to the local injectivity radius both before
and after one diagonal step. Two valid injectivity balls are nested, so
successive relative lifts agree even when their radii differ. No compact
orbit assumption or finite-entropy hypothesis is required for the
resulting countable observation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma variable_future_lifts_conjugate {n : ℕ} (a : G n) (x y : X n)
    (L : ℝ) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hexpand : ∀ s, 0 < s →
      (MulAut.conj a⁻¹) '' matrixBall n s ⊆ matrixBall n (L*s))
    (hinj : ∀ k : ℕ, Set.InjOn
      (fun g => rightAction ((fun z => rightAction z a)^[k] x) g)
        (matrixBall n (r k)))
    (hnext : ∀ k : ℕ, Set.InjOn
      (fun g => rightAction ((fun z => rightAction z a)^[k+1] x) g)
        (matrixBall n (L*r k)))
    (g : ℕ → G n) (hg : ∀ k, g k ∈ matrixBall n (r k))
    (hlift : ∀ k, rightAction ((fun z => rightAction z a)^[k] x) (g k) =
      (fun z => rightAction z a)^[k] y) :
    ∀ k, g k = (MulAut.conj a⁻¹)^[k] (g 0) := by
  have hstep (k : ℕ) : g (k+1) = MulAut.conj a⁻¹ (g k) := by
    have he : rightAction ((fun z => rightAction z a)^[k+1] x) (g (k+1)) =
        rightAction ((fun z => rightAction z a)^[k+1] x) (MulAut.conj a⁻¹ (g k)) := by
      rw [hlift (k+1),Function.iterate_succ_apply',←hlift k,rightAction_conjugation,
        Function.iterate_succ_apply']
    have hc := hexpand (r k) (hr k) ⟨g k,hg k,rfl⟩
    rcases le_total (r (k+1)) (L*r k) with h | h
    · exact hnext k (matrixBall_mono h (hg (k+1))) hc he
    · exact hinj (k+1) (hg (k+1)) (matrixBall_mono h hc) he
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [hstep,Function.iterate_succ_apply',ih]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LocalInjectivityHeight
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable chart height with bounded diagonal increments

Local quotient injectivity is encoded on a geometric sequence of radii.
The least admissible index is measurable and changes by at most one under
a fixed diagonal translation. This supplies chart-size control without
an integrability assumption on the height itself.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma LocalInjectivityAt.mono {n : ℕ} {r s : ℝ} {x : X n}
    (h : LocalInjectivityAt r x) (hs : s ≤ r) : LocalInjectivityAt s x := by
  obtain ⟨U,hU,hx,hi⟩ := h
  exact ⟨U,hU,hx,fun y hy => (hi y hy).mono (matrixBall_mono hs)⟩

lemma localInjectivityAt_translate {n : ℕ} (a : G n) {κ r : ℝ}
    (hexpand : (MulAut.conj a) '' matrixBall n (r/κ) ⊆ matrixBall n r)
    {x : X n} (hx : LocalInjectivityAt r x) :
    LocalInjectivityAt (r/κ) (rightAction x a) := by
  obtain ⟨U,hU,hx,hi⟩ := hx
  refine ⟨(rightActionHomeomorph a) '' U,
    (rightActionHomeomorph a).isOpenMap U hU,⟨x,hx,rfl⟩,?_⟩
  rintro _ ⟨z,hz,rfl⟩ u hu v hv heq
  apply (MulAut.conj a).injective
  apply hi z hz (hexpand ⟨u,hu,rfl⟩) (hexpand ⟨v,hv,rfl⟩)
  have H := congrArg (fun w => rightAction w a⁻¹) heq
  change rightAction (rightAction (rightAction z a) u) a⁻¹ =
    rightAction (rightAction (rightAction z a) v) a⁻¹ at H
  simpa only [rightAction_mul,MulAut.conj_apply,mul_assoc] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogProper
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact logarithmic balls and a tempered exhaustion

Logarithmic matrix-length sublevels are compact. Their quotient images
control closed logarithmic-distance balls. A rescaled distance from one
fixed point then gives a proper measurable natural height with sublinear
growth under a measure-preserving right translation.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

theorem isCompact_matrixLogLength_sublevel {n : ℕ} (R : ℝ) :
    IsCompact {g : G n | matrixLogLength g ≤ R} := by
  have hK := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
    (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℝ) (Real.exp R-1))
  apply hK.of_isClosed_subset (isClosed_le (continuous_matrixLogLength n) continuous_const)
  intro g hg
  change dist g.val 1 ≤ Real.exp R-1
  rw [dist_eq_norm]
  exact (norm_sub_one_le_exp_matrixLogLength g).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hg) 1)

theorem isCompact_quotientLogDistance_sublevel {n : ℕ} (x : X n) (R : ℝ) :
    IsCompact {y : X n | quotientLogDistance x y ≤ R} := by
  have hK := (isCompact_matrixLogLength_sublevel (n := n) (R+1)).image
    (continuous_rightOrbit n x)
  apply hK.of_isClosed_subset (isClosed_le (continuous_quotientLogDistance n x) continuous_const)
  intro y hy
  obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt x y (by norm_num : (0:ℝ)<1)
  exact ⟨g,hlen.le.trans (by linarith [show quotientLogDistance x y ≤ R from hy]),hg⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ConjugationRadius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative conjugation of local matrix balls

The logarithmic displacement length gives an explicit exponential loss
when a local quotient chart is transported by a group element.
-/

noncomputable section
open Set Matrix
open scoped Matrix.Norms.Operator Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrix_entry_abs_le_operator_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  have H : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k => ∑ l, ‖A k l‖₊) (Finset.mem_univ i))
  change ‖A i j‖ ≤ ‖A‖
  exact_mod_cast H

lemma matrix_operator_norm_le_card_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hA : ∀ i j, |A i j| ≤ r) : ‖A‖ ≤ (n:ℝ)*r := by
  change ‖fun i => WithLp.toLp 1 (A i)‖ ≤ (n:ℝ)*r
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hr)]
  intro i
  rw [PiLp.norm_eq_of_L1]
  change (∑ j, ‖A i j‖) ≤ (n:ℝ)*r
  calc
    _ ≤ ∑ _j : Fin n, r := Finset.sum_le_sum (fun j _ => by simpa only [Real.norm_eq_abs] using hA i j)
    _ = _ := by simp

lemma specialLinear_norm_le_exp_length {n : ℕ} (hn : 0 < n) (g : G n) :
    ‖g.val‖ ≤ Real.exp (matrixLogLength g) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have h := norm_add_le (g.val-1) (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [sub_add_cancel,norm_one] at h
  have H := norm_sub_one_le_exp_matrixLogLength g
  linarith

lemma conjugation_matrixBall_exp_bound {n : ℕ} (hn : 0 < n)
    (g : G n) {r : ℝ} (hr : 0 < r) :
    (MulAut.conj g) '' matrixBall n (r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))) ⊆
      matrixBall n r := by
  rintro _ ⟨u,hu,rfl⟩ i j
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 ≤ r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g)) := by positivity
  have hU := matrix_operator_norm_le_card_mul (u.val-1) hs
    (fun i j => (hu i j).le)
  have hg := specialLinear_norm_le_exp_length hn g
  have hgi := specialLinear_norm_le_exp_length hn g⁻¹
  rw [matrixLogLength_inv] at hgi
  have hgg : g.val*(g⁻¹).val=(1 : Matrix (Fin n) (Fin n) ℝ) := by
    change (g*g⁻¹).val=1
    simp
  have he : (MulAut.conj g u).val-1=g.val*(u.val-1)*(g⁻¹).val := by
    change g.val*u.val*(g⁻¹).val-1= _
    rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hgg]
  have hb : ‖(MulAut.conj g u).val-1‖ ≤
      Real.exp (matrixLogLength g)*((n:ℝ)*(r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))))*
        Real.exp (matrixLogLength g) := by
    rw [he]
    calc
      _ ≤ (‖g.val‖*‖u.val-1‖)*‖(g⁻¹).val‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ _ := mul_le_mul (mul_le_mul hg hU (norm_nonneg _) (Real.exp_pos _).le)
        hgi (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg n) hs))
  have hc : Real.exp (matrixLogLength g)*
      ((n:ℝ)*(r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))))*
      Real.exp (matrixLogLength g)=r/2 := by
    have he : Real.exp (2*matrixLogLength g)=Real.exp (matrixLogLength g)*Real.exp (matrixLogLength g) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he]
    field_simp [hnp.ne',Real.exp_ne_zero]
  rw [hc] at hb
  have hentry := matrix_entry_abs_le_operator_norm ((MulAut.conj g u).val-1) i j
  change |(MulAut.conj g u).val i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| < r
  exact hentry.trans hb |>.trans_lt (by linarith)

lemma localInjectivityAt_exp_translate {n : ℕ} (hn : 0 < n)
    (g : G n) {r : ℝ} (hr : 0 < r) {x : X n} (hx : LocalInjectivityAt r x) :
    LocalInjectivityAt (r/(2*(n:ℝ)*Real.exp (2*matrixLogLength g))) (rightAction x g) :=
  localInjectivityAt_translate g (conjugation_matrixBall_exp_bound hn g hr) hx

/-- Explicit exponential chart radii on every logarithmic-distance ball. -/
theorem exists_uniform_logarithmic_injectivity_radius {n : ℕ} (hn : 0 < n) :
    ∃ r > 0, ∀ (R : ℝ) (x : X n),
      quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
      LocalInjectivityAt (r/(2*(n:ℝ)*Real.exp (2*(R+1)))) x := by
  let x₀ : X n := Quotient.mk _ (1 : G n)
  obtain ⟨U,hU,hx,r,hr,hinj⟩ := local_uniform_chart_injective x₀
  have hbase : LocalInjectivityAt r x₀ := ⟨U,hU,hx,hinj⟩
  refine ⟨r,hr,?_⟩
  intro R x hxR
  obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt x₀ x (by norm_num : (0:ℝ)<1)
  have hbound : matrixLogLength g ≤ R+1 := by
    dsimp [x₀] at hlen
    linarith
  have hden : 2*(n:ℝ)*Real.exp (2*matrixLogLength g) ≤
      2*(n:ℝ)*Real.exp (2*(R+1)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have ht := localInjectivityAt_exp_translate hn g hr hbase
  rw [hg] at ht
  apply ht.mono
  exact div_le_div_of_nonneg_left hr.le (by positivity) hden

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DyadicBoundaryCuts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance cuts with uniform quantitative boundary bounds

One cut controls all dyadic widths. The constant depends only on the
length of the interval from which the cut is selected, not the observable
or the probability measure.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

lemma lintegral_dyadicBoundaryCost (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) :
    (∫⁻ r, dyadicBoundaryCost μ f r) = 4 := by
  unfold dyadicBoundaryCost
  have hm (k : ℕ) : Measurable (fun r =>
      ENNReal.ofReal ((2:ℝ)^k) * μ (realBoundaryStrip f r ((1/4:ℝ)^k))) :=
    measurable_const.mul (measurable_realBoundaryStrip_mass μ hf _)
  rw [lintegral_tsum (fun k => (hm k).aemeasurable)]
  simp_rw [lintegral_const_mul _ (measurable_realBoundaryStrip_mass μ hf _),
    lintegral_realBoundaryStrip_mass μ hf]
  have he (k : ℕ) : ENNReal.ofReal ((2:ℝ)^k) * ENNReal.ofReal (2*(1/4:ℝ)^k) =
      ENNReal.ofReal (2*(1/2:ℝ)^k) := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = 2*((2:ℝ)^k*(1/4:ℝ)^k) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  simp_rw [he]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (summable_geometric_two.mul_left 2),tsum_mul_left,tsum_geometric_two]
  norm_num

theorem exists_dyadic_boundary_cut (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, μ {x | f x=r}=0 ∧
      ∀ k : ℕ, μ (realBoundaryStrip f r ((1/4:ℝ)^k)) ≤
        ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
  obtain ⟨r,hr,hcost⟩ := exists_cut_cost_le (dyadicBoundaryCost μ f)
    (by norm_num : (0:ℝ)<4) hab (by rw [lintegral_dyadicBoundaryCost μ hf]; norm_num)
  have hbound (k : ℕ) : μ (realBoundaryStrip f r ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
    have hterm := (ENNReal.le_tsum k (f := fun j : ℕ =>
      ENNReal.ofReal ((2:ℝ)^j)*μ (realBoundaryStrip f r ((1/4:ℝ)^j)))).trans hcost
    have hp : 0 ≤ (1/2:ℝ)^k := by positivity
    have H := mul_le_mul' (le_rfl : ENNReal.ofReal ((1/2:ℝ)^k) ≤
      ENNReal.ofReal ((1/2:ℝ)^k)) hterm
    have he : ENNReal.ofReal ((1/2:ℝ)^k)*(ENNReal.ofReal ((2:ℝ)^k)*
        μ (realBoundaryStrip f r ((1/4:ℝ)^k))) =
        μ (realBoundaryStrip f r ((1/4:ℝ)^k)) := by
      rw [←mul_assoc,←ENNReal.ofReal_mul hp,←mul_pow]
      norm_num
    have heR : ENNReal.ofReal ((1/2:ℝ)^k)*ENNReal.ofReal (2*4/(b-a)) =
        ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
      rw [←ENNReal.ofReal_mul hp]
      congr 1
      ring
    rwa [he,heR] at H
  refine ⟨r,hr,?_,hbound⟩
  apply fiber_null_of_summable_realBoundaryStrip_mass μ
    (fun k : ℕ => (1/4:ℝ)^k) (fun _ => by positivity) r
  have hsum := ENNReal.tsum_le_tsum hbound
  have he : (∑' k : ℕ, ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k)) < ∞ :=
    (summable_geometric_two.mul_left (8/(b-a))).tsum_ofReal_lt_top
  exact (lt_of_le_of_lt hsum he).ne

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ControlledRadialHeight
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proper radial heights with controlled boundary strips

Well-separated radial thresholds can be chosen with one common strip
bound. The corresponding integer height is proper and has unit jumps
under the prescribed right translation.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_controlled_radial_height {n : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ] (a : G n) :
    ∃ (B : ℝ) (t : ℕ → ℝ) (H : X n → ℕ),
      0 < B ∧ matrixLogLength a < B ∧ Measurable H ∧
      (∀ m : ℕ, B*(2*(m:ℝ)+1/2) < t m ∧ t m < B*(2*(m:ℝ)+1)) ∧
      (∀ m, {x | H x ≤ m} =
        {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t m}) ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1) ∧
      ∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x=t m}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip
          (quotientLogDistance (Quotient.mk _ (1 : G n))) (t m) ((1/4:ℝ)^k)) ≤
            ENNReal.ofReal (16/B*(1/2:ℝ)^k) := by
  classical
  let B := 1+matrixLogLength a
  have hB : 0 < B := by dsimp [B] <;> linarith [matrixLogLength_nonneg a]
  have hBa : matrixLogLength a < B := by dsimp [B] <;> linarith
  let D : X n → ℝ := quotientLogDistance (Quotient.mk _ (1 : G n))
  have hD : Continuous D := continuous_quotientLogDistance n _
  have hex (m : ℕ) := exists_dyadic_boundary_cut μ hD.measurable
    (show B*(2*(m:ℝ)+1/2) < B*(2*(m:ℝ)+1) by nlinarith)
  choose t ht hnull hboundary using hex
  have hgap (m : ℕ) : t m+B ≤ t (m+1) := by
    have h₁ := (ht m).2
    have h₂ := (ht (m+1)).1
    push_cast at h₂
    nlinarith
  have hmono : Monotone t := monotone_nat_of_le_succ fun m => by
    have := hgap m
    linarith
  have hfinite (x : X n) : ∃ m : ℕ, D x ≤ t m := by
    obtain ⟨m,hm⟩ := exists_nat_gt (D x/B)
    have hx : D x < (m:ℝ)*B := (div_lt_iff₀ hB).mp hm
    refine ⟨m,?_⟩
    have ht₀ := (ht m).1
    have hm₀ : 0 ≤ B*(m:ℝ) := mul_nonneg hB.le (Nat.cast_nonneg _)
    linarith
  let H : X n → ℕ := fun x => Nat.find (hfinite x)
  have hle (x : X n) (m : ℕ) : H x ≤ m ↔ D x ≤ t m := by
    constructor
    · intro h
      exact (Nat.find_spec (hfinite x)).trans (hmono h)
    · exact Nat.find_min' (hfinite x)
  have hsets (m : ℕ) : {x | H x ≤ m} = {x | D x ≤ t m} := Set.ext fun x => hle x m
  have hHm : Measurable H := by
    apply measurable_of_Iic
    intro m
    change MeasurableSet {x | H x ≤ m}
    rw [hsets]
    exact measurableSet_le hD.measurable measurable_const
  refine ⟨B,t,H,hB,hBa,hHm,ht,hsets,?_,?_,?_⟩
  · intro m
    rw [hsets]
    exact isCompact_quotientLogDistance_sublevel _ _
  · intro x
    obtain ⟨hlo,hhi⟩ := abs_le.mp (quotientLogDistance_right_bound
      (Quotient.mk _ (1 : G n)) x a)
    have hx := (hle x (H x)).mp le_rfl
    have hax := (hle (rightAction x a) (H (rightAction x a))).mp le_rfl
    constructor
    · apply (hle _ _).mpr
      have hg := hgap (H x)
      change D (rightAction x a)-D x ≤ matrixLogLength a at hhi
      linarith
    · apply (hle _ _).mpr
      have hg := hgap (H (rightAction x a))
      change -matrixLogLength a ≤ D (rightAction x a)-D x at hlo
      linarith
  · intro m
    refine ⟨hnull m,?_⟩
    intro k
    convert hboundary m k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    field_simp [hB.ne']
    ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RadialFutureLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentially shrinking radial cells give triangular future lifts -/

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma LocalInjectivityAt.injOn {n : ℕ} {r : ℝ} {x : X n}
    (h : LocalInjectivityAt r x) :
    Set.InjOn (fun g => rightAction x g) (matrixBall n r) := by
  obtain ⟨U,_,hx,hi⟩ := h
  exact hi x hx

/-- The chosen lift remains in the height-dependent small matrix ball at
every future time; the same radius is an injectivity radius at each point. -/
theorem exists_radial_radius_small_conjugate_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) (R : ℝ) (hR : 0 < R) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ r₀ ≤ R ∧
      (∀ x, Set.InjOn (fun g => rightAction x g)
        (matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))))) ∧
      ∀ (Q : X n → ℕ),
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g=y ∧ (∀ i j, ell j < ell i → g.val i j=0) ∧
          ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ) * g *
            diagonalOneParameter ell hell (-(k:ℝ)) ∈
            matrixBall n (r₀*Real.exp (-(4*B)*
              (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ))) := by
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun x => rightAction x a
  have hneg : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨L,hL,hexpand⟩ := diagonal_conjugation_expansion (fun i => -ell i) hneg
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hparam : diagonalOneParameter (fun i => -ell i) hneg (-1) = a⁻¹ := by
    calc
      _ = diagonalOneParameter ell hell 1 := by
        simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
      _ = _ := by dsimp [a]; rw [diagonalOneParameter_neg,inv_inv]
  have hex (s : ℝ) (hs : 0 < s) :
      (MulAut.conj a⁻¹) '' matrixBall n s ⊆ matrixBall n (L*s) :=
    hparam ▸ hexpand s hs
  obtain ⟨b,hb,hinj⟩ := exists_uniform_logarithmic_injectivity_radius hn
  let c := b/(2*(n:ℝ)*Real.exp (2*(B+matrixLogLength a+1)))
  have hc : 0 < c := by dsimp [c] <;> positivity
  let r₀ := min R (min 1 (c/L))
  have hr₀ : 0 < r₀ := lt_min hR (lt_min zero_lt_one (div_pos hc hLp))
  have hLr₀ : L*r₀ ≤ c := by
    have hh := (le_div_iff₀ hLp).mp ((min_le_right R (min 1 (c/L))).trans (min_le_right 1 (c/L)))
    simpa only [mul_comm] using hh
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  have hr (m : ℕ) : 0 < r m := mul_pos hr₀ (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    have he : Real.exp (-(4*B)*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg m)])
    exact (mul_le_of_le_one_right hr₀.le he).trans ((min_le_right R (min 1 (c/L))).trans (min_le_left 1 (c/L)))
  have hrad (m : ℕ) : L*r m ≤
      b/(2*(n:ℝ)*Real.exp (2*(2*B*(m:ℝ)+B+matrixLogLength a+1))) := by
    have he : Real.exp (2*(2*B*(m:ℝ)+B+matrixLogLength a+1)) =
        Real.exp (2*(B+matrixLogLength a+1))*Real.exp ((4*B)*(m:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have heq : c*Real.exp (-(4*B)*(m:ℝ)) =
        b/(2*(n:ℝ)*Real.exp (2*(2*B*(m:ℝ)+B+matrixLogLength a+1))) := by
      rw [he,neg_mul,Real.exp_neg]
      dsimp [c]
      field_simp
    rw [←heq]
    dsimp [r]
    nlinarith [Real.exp_pos (-(4*B)*(m:ℝ))]
  have hi (x : X n) : LocalInjectivityAt (L*r (H x)) x := by
    apply (hinj (2*B*(H x:ℝ)+B+matrixLogLength a) x ?_).mono (hrad (H x))
    exact (hheight x).trans (by linarith [matrixLogLength_nonneg a])
  have hnext (x : X n) : LocalInjectivityAt (L*r (H x)) (T x) := by
    apply (hinj (2*B*(H x:ℝ)+B+matrixLogLength a) (T x) ?_).mono (hrad (H x))
    have hh := (abs_le.mp (quotientLogDistance_right_bound
      (Quotient.mk _ (1 : G n)) x a)).2
    change quotientLogDistance (Quotient.mk _ (1 : G n)) (T x)-
      quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ matrixLogLength a at hh
    linarith [hheight x]
  have hirad (x : X n) : Set.InjOn (fun g => rightAction x g)
      (matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ)))) :=
    (hi x).injOn.mono (matrixBall_mono (le_mul_of_one_le_left (hr _).le hL))
  refine ⟨r₀,hr₀,(min_le_right _ _).trans (min_le_left _ _),min_le_left _ _,hirad,?_⟩
  intro Q hsmall x y hxy
  let s := fun k : ℕ => r (H (T^[k] x))
  choose g hg hlift using fun k => hsmall (T^[k] x) (T^[k] y) (hxy k)
  have hconj := variable_future_lifts_conjugate a x y L s (fun k => hr _) hex
    (fun k => ?_) (fun k => ?_) g hg hlift
  · have he (k : ℕ) : diagonalOneParameter ell hell (k:ℝ) * g 0 *
        diagonalOneParameter ell hell (-(k:ℝ)) = g k := by
      have hp : a^k = diagonalOneParameter ell hell (-(k:ℝ)) := by
        dsimp [a]
        rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
      calc
        _ = (MulAut.conj a⁻¹)^[k] (g 0) := by
          rw [conjugation_iterate,hp,←diagonalOneParameter_neg,neg_neg]
        _ = g k := (hconj k).symm
    refine ⟨g 0,?_,by simpa only [Function.iterate_zero,Function.id_def] using hlift 0,?_,?_⟩
    · simpa only [s, r, Function.iterate_zero, Function.id_def] using hg 0
    · intro i j hij
      apply conjugation_expanding_entry_eq_zero ell hell (g 0)
        tendsto_natCast_atTop_atTop 2 _ hij
      apply Eventually.of_forall
      intro k p q
      rw [he k]
      have hh := hg k p q
      change |(g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q| < s k at hh
      have hone : |(1 : Matrix (Fin n) (Fin n) ℝ) p q| ≤ 1 := by
        simp only [Matrix.one_apply]
        split_ifs <;> norm_num
      have ht := abs_add_le ((g k).val p q-(1 : Matrix (Fin n) (Fin n) ℝ) p q)
        ((1 : Matrix (Fin n) (Fin n) ℝ) p q)
      rw [sub_add_cancel] at ht
      have hs : s k ≤ 1 := hr1 _
      linarith
    · intro k
      rw [he k]
      exact hg k
  · exact (hi (T^[k] x)).injOn.mono (matrixBall_mono
      (le_mul_of_one_le_left (hr _).le hL))
  · simpa only [Function.iterate_succ_apply'] using (hnext (T^[k] x)).injOn

/-- Future fibers admit small triangular lifts. -/
theorem exists_radial_radius_small_triangular_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) (R : ℝ) (hR : 0 < R) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ r₀ ≤ R ∧
      ∀ (Q : X n → ℕ),
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall n (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g=y ∧ ∀ i j, ell j < ell i → g.val i j=0 := by
  obtain ⟨r,hr,hr1,hrR,_,h⟩ := exists_radial_radius_small_conjugate_lifts
    hn ell hell B hB H hheight R hR
  refine ⟨r,hr,hr1,hrR,?_⟩
  intro Q hQ x y hxy
  obtain ⟨g,hg,hgx,hgt,_⟩ := h Q hQ x y hxy
  exact ⟨g,hg,hgx,hgt⟩


end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_HeightObservationEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy controlled by the increments of a height

A finite label reconstructed from its next value and a finite increment
code has entropy rate bounded by the entropy of that code. In particular,
all finite truncations of a height changing by at most one have entropy
rate at most `log 3`, regardless of the height's integrability.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [MeasurableSpace Y]

section Recoding
variable {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]

lemma observationEntropy_recode_le (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (hP : Measurable P) (f : α → β) :
    observationEntropy μ (f ∘ P) ≤ observationEntropy μ P := by
  have hfP : Measurable (f ∘ P) := (measurable_of_finite f).comp hP
  have H := conditionalObservationEntropy_nonneg μ P (f ∘ P)
    (fun a => hP (measurableSet_singleton a))
    (fun b => hfP (measurableSet_singleton b))
  have he := observationEntropy_injective μ P (fun a => (f a,a))
    (fun _ _ h => congrArg Prod.snd h)
  change observationEntropy μ (fun y => ((f ∘ P) y,P y)) = observationEntropy μ P at he
  unfold conditionalObservationEntropy at H
  rw [he] at H
  linarith

omit [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma observationEntropyRate_le_oneStep (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (P : Y → α) (hP : Measurable P) :
    observationEntropyRate μ T P ≤ conditionalObservationEntropy μ P (P ∘ T) := by
  have hp a := hP (measurableSet_singleton a)
  have H := le_of_tendsto (futureConditionalEntropy_tendsto_rate μ hT P hp)
    ((eventually_ge_atTop 1).mono fun N hN =>
      futureConditionalEntropy_antitone μ hT.measurable P hp hN)
  have he : conditionalObservationEntropy μ P (futureName T P 1) =
      conditionalObservationEntropy μ P (P ∘ T) := by
    change conditionalObservationEntropy μ P (fun y => orbitName T P 1 (T y)) = _
    rw [orbitName_one]
    change conditionalObservationEntropy μ P (fun y (_ : Fin 1) => P (T y)) = _
    exact conditionalObservationEntropy_injective μ P (P ∘ T) id
      (fun a (_ : Fin 1) => a) Function.injective_id (fun _ _ h => congrFun h 0)
  change observationEntropyRate μ T P ≤ conditionalObservationEntropy μ P (futureName T P 1) at H
  rwa [he] at H

/-- A one-step reconstruction code bounds the entropy rate. -/
theorem observationEntropyRate_le_incrementEntropy
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : Measurable P) (D : Y → β) (hD : Measurable D)
    (decode : α → β → α) (hdecode : ∀ y, decode (P (T y)) (D y)=P y) :
    observationEntropyRate μ T P ≤ observationEntropy μ D := by
  have hnext := hP.comp hT.measurable
  have H := observationEntropy_recode_le μ (fun y => (P (T y),D y))
    (hnext.prodMk hD) (fun z => (z.1,decode z.1 z.2))
  have he : (fun y => (P (T y),decode (P (T y)) (D y))) =
      (fun y => (P (T y),P y)) := by funext y; rw [hdecode]
  change observationEntropy μ (fun y => (P (T y),decode (P (T y)) (D y))) ≤ _ at H
  rw [he] at H
  have H' := observationEntropy_joint_le μ (P ∘ T) D
    (fun a => hnext (measurableSet_singleton a))
    (fun b => hD (measurableSet_singleton b))
  change observationEntropy μ (fun y => (P (T y),D y)) ≤
    observationEntropy μ (P ∘ T) + observationEntropy μ D at H'
  have hc : conditionalObservationEntropy μ P (P ∘ T) ≤ observationEntropy μ D := by
    unfold conditionalObservationEntropy
    change observationEntropy μ (fun y => (P (T y),P y)) -
      observationEntropy μ (P ∘ T) ≤ _
    linarith
  exact (observationEntropyRate_le_oneStep μ hT P hP).trans hc

end Recoding

/-- A finite clipped height is reconstructed from its next value and a
three-valued increment; the middle code means that the label did not change. -/
theorem heightClip_increment_model {T : Y → Y} (hT : Measurable T)
    (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ y, H (T y) ≤ H y+1 ∧ H y ≤ H (T y)+1) (N : ℕ) :
    ∃ (D : Y → Fin 3) (decode : Fin (N+1) → Fin 3 → Fin (N+1)),
      Measurable D ∧
      (∀ y, decode (heightClip H N (T y)) (D y)=heightClip H N y) ∧
      (∀ y, D y=1 ↔ heightClip H N (T y)=heightClip H N y) := by
  classical
  let P := heightClip H N
  have hP : Measurable P := heightClip_measurable hH N
  let D : Y → Fin 3 := fun y =>
    if P y < P (T y) then 0 else if P (T y) < P y then 2 else 1
  have hD : Measurable D := by
    have hc : Measurable (fun z : Fin (N+1) × Fin (N+1) =>
        (if z.1 < z.2 then 0 else if z.2 < z.1 then 2 else 1 : Fin 3)) :=
      measurable_of_finite _
    exact hc.comp (hP.prodMk (hP.comp hT))
  let decode : Fin (N+1) → Fin 3 → Fin (N+1) := fun p q =>
    ⟨min N (if q=0 then p.val-1 else if q=2 then p.val+1 else p.val),
      Nat.lt_succ_of_le (min_le_left _ _)⟩
  have hdecode (y : Y) : decode (P (T y)) (D y)=P y := by
    have hs := hstep y
    by_cases hlt : P y < P (T y)
    · have he : D y=0 := by simp only [D,hlt,ite_true, if_true]
      rw [he]
      apply Fin.ext
      change min N (min (H (T y)) N-1)=min (H y) N
      change min (H y) N < min (H (T y)) N at hlt
      omega
    · by_cases hgt : P (T y) < P y
      · have he : D y=2 := by simp only [D,hlt,hgt,ite_false, if_false,ite_true, if_true]
        rw [he]
        apply Fin.ext
        change min N (min (H (T y)) N+1)=min (H y) N
        change min (H (T y)) N < min (H y) N at hgt
        omega
      · have he : D y=1 := by simp only [D,hlt,hgt,ite_false, if_false]
        rw [he]
        apply Fin.ext
        change min N (min (H (T y)) N)=min (H y) N
        change ¬min (H y) N < min (H (T y)) N at hlt
        change ¬min (H (T y)) N < min (H y) N at hgt
        omega
  refine ⟨D,decode,hD,hdecode,?_⟩
  intro y
  change D y=1 ↔ P (T y)=P y
  by_cases hlt : P y < P (T y)
  · have hn : P (T y) ≠ P y := ne_of_gt hlt
    simp [D,hlt,hn]
  · by_cases hgt : P (T y) < P y
    · have hn : P (T y) ≠ P y := ne_of_lt hgt
      simp [D,hlt,hgt,hn]
    · have he : P (T y)=P y := le_antisymm (le_of_not_gt hlt) (le_of_not_gt hgt)
      simp [D,he]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RareTernaryEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy of a rare three-valued increment

When a three-valued increment is usually the middle value, its entropy
is bounded by binary entropy plus the exceptional mass times `log 2`.
The bound tends to zero with the exceptional mass.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma negMulLog_pair_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a + Real.negMulLog b ≤
      Real.negMulLog (a+b) + (a+b)*Real.log 2 := by
  have hJ := Real.concaveOn_negMulLog.2 ha hb
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hJ
  have hm : (1/2:ℝ)*a+(1/2)*b=(a+b)/2 := by ring
  rw [hm] at hJ
  have hhalf : Real.negMulLog (1/2:ℝ)=Real.log 2/2 := by
    rw [one_div,Real.negMulLog,Real.log_inv]
    ring
  have hs : 2*Real.negMulLog ((a+b)/2)=Real.negMulLog (a+b)+(a+b)*Real.log 2 := by
    rw [div_eq_mul_inv,Real.negMulLog_mul]
    have he : (2:ℝ)⁻¹=1/2 := by norm_num
    rw [he,hhalf]
    ring
  linarith

lemma continuous_rareTernaryCost : Continuous rareTernaryCost := by
  unfold rareTernaryCost
  fun_prop

lemma finiteShannon_ternary_le {p : Fin 3 → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i=1) :
    finiteShannon p ≤ rareTernaryCost (p 0+p 2) := by
  have hpair := negMulLog_pair_le (hp 0) (hp 2)
  have hmid : p 1=1-(p 0+p 2) := by
    rw [Fin.sum_univ_three] at hs
    linarith
  unfold finiteShannon rareTernaryCost
  rw [Fin.sum_univ_three,←hmid]
  linarith

lemma observationEntropy_ternary_le
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (D : Y → Fin 3) (hD : Measurable D) :
    observationEntropy μ D ≤ rareTernaryCost (μ.real {y | D y ≠ 1}) := by
  have hd : Disjoint {y | D y=0} {y | D y=2} := by
    rw [Set.disjoint_left]
    intro y h0 h2
    have h : (0:Fin 3)=2 := h0.symm.trans h2
    norm_num at h
  have he : {y | D y≠1} = {y | D y=0} ∪ {y | D y=2} := by
    ext y
    change D y≠1 ↔ D y=0 ∨ D y=2
    generalize hz : D y=z
    fin_cases z <;> simp
  have hm : μ.real {y | D y≠1} = μ.real {y | D y=0} + μ.real {y | D y=2} := by
    rw [he,measureReal_union hd (hD (measurableSet_singleton 2))]
  rw [hm]
  exact finiteShannon_ternary_le (fun _ => measureReal_nonneg)
    (observation_distribution_sum μ D (fun i => hD (measurableSet_singleton i)))

lemma rareTernaryCost_small {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p : ℝ, 0 ≤ p → p < δ → rareTernaryCost p < ε := by
  have hlim : Tendsto rareTernaryCost (𝓝 0) (𝓝 0) := by
    simpa only [rareTernaryCost_zero] using continuous_rareTernaryCost.tendsto (0:ℝ)
  have hnear := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ,hδ,?_⟩
  intro p hp hpδ
  apply hball
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hp] using hpδ

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HeightBoundaryCount
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the boundaries of shifted height bins

A natural height crosses exactly one of the `q` shifted bin boundaries
when incremented by one. Integrating this identity controls boundary
frequencies without requiring the height itself to be integrable.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree

lemma sum_shifted_height_boundaries (a q : ℕ) (hq : 0 < q) :
    (∑ r ∈ Finset.range q,
      if (a+r+1)/q ≠ (a+r)/q then (1:ℝ) else 0) = 1 := by
  have he (r : ℕ) :
      (if (a+r+1)/q ≠ (a+r)/q then (1:ℝ) else 0) =
        (((a+r+1)/q : ℕ):ℝ) - (((a+r)/q : ℕ):ℝ) := by
    have hlo : (a+r)/q ≤ (a+r+1)/q :=
      Nat.div_le_div_right (show a+r ≤ a+r+1 by omega)
    have hhi : (a+r+1)/q ≤ (a+r)/q+1 := by
      calc
        _ ≤ (a+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
    by_cases h : (a+r+1)/q = (a+r)/q
    · simp only [h,ne_eq,not_true_eq_false,ite_false, if_false,sub_self]
    · have hh : (a+r+1)/q = (a+r)/q+1 := by omega
      rw [ite_eq_left h,hh,Nat.cast_add,Nat.cast_one]
      ring
  simp_rw [he, Nat.add_assoc]
  rw [Finset.sum_range_sub (fun r => (((a+r)/q:ℕ):ℝ))]
  rw [Nat.add_zero,Nat.add_div_right a hq,Nat.cast_add,Nat.cast_one]
  ring

variable {Y : Type*} [MeasurableSpace Y]

lemma measurableSet_heightBoundary {H : Y → ℕ} (hH : Measurable H) (q r : ℕ) :
    MeasurableSet (heightBoundary H q r) :=
  (measurable_of_countable (fun a : ℕ => decide ((a+r+1)/q ≠ (a+r)/q))).comp hH |>
    fun h => by
      have he : heightBoundary H q r =
          (fun x => decide ((H x+r+1)/q ≠ (H x+r)/q)) ⁻¹' {true} := by
        ext x
        simp [heightBoundary]
      rw [he]
      exact h (measurableSet_singleton true)

theorem sum_heightBoundary_measures
    (μ : Measure Y) [IsProbabilityMeasure μ] (H : Y → ℕ) (hH : Measurable H)
    (q : ℕ) (hq : 0 < q) :
    (∑ r ∈ Finset.range q, μ.real (heightBoundary H q r)) = 1 := by
  have hm r := measurableSet_heightBoundary hH q r
  have hi r : Integrable ((heightBoundary H q r).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (hm r)
  calc
    _ = ∑ r ∈ Finset.range q, ∫ x, (heightBoundary H q r).indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact (integral_indicator_one (μ := μ) (hm r)).symm
    _ = ∫ x, ∑ r ∈ Finset.range q, (heightBoundary H q r).indicator (fun _ => (1:ℝ)) x ∂μ :=
      (integral_finsetSum _ (fun r _ => hi r)).symm
    _ = 1 := by
      have he (x : Y) : (∑ r ∈ Finset.range q,
          (heightBoundary H q r).indicator (fun _ => (1:ℝ)) x) = 1 := by
        simpa only [heightBoundary,indicator_apply,mem_ofPred_eq] using
          sum_shifted_height_boundaries (H x) q hq
      simp_rw [he]
      simp

theorem exists_shift_heightBoundary_le
    (μ : Measure Y) [IsProbabilityMeasure μ] (H : Y → ℕ) (hH : Measurable H)
    (q : ℕ) (hq : 0 < q) :
    ∃ r < q, μ.real (heightBoundary H q r) ≤ 1/(q:ℝ) := by
  by_contra h
  have hh : ∀ r ∈ Finset.range q, 1/(q:ℝ) < μ.real (heightBoundary H q r) := by
    intro r hr
    exact lt_of_not_ge (fun he => h ⟨r,Finset.mem_range.mp hr,he⟩)
  have hs := Finset.sum_lt_sum (fun r hr => (hh r hr).le)
    ⟨0,Finset.mem_range.mpr hq,hh 0 (Finset.mem_range.mpr hq)⟩
  rw [sum_heightBoundary_measures μ H hH q hq] at hs
  have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,one_div,
    mul_inv_cancel₀ hqr] at hs
  exact (lt_irrefl 1 hs)

omit [MeasurableSpace Y] in
lemma height_bin_change_subset (H : Y → ℕ) (T : Y → Y)
    (hstep : ∀ x, H (T x) ≤ H x+1 ∧ H x ≤ H (T x)+1) (q r : ℕ) :
    {x | (H (T x)+r)/q ≠ (H x+r)/q} ⊆
      heightBoundary H q r ∪ T ⁻¹' heightBoundary H q r := by
  intro x hx
  have hs := hstep x
  change (H (T x)+r)/q ≠ (H x+r)/q at hx
  by_cases he : H (T x)=H x
  · exact (hx (congrArg (fun a => (a+r)/q) he)).elim
  by_cases hlt : H (T x) < H x
  · right
    have hh : H x=H (T x)+1 := by omega
    change (H (T x)+r+1)/q ≠ (H (T x)+r)/q
    have ha : H x+r=H (T x)+r+1 := by omega
    rw [ha] at hx
    exact hx.symm
  · left
    have hh : H (T x)=H x+1 := by omega
    change (H x+r+1)/q ≠ (H x+r)/q
    have ha : H (T x)+r=H x+r+1 := by omega
    rwa [ha] at hx

/-- Coarse height bins can be shifted so their one-step changes have
arbitrarily small probability, even when the height has infinite mean. -/
theorem exists_shift_rare_height_changes
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ x, H (T x) ≤ H x+1 ∧ H x ≤ H (T x)+1)
    (q : ℕ) (hq : 0 < q) :
    ∃ r < q, μ.real {x | (H (T x)+r)/q ≠ (H x+r)/q} ≤ 2/(q:ℝ) := by
  obtain ⟨r,hr,hb⟩ := exists_shift_heightBoundary_le μ H hH q hq
  refine ⟨r,hr,?_⟩
  have hm := measurableSet_heightBoundary hH q r
  have he : μ.real (T ⁻¹' heightBoundary H q r) = μ.real (heightBoundary H q r) :=
    congrArg ENNReal.toReal (hT.measure_preimage hm.nullMeasurableSet)
  calc
    _ ≤ μ.real (heightBoundary H q r ∪ T ⁻¹' heightBoundary H q r) :=
      measureReal_mono (height_bin_change_subset H T hstep q r) (measure_ne_top _ _)
    _ ≤ μ.real (heightBoundary H q r) + μ.real (T ⁻¹' heightBoundary H q r) :=
      measureReal_union_le _ _
    _ = 2*μ.real (heightBoundary H q r) := by rw [he]; ring
    _ ≤ 2/(q:ℝ) := by
      calc
        _ ≤ 2*(1/(q:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
        _ = _ := by ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SmallHeightEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse heights with uniformly small finite-observation entropy

A shift of a sufficiently coarse binning has rare changes. The ternary
reconstruction bound therefore makes every finite truncation have small
entropy rate, without any moment assumption on the original height.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_coarse_height_small_entropy
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (H : Y → ℕ) (hH : Measurable H)
    (hstep : ∀ x, H (T x) ≤ H x+1 ∧ H x ≤ H (T x)+1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (q r : ℕ), 0 < q ∧ r < q ∧ ∀ N : ℕ,
      observationEntropyRate μ T (heightClip (fun x => (H x+r)/q) N) < ε := by
  obtain ⟨δ,hδ,hsmall⟩ := rareTernaryCost_small hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (half_pos hδ)
  let q := k+1
  have hq : 0 < q := Nat.succ_pos k
  have hqδ : 2/(q:ℝ) < δ := by
    have he : 2/(q:ℝ)=2*(1/(k+1:ℝ)) := by dsimp [q]; push_cast <;> ring
    rw [he]
    linarith
  obtain ⟨r,hr,hchange⟩ := exists_shift_rare_height_changes μ hT H hH hstep q hq
  let J : Y → ℕ := fun x => (H x+r)/q
  have hJ : Measurable J := (measurable_of_countable (fun a : ℕ => (a+r)/q)).comp hH
  have hJstep (x : Y) : J (T x) ≤ J x+1 ∧ J x ≤ J (T x)+1 := by
    have hs := hstep x
    constructor
    · calc
        _ ≤ (H x+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
    · calc
        _ ≤ (H (T x)+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
  refine ⟨q,r,hq,hr,?_⟩
  intro N
  obtain ⟨D,decode,hD,hdecode,hmid⟩ := heightClip_increment_model hT.measurable J hJ hJstep N
  have hsub : {x | D x≠1} ⊆ {x | J (T x)≠J x} := by
    intro x hx he
    apply hx
    apply (hmid x).mpr
    apply Fin.ext
    change min (J (T x)) N = min (J x) N
    rw [he]
  have hp : μ.real {x | D x≠1} < δ :=
    ((measureReal_mono hsub (measure_ne_top _ _)).trans hchange).trans_lt hqδ
  exact ((observationEntropyRate_le_incrementEntropy μ hT (heightClip J N)
    (heightClip_measurable hJ N) D hD decode hdecode).trans
      (observationEntropy_ternary_le μ D hD)).trans_lt
        (hsmall _ measureReal_nonneg hp)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LowEntropyRadialHeight
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Controlled radial heights with arbitrarily small truncation entropy

Coarsening retains a subsequence of the radial thresholds, so their
uniform boundary estimate survives unchanged.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_low_entropy_controlled_radial_height {n : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ] (a : G n)
    (ha : MeasurePreserving (fun x => rightAction x a) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B D : ℝ) (t : ℕ → ℝ) (H : X n → ℕ),
      0 < B ∧ 0 ≤ D ∧ Measurable H ∧
      (∀ m, t m ≤ 2*B*(m:ℝ)+B) ∧
      (∀ x m, H x ≤ m ↔
        quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t m) ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1) ∧
      (∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x=t m}=0) ∧
      (∀ m k, μ (realBoundaryStrip
        (quotientLogDistance (Quotient.mk _ (1 : G n))) (t m) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (D*(1/2:ℝ)^k)) ∧
      ∀ N, observationEntropyRate μ (fun x => rightAction x a) (heightClip H N) < ε := by
  obtain ⟨B,t,H,hB,_,hH,ht,hlevel,hcompact,hstep,hboundary⟩ :=
    exists_controlled_radial_height μ a
  obtain ⟨q,r,hq,hr,hent⟩ := exists_coarse_height_small_entropy μ ha H hH hstep hε
  let J : X n → ℕ := fun x => (H x+r)/q
  let idx : ℕ → ℕ := fun m => q*(m+1)-1-r
  let B' : ℝ := 2*B*q
  have hB' : 0 < B' := by dsimp [B'] <;> positivity
  have hj (x : X n) (m : ℕ) : J x ≤ m ↔ H x ≤ idx m := by
    have hqm : r < q*(m+1) := by nlinarith
    change (H x+r)/q ≤ m ↔ H x ≤ q*(m+1)-1-r
    rw [Nat.le_iff_lt_add_one,Nat.div_lt_iff_lt_mul hq,Nat.mul_comm (m+1) q]
    omega
  have hsets (m : ℕ) : {x | J x ≤ m}={x | H x ≤ idx m} :=
    Set.ext fun x => hj x m
  have hlev (x : X n) (m : ℕ) : J x ≤ m ↔
      quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t (idx m) := by
    rw [hj]
    change x ∈ {x | H x ≤ idx m} ↔
      x ∈ {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ t (idx m)}
    rw [hlevel]
  refine ⟨B',16/B,(fun m => t (idx m)),J,hB',by positivity,
    (measurable_of_countable (fun k : ℕ => (k+r)/q)).comp hH,?_,hlev,?_,?_,
    (fun m => (hboundary (idx m)).1),(fun m k => (hboundary (idx m)).2 k),hent⟩
  · intro m
    have hidx : idx m+1 ≤ q*(m+1) := by
      dsimp only [idx]
      have hqm : 0 < q*(m+1) := by positivity
      omega
    have hcast : (idx m:ℝ)+1 ≤ (q:ℝ)*((m:ℝ)+1) := by exact_mod_cast hidx
    calc
      t (idx m) ≤ B*(2*(idx m:ℝ)+1) := (ht (idx m)).2.le
      _ ≤ B*(2*((q:ℝ)*((m:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ = B'*(m:ℝ)+B' := by dsimp [B'] <;> ring
      _ ≤ 2*B'*(m:ℝ)+B' := by nlinarith [mul_nonneg hB'.le (Nat.cast_nonneg m)]
  · intro m
    rw [hsets]
    exact hcompact _
  · intro x
    have hs := hstep x
    constructor
    · calc
        _ ≤ (H x+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq
    · calc
        _ ≤ (H (rightAction x a)+r+q)/q := Nat.div_le_div_right (by omega)
        _ = _ := Nat.add_div_right _ hq

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_BilateralNeutralLifts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilateral observation fibers have neutral relative displacement

The same small radial cells are used in both time directions. Uniqueness
of the small lift identifies the two triangular lifts; their common lift
commutes with the diagonal flow. This supplies the geometry needed to
bound the entropy left over after the complete observation itinerary.
-/

noncomputable section
open Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma commute_diagonalOneParameter_of_weight_support {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (g : G n)
    (hg : ∀ i j, ell i ≠ ell j → g.val i j=0) (t : ℝ) :
    Commute g (diagonalOneParameter ell hell t) := by
  change g * diagonalOneParameter ell hell t = diagonalOneParameter ell hell t * g
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (g.val * Matrix.diagonal (fun k => Real.exp (ell k*t))) i j =
    (Matrix.diagonal (fun k => Real.exp (ell k*t)) * g.val) i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : ell i=ell j
  · rw [h,mul_comm]
  · rw [hg i j h]
    simp

theorem exists_radial_radius_bilateral_neutral_lifts {n : ℕ} (hn : 0 < n)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (B : ℝ) (hB : 0 < B) (H : X n → ℕ)
    (hheight : ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤
      2*B*(H x:ℝ)+B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ Q : X n → ℕ,
      (∀ x y, Q y=Q x →
        ∃ g ∈ matrixBall n (r*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) →
      ∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
  obtain ⟨b,hb,hinj⟩ := exists_uniform_logarithmic_injectivity_radius hn
  let R := b/(2*(n:ℝ)*Real.exp (2*(B+1)))
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hneg : ∑ i, -ell i=0 := by simp only [Finset.sum_neg_distrib,hell,neg_zero]
  obtain ⟨rpos,hp,hp1,hpR,hplus⟩ := exists_radial_radius_small_triangular_lifts
    hn ell hell B hB H hheight R hR
  obtain ⟨rneg,hm,hm1,hmR,hminus⟩ := exists_radial_radius_small_triangular_lifts
    hn (fun i => -ell i) hneg B hB H hheight R hR
  let r := min rpos rneg
  refine ⟨r,lt_min hp hm,(min_le_left _ _).trans hp1,?_⟩
  intro Q hsmall x y hforward hbackward
  have hsp : ∀ x y, Q y=Q x →
      ∃ g ∈ matrixBall n (rpos*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y := by
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := hsmall x y hxy
    exact ⟨g,matrixBall_mono
      (mul_le_mul_of_nonneg_right (min_le_left rpos rneg) (Real.exp_pos _).le) hg,hgx⟩
  have hsm : ∀ x y, Q y=Q x →
      ∃ g ∈ matrixBall n (rneg*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y := by
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := hsmall x y hxy
    exact ⟨g,matrixBall_mono
      (mul_le_mul_of_nonneg_right (min_le_right rpos rneg) (Real.exp_pos _).le) hg,hgx⟩
  obtain ⟨g,hg,hgx,hgt⟩ := hplus Q hsp x y hforward
  have ha : diagonalOneParameter (fun i => -ell i) hneg (-1) =
      diagonalOneParameter ell hell 1 := by
    simpa only [neg_neg] using diagonalOneParameter_neg_weights ell hell (-1)
  obtain ⟨g',hg',hg'x,hg't⟩ := hminus Q hsm x y (by
    rw [ha]
    exact hbackward)
  have heqrad : R*Real.exp (-(4*B)*(H x:ℝ)) =
      b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1))) := by
    have he : Real.exp (2*(2*B*(H x:ℝ)+B+1)) =
        Real.exp (2*(B+1))*Real.exp ((4*B)*(H x:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he,neg_mul,Real.exp_neg]
    dsimp [R]
    field_simp
  have hi := (hinj (2*B*(H x:ℝ)+B) x (hheight x)).injOn
  have hgR : g ∈ matrixBall n (b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1)))) := by
    rw [←heqrad]
    exact matrixBall_mono (mul_le_mul_of_nonneg_right hpR (Real.exp_pos _).le) hg
  have hg'R : g' ∈ matrixBall n (b/(2*(n:ℝ)*Real.exp (2*(2*B*(H x:ℝ)+B+1)))) := by
    rw [←heqrad]
    exact matrixBall_mono (mul_le_mul_of_nonneg_right hmR (Real.exp_pos _).le) hg'
  have heq : g=g' := hi hgR hg'R (hgx.trans hg'x.symm)
  have hsupport : ∀ i j, ell i ≠ ell j → g.val i j=0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rw [heq]
      exact hg't i j (by linarith)
    · exact hgt i j h
  have hrad : rpos*Real.exp (-(4*B)*(H x:ℝ)) ≤ 1 := by
    apply le_trans _ hp1
    apply mul_le_of_le_one_right hp.le
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (H x))]
  exact ⟨g,matrixBall_mono hrad hg,hgx,
    commute_diagonalOneParameter_of_weight_support ell hell g hsupport⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeakStableFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal and unipotent coordinates of a weak stable displacement -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- Positive upper triangular matrices split into a positive diagonal
matrix and an actual ordered upper-root word. -/
theorem upper_triangular_positive_diagonal_factorization {n : ℕ} (g : G n)
    (htri : g.val.IsUpperTriangular) (hpos : ∀ i, 0 < g.val i i) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u := by
  let v : Fin n → ℝ := fun i => Real.log (g.val i i)
  have hprod : ∏ i, g.val i i=1 := (Matrix.det_of_isUpperTriangular htri).symm.trans g.prop
  have hv : ∑ i, v i=0 := by
    dsimp [v]
    rw [←Real.log_prod (fun i _ => (hpos i).ne'),hprod,Real.log_one]
  let a := diagonalOneParameter v hv 1
  let u : G n := a⁻¹*g
  have hu : PositiveRootPattern (allPositiveRoots n) u := by
    intro i j hij
    have hij' : ¬ i < j := by simpa [allPositiveRoots] using hij
    have he : u.val i j=Real.exp (-v i)*g.val i j := by
      change ((diagonalOneParameter v hv 1)⁻¹*g).val i j = _
      rw [←diagonalOneParameter_neg]
      change (Matrix.diagonal (fun i => Real.exp (v i*(-1))) * g.val) i j = _
      rw [Matrix.diagonal_mul]
      congr 2
      ring
    rw [he]
    by_cases heq : i=j
    · subst j
      rw [Matrix.one_apply_eq]
      dsimp [v]
      rw [Real.exp_neg,Real.exp_log (hpos i),inv_mul_cancel₀ (hpos i).ne']
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij') (Ne.symm heq)
      rw [htri hji,Matrix.one_apply_ne heq,mul_zero]
  have hum : u ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootPattern_mem_generated (allPositiveRoots n)
      (fun p hp => (Finset.mem_filter.mp hp).2) (allPositiveRoots_closed n) hu
  obtain ⟨t,ht⟩ := upperRootWord_surjective n ⟨u,hum⟩
  refine ⟨v,hv,t,?_⟩
  rw [ht]
  change g=a*(a⁻¹*g)
  group

/-- A sufficiently small future lift has a neutral diagonal part. Its
remaining part belongs to the genuine strong stable unipotent group. -/
theorem small_weak_stable_factorization {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (hord : StrictMono ell) (g : G n) (hg : g ∈ matrixBall n 1)
    (hzero : ∀ i j, ell j < ell i → g.val i j=0) :
    ∃ (v : Fin n → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime n),
      g=diagonalOneParameter v hv 1 * (completeRootChain n).word u ∧
      ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t) := by
  have htri : g.val.IsUpperTriangular := fun i j hji => hzero i j (hord hji)
  have hpos (i : Fin n) : 0 < g.val i i := by
    have hh := hg i i
    rw [Matrix.one_apply_eq] at hh
    have hh' := (abs_lt.mp hh).1
    linarith
  obtain ⟨v,hv,u,hu⟩ := upper_triangular_positive_diagonal_factorization g htri hpos
  refine ⟨v,hv,u,hu,?_⟩
  intro t
  apply commute_diagonalOneParameter_of_weight_support ell hell
  intro i j hij
  have hne : i ≠ j := by intro he; exact hij (congrArg ell he)
  change (Matrix.diagonal (fun i => Real.exp (v i*1))) i j=0
  exact Matrix.diagonal_apply_ne _ hne

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BranchingSubordinateObservation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded future observation with finite branching

The same low-entropy height and small relative charts provide the weak-stable
and neutral fiber properties, with uniformly finite predecessor labels.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

/-- The branching observation also retains the uniform radial injectivity
radius and a single lift whose every future conjugate is radially small. -/
theorem exists_bounded_branching_subordinate_observation_with_lifts_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (B r₀ : ℝ) (H Q : X (d+1) → ℕ),
      0 < B ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ Measurable H ∧ Measurable Q ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B) ∧
      (∀ x, Set.InjOn (fun g => rightAction x g)
        (matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))))) ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))),
          rightAction x g = y ∧ (∀ i j, ell j < ell i → g.val i j = 0) ∧
          ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ) * g *
            diagonalOneParameter ell hell (-(k:ℝ)) ∈
            matrixBall (d+1) (r₀*Real.exp (-(4*B)*
              (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ)))) ∧
      (∀ᵐ x ∂μ, ∀ s : UpperRootTime (d+1),
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k]
            (rightAction x ((completeRootChain (d+1)).word s))) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        s ∈ (completeRootChain (d+1)).cube 1) ∧
      (∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
      (∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
        H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1) ∧
      (∀ x y, Q y=Q x → H y=H x) ∧
      (∀ x y,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
          Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
        ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
          ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) ∧
      (∀ x y, (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
        ∃ (v : Fin (d+1) → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime (d+1)),
          rightAction x (diagonalOneParameter v hv 1 * (completeRootChain (d+1)).word u)=y ∧
          ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t)) ∧
      UniformFinitePredecessors
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
      ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
        (∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
        ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m) := by
  let a := diagonalOneParameter ell hell (-1)
  have hT : MeasurePreserving (fun x => rightAction x a) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [a]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨B,D,t,H,hB,hD,hH,ht,hlevel,hcompact,hstep,hnull,hbound,hent⟩ :=
    exists_low_entropy_controlled_radial_height μ a hT hε
  have hheight (x : X (d+1)) :
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
    ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
  obtain ⟨rB,hrB,_,hbilateral⟩ := exists_radial_radius_bilateral_neutral_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
  obtain ⟨R,hR,hunique⟩ := exists_uniform_triangular_lift_radius d
  have hcube : (completeRootChain (d+1)).cube 1 ∈
      𝓝 (completeRootChain (d+1)).zeroTime :=
    ((completeRootChain (d+1)).cube_open 1).mem_nhds
      ((completeRootChain (d+1)).zeroTime_mem_cube zero_lt_one)
  rw [(upperRootWord_isEmbedding (d+1)).isInducing.nhds_eq_comap,
    EliminationChain.word_zeroTime] at hcube
  obtain ⟨V,hV,hVcube⟩ := Filter.mem_comap.mp hcube
  obtain ⟨S,hS,hSV⟩ := matrixBall_nhds_basis hV
  let Kp := predecessorPackingRadius (d+1) a (16*Real.exp (4*B)) 16
  have hKp : 0 < Kp := by dsimp [Kp,predecessorPackingRadius] <;> positivity
  have hpackRadius : 0 < 4/((d+1:ℝ)*Kp) := by positivity
  obtain ⟨r₀,hr₀,hr₀1,hrcap₀,hinj,htri⟩ := exists_radial_radius_small_conjugate_lifts
    (Nat.succ_pos d) ell hell B hB H hheight
    (min (min (min R S) rB) (4/((d+1:ℝ)*Kp)))
    (lt_min (lt_min (lt_min hR hS) hrB) hpackRadius)
  have hrcap := hrcap₀.trans (min_le_left (min (min R S) rB) _)
  have hpack : (d+1:ℝ)*Kp*r₀ ≤ 4 := by
    have hh := hrcap₀.trans (min_le_right (min (min R S) rB) _)
    have hnK : 0 < (d+1:ℝ)*Kp := by positivity
    have Hh := (le_div_iff₀ hnK).mp hh
    nlinarith
  obtain ⟨Q,hQ,hfinite,hsmall,hgood,hbranch,hcode⟩ := exists_branching_cover_future_observation
    d ell hell hgap μ hA B hB H hH t ht hlevel hstep
    hnull hD hbound hr₀ hr₀1 (by simpa only [Kp,a,Nat.cast_add,Nat.cast_one] using hpack)
  have hstrong : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))),
        rightAction x g = y ∧ (∀ i j, ell j < ell i → g.val i j = 0) ∧
        ∀ k : ℕ, diagonalOneParameter ell hell (k:ℝ) * g *
          diagonalOneParameter ell hell (-(k:ℝ)) ∈
          matrixBall (d+1) (r₀*Real.exp (-(4*B)*
            (H ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x):ℝ))) := by
    intro x y hxy
    exact htri Q (fun x y hxy => (hsmall x y hxy).2) x y hxy
  have hneutral : ∀ x y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t) := by
    apply hbilateral Q
    intro x y hxy
    obtain ⟨g,hg,hgx⟩ := (hsmall x y hxy).2
    exact ⟨g,matrixBall_mono (mul_le_mul_of_nonneg_right
      (hrcap.trans (min_le_right _ _)) (Real.exp_pos _).le) hg,hgx⟩
  have hfactor : ∀ x y, (∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      ∃ (v : Fin (d+1) → ℝ) (hv : ∑ i, v i=0) (u : UpperRootTime (d+1)),
        rightAction x (diagonalOneParameter v hv 1 * (completeRootChain (d+1)).word u)=y ∧
        ∀ t : ℝ, Commute (diagonalOneParameter v hv 1) (diagonalOneParameter ell hell t) := by
    intro x y hxy
    obtain ⟨g,hg,hgx,hgt,_⟩ := htri Q (fun x y hxy => (hsmall x y hxy).2) x y hxy
    have hg1 : g ∈ matrixBall (d+1) 1 := by
      apply matrixBall_mono (r := r₀*Real.exp (-(4*B)*(H x:ℝ))) _ hg
      have he : Real.exp (-(4*B)*(H x:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
        nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (α := ℝ) (H x))])
      exact (mul_le_mul_of_nonneg_left he hr₀.le).trans (by simpa using hr₀1)
    have hord : StrictMono ell := by
      intro i j hij
      have hh := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
      have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
      dsimp at hh
      linarith
    obtain ⟨v,hv,u,he,hd⟩ := small_weak_stable_factorization ell hell hord g hg1 hgt
    refine ⟨v,hv,u,?_,hd⟩
    rw [←he]
    exact hgx
  refine ⟨B,r₀,H,Q,hB,hr₀,hr₀1,hH,hQ,hheight,hinj,hcompact,hfinite,hent,hstrong,?_,hgood,hstep,
    (fun x y hxy => (hsmall x y hxy).1),hneutral,hfactor,hbranch,hcode⟩
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx s hs
  obtain ⟨g,hg,hgx,hgt,_⟩ := htri Q (fun x y hxy => (hsmall x y hxy).2)
    x (rightAction x ((completeRootChain (d+1)).word s)) hs
  have hrad : r₀*Real.exp (-(4*B)*(H x:ℝ)) ≤ min R S := by
    apply le_trans _ (hrcap.trans (min_le_left _ _))
    apply mul_le_of_le_one_right hr₀.le
    exact Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (H x))])
  have hgR : g ∈ matrixBall (d+1) R :=
    matrixBall_mono (hrad.trans (min_le_left _ _)) hg
  have hgS : g ∈ matrixBall (d+1) S :=
    matrixBall_mono (hrad.trans (min_le_right _ _)) hg
  have hgtri : g.val.IsUpperTriangular := by
    intro i j hji
    apply hgt i j
    have hh := hgap ⟨(j,i), Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji⟩⟩
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp at hh
    linarith
  have hu := upperRootWord_mem (d+1) s
  have hutri : ((completeRootChain (d+1)).word s).val.IsUpperTriangular := by
    intro i j hji
    have hp := positiveRootGeneratedGroup_pattern (allPositiveRoots (d+1))
      (allPositiveRoots_closed (d+1)) hu i j (by
        simpa [allPositiveRoots] using not_lt_of_ge hji.le)
    change ((completeRootChain (d+1)).word s).val i j =
      (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j at hp
    exact hp.trans (Matrix.one_apply_ne (show i ≠ j from ne_of_gt hji))
  have hueq := hunique x hx ((completeRootChain (d+1)).word s) g hutri
    (upperRoot_diagonal hu) hgR hgtri hgx.symm
  exact hVcube (by change (completeRootChain (d+1)).word s ∈ V; rw [hueq]; exact hSV hgS)

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts_oai := @OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts_oai
