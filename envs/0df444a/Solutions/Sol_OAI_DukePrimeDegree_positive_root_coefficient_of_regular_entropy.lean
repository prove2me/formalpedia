-- Prove2me | solution 1 for OAI.DukePrimeDegree.positive_root_coefficient_of_regular_entropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:12.020802+00:00
-- url     : https://prove2.me/submissions/e77ce324-91b2-4a93-9346-f42e6e034f46

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
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Composition.MapComap
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
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_DukePrimeDegree_positive_root_coefficient_of_positive_diagonal_entropy

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_EntropyInverse
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Time reversal of entropy

Reversing a finite orbit name and shifting its starting point does not
change its Shannon entropy. This proves equality of
Kolmogorov--Sinai entropy for mutually inverse measure-preserving maps,
as used in EKL (2006), equation (3.2).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma inverse_orbitName {Y α : Type*} (T S : Y → Y)
    (hST : Function.LeftInverse S T) (P : Y → α) (N : ℕ) (y : Y) :
    orbitName S P N (T^[N - 1] y) =
      reverseWordEquiv α N (orbitName T P N y) := by
  funext j
  change P (S^[j.val] (T^[N - 1] y)) = P (T^[j.rev.val] y)
  congr 1
  have hN : N - 1 = j.val + (N - 1 - j.val) := by omega
  rw [hN, Function.iterate_add_apply]
  rw [(hST.iterate j.val) _]
  rw [Fin.val_rev]
  exact congrArg (fun m : ℕ => T^[m] y) (by omega)

/-- Finite block entropies agree exactly under time reversal. -/
theorem orbitEntropy_inverse {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName S P N) =
      observationEntropy μ (orbitName T P N) := by
  calc
    observationEntropy μ (orbitName S P N) =
        observationEntropy μ (fun y => orbitName S P N (T^[N - 1] y)) :=
      (observationEntropy_comp_preserving μ _
        (orbitName_measurable_fiber hS hP N) (hT.iterate (N - 1))).symm
    _ = observationEntropy μ (fun y => reverseWordEquiv α N (orbitName T P N y)) := by
      congr 1
      funext y
      exact inverse_orbitName T S hST P N y
    _ = _ := observationEntropy_equiv μ _ _

/-- Equality holds for every finite observation, before taking the supremum. -/
theorem observationEntropyRate_inverse {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ S P = observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  rw [orbitEntropy_inverse μ T S hT hS hST P hP]

/-- Entropy is invariant under reversing an invertible measure-preserving map. -/
theorem measureEntropy_inverse {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T) :
    measureEntropy μ S = measureEntropy μ T := by
  unfold measureEntropy
  congr 1
  funext k
  congr 1
  funext P
  congr 1
  funext hP
  rw [observationEntropyRate_inverse μ T S hT hS hST P hP]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

lemma observationEntropyRate_nonneg {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    0 ≤ observationEntropyRate μ T P := by
  unfold observationEntropyRate
  apply le_csInf
  · exact ⟨_,1,(show (1:ℕ) ≤ 1 from le_rfl),rfl⟩
  · rintro _ ⟨N,_,rfl⟩
    exact div_nonneg (observationEntropy_nonneg μ _ (orbitName_measurable_fiber hT hP N))
      (Nat.cast_nonneg _)

lemma observationEntropyRate_eq_zero_of_measureEntropy {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y} (hT : Measurable T)
    (hzero : measureEntropy μ T = 0) {k : ℕ} (P : Y → Fin k)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P = 0 := by
  have H : ENNReal.ofReal (observationEntropyRate μ T P) ≤ measureEntropy μ T :=
    le_iSup_of_le k (le_iSup_of_le P (le_iSup_of_le hP le_rfl))
  rw [hzero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at H
  exact le_antisymm H (observationEntropyRate_nonneg μ hT P hP)



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_DiagonalEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
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

/-- Time reversal for the diagonal action on the arithmetic quotient. -/
theorem diagonal_entropy_neg (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-t))) =
      measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) := by
  apply measureEntropy_inverse
  · refine ⟨(continuous_rightAction _).measurable, ?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  · exact (continuous_rightAction _).measurable
  · intro x
    change rightAction (rightAction x (diagonalOneParameter ell hell t))
      (diagonalOneParameter ell hell (-t)) = x
    rw [rightAction_mul, diagonalOneParameter_neg]
    simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationRefinement
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FourthIterateEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive entropy survives the fourth iterate

The regular weights used in the finite coefficient-balance test are four
times the original regular weights. Grouping four consecutive symbols
transfers positive metric entropy to that time-four map. Only this fixed
iterate is needed here.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma orbitName_four_blocks {Y α : Type*}
    (T : Y → Y) (P : Y → α) (N : ℕ) :
    orbitName T P (N * 4) = fun y =>
      fourWordEquiv α N (orbitName (T^[4]) (orbitName T P 4) N y) := by
  funext y
  apply (fourWordEquiv α N).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i j
  change P (T^[j.val + 4 * i.val] y) = P (T^[j.val] ((T^[4])^[i.val] y))
  rw [Function.iterate_add_apply, Function.iterate_mul]

private lemma observationEntropyRate_recode {Y α β : Type*}
    [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) (e : α ≃ β) :
    observationEntropyRate μ T (fun y => e (P y)) = observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  congr 1
  have hi : Function.Injective (fun w : Fin N → α => fun i => e (w i)) := by
    intro w v h
    funext i
    exact e.injective (congrFun h i)
  exact observationEntropy_injective μ (orbitName T P N) _ hi

/-- Four-symbol blocks have four times the original entropy rate. -/
theorem observationEntropyRate_four_blocks {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ (T^[4]) (orbitName T P 4) =
      4 * observationEntropyRate μ T P := by
  have hsub : Tendsto (fun N : ℕ => N * 4) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have H := (tendsto_observationEntropyRate μ hT P hP).comp hsub
  have hscaled : Tendsto (fun N : ℕ => 4 *
      (observationEntropy μ (orbitName T P (N * 4)) / (N * 4 : ℕ))) atTop
      (𝓝 (4 * observationEntropyRate μ T P)) := tendsto_const_nhds.mul H
  have heq : (fun N : ℕ => 4 *
      (observationEntropy μ (orbitName T P (N * 4)) / (N * 4 : ℕ))) =
      (fun N : ℕ =>
        observationEntropy μ (orbitName (T^[4]) (orbitName T P 4) N) / N) := by
    funext N
    rw [orbitName_four_blocks, observationEntropy_equiv]
    by_cases hN : N = 0
    · subst N
      simp
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    push_cast
    field_simp [hN']
  rw [heq] at hscaled
  exact tendsto_nhds_unique
    (tendsto_observationEntropyRate μ (hT.iterate 4) (orbitName T P 4)
      (orbitName_measurable_fiber hT.measurable hP 4)) hscaled

/-- Vanishing entropy of the time-four map forces vanishing entropy of
the original map. This uses the actual supremum over finite observations. -/
theorem measureEntropy_eq_zero_of_fourth_iterate {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hzero : measureEntropy μ (T^[4]) = 0) :
    measureEntropy μ T = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  let e := Fintype.equivFin (Fin 4 → Fin k)
  let Q := fun y => e (orbitName T P 4 y)
  have hQ (a) : MeasurableSet {y | Q y = a} := by
    have heq : {y | Q y = a} = {y | orbitName T P 4 y = e.symm a} := by
      ext y
      exact e.eq_symm_apply.symm
    rw [heq]
    exact orbitName_measurable_fiber hT.measurable hP 4 _
  have hz := observationEntropyRate_eq_zero_of_measureEntropy μ
    (hT.measurable.iterate 4) hzero Q hQ
  rw [observationEntropyRate_recode μ (T^[4]) (orbitName T P 4) e,
    observationEntropyRate_four_blocks μ hT P hP] at hz
  have hp : observationEntropyRate μ T P = 0 := by linarith
  rw [hp, ENNReal.ofReal_zero]
  exact bot_le

theorem measureEntropy_fourth_iterate_pos {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hpos : 0 < measureEntropy μ T) :
    0 < measureEntropy μ (T^[4]) := by
  by_contra h
  have hz : measureEntropy μ (T^[4]) = 0 := le_antisymm (not_lt.mp h) bot_le
  exact (ne_of_gt hpos) (measureEntropy_eq_zero_of_fourth_iterate μ hT hz)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularEntropyTests
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely many regular weights suffice for coefficient balance

For the prime-degree application the balance argument does not need the
entropy formula at singular weights. One regular weight and one small
perturbation for each coordinate suffice, together with their negatives.
All positive gaps in these explicit weights are at least log 4.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma regularEntropyTest_none (d : ℕ) (i : Fin (d+1)) :
    regularEntropyTest d none i = 4 * regularDiagonalWeights d i := by
  simp only [regularEntropyTest, rawEntropyTest, reduceCtorEq, ite_false, if_false,
    add_zero, ←Finset.mul_sum, regularDiagonalWeights]
  ring

lemma regularEntropyTest_gap (d : ℕ) (a : Option (Fin (d+1)))
    {i j : Fin (d+1)} (hij : i < j) :
    Real.log 4 ≤ regularEntropyTest d a j - regularEntropyTest d a i := by
  have hg : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Nat.succ_le_of_lt hij)
  have hi : (if a = some i then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hj : 0 ≤ (if a = some j then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have hl : Real.log 4 ≤ (3:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
    norm_num at h
    exact h
  dsimp only [regularEntropyTest,rawEntropyTest]
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularEntropyScaling
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive entropy at the base regular test weight -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonal_regularEntropyTest_none (d : ℕ) :
    diagonalOneParameter (regularEntropyTest d none) (regularEntropyTest_sum d none) 1 =
      diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 4 := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  rw [regularEntropyTest_none]
  congr 1
  ring

/-- The test weight indexed by `none` is the fourth iterate of the
original regular diagonal transformation. -/
theorem positive_entropy_regular_test (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d none) (regularEntropyTest_sum d none) 1)) := by
  let T := fun x => rightAction x
    (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have heq : (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d none) (regularEntropyTest_sum d none) 1)) =
      T^[4] := by
    funext x
    have hn : diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 4 =
        (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)^4 := by
      simpa only [Nat.cast_ofNat] using
        diagonalOneParameter_nat (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 4
    rw [diagonal_regularEntropyTest_none, hn]
    exact (rightAction_iterate _ 4 x).symm
  rw [heq]
  exact measureEntropy_fourth_iterate_pos μ hT hpos

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_AtomicRootPositivity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive entropy gives a positive actual root coefficient -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

/-- The positive-entropy hypothesis used by the prime-degree application
already supplies a positive root coefficient, without EKL Proposition3.1(3). -/
theorem positive_root_coefficient_of_regular_entropy_oai (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hpos : 0 < measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1))) :
    ∃ i j : Fin (d+1), i < j ∧ 0 < canonicalRootCoefficient d μ i j := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hp := positive_entropy_regular_test d μ hA hpos
  have hn := diagonal_entropy_neg d (regularEntropyTest d none)
    (regularEntropyTest_sum d none) μ hA 1
  rw [←hn] at hp
  exact positive_root_coefficient_of_positive_diagonal_entropy d
    (regularEntropyTest d none) (regularEntropyTest_sum d none)
    (fun p => regularEntropyTest_gap d none (Finset.mem_filter.mp p.prop).2) μ hp

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.positive_root_coefficient_of_regular_entropy_oai := @OAI.DukePrimeDegree.positive_root_coefficient_of_regular_entropy_oai
