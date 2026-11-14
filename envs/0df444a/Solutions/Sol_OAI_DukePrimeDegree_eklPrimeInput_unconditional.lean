-- Prove2me | solution 1 for OAI.DukePrimeDegree.eklPrimeInput_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:40:24.628355+00:00
-- url     : https://prove2.me/submissions/f756df1e-aef1-403c-b699-50d5aacdec39

import Mathlib
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Encodable.Lattice
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke035
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_eklPrimeInput_of_regular_entropy_upper_bounds
import Theorems.Thm_OAI_DukePrimeDegree_exists_bounded_branching_subordinate_observation_with_lifts
import Theorems.Thm_OAI_DukePrimeDegree_exists_sparse_upperRoot_comparison
import Theorems.Thm_OAI_DukePrimeDegree_negative_diagonal_entropy_le_root_sum_of_small_auxiliary

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
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
open scoped Classical Pointwise


namespace PrimeDegreePackets

lemma observationEntropy_map {Y Z α : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [Fintype α] (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (P : Z → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    observationEntropy (Measure.map f μ) P = observationEntropy μ (P ∘ f) := by
  unfold observationEntropy finiteShannon
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (Measure.map f μ {z | P z = a}).toReal = _
  rw [Measure.map_apply hf (hP a)]
  rfl

lemma orbitName_semiconj {Y Z α : Type*} (f : Y → Z) (S : Y → Y) (T : Z → Z)
    (h : ∀ y, f (S y) = T (f y)) (P : Z → α) (N : ℕ) :
    orbitName T P N ∘ f = orbitName S (P ∘ f) N := by
  have H (n : ℕ) (y : Y) : f (S^[n] y) = T^[n] (f y) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply',h,ih]
  ext y j
  exact congrArg P (H j.val y).symm

lemma observationEntropyRate_map_semiconj {Y Z α : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z] [Fintype α]
    (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (S : Y → Y) (T : Z → Z) (hT : Measurable T)
    (h : ∀ y, f (S y) = T (f y))
    (P : Z → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    observationEntropyRate (Measure.map f μ) T P =
      observationEntropyRate μ S (P ∘ f) := by
  unfold observationEntropyRate
  congr 3
  funext N
  rw [observationEntropy_map μ f hf _ (orbitName_measurable_fiber hT hP N),
    orbitName_semiconj f S T h P N]

 
theorem measureEntropy_map_semiconj_le {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (f : Y → Z) (hf : Measurable f)
    (S : Y → Y) (T : Z → Z) (hT : Measurable T)
    (h : ∀ y, f (S y) = T (f y)) :
    measureEntropy (Measure.map f μ) T ≤ measureEntropy μ S := by
  unfold measureEntropy
  refine iSup_le fun k => iSup_le fun P => iSup_le fun hP => ?_
  rw [observationEntropyRate_map_semiconj μ f hf S T hT h P hP]
  apply le_iSup_of_le k
  apply le_iSup_of_le (P ∘ f)
  exact le_iSup_of_le (fun a => (hP a).preimage hf) le_rfl

end PrimeDegreePackets


open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeDuality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory


namespace PrimeDegreePackets
open ThetaConstruction

lemma restoredLogCoordinates_sum {d : ℕ} (u : LogCoordinates d) :
    ∑ i, restoredLogCoordinates u i = 0 := by
  simp [restoredLogCoordinates,Fin.sum_univ_castSucc]

end PrimeDegreePackets


open MeasureTheory Module WithLp

open scoped BigOperators NumberField nonZeroDivisors ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_DiagonalEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalFiberRecoding
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylReindex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting coordinates on the arithmetic quotient

Coordinate reversal transfers the increasing regular weight construction
to its decreasing counterpart. Reindexing preserves determinant one and
the integral lattice, so it acts on the actual quotient.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

lemma quotientReindex_rightAction {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : X n) (g : G n) :
    quotientReindex e (rightAction x g) =
      rightAction (quotientReindex e x) (reindexSpecialLinear ℝ e g) := by
  induction x using Quotient.inductionOn with
  | h a => exact congrArg (Quotient.mk _) ((reindexSpecialLinear ℝ e).map_mul a g)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WeylEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy under coordinate permutations of the quotient -/

noncomputable section
open MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measureEntropy_map_measurableEquiv {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure Y) (e : Y ≃ᵐ Z) (S : Y → Y) (T : Z → Z)
    (hS : Measurable S) (hT : Measurable T)
    (h : ∀ y, e (S y) = T (e y)) :
    measureEntropy (μ.map e) T = measureEntropy μ S := by
  apply le_antisymm
  · exact measureEntropy_map_semiconj_le μ e e.measurable S T hT h
  · have hi (z : Z) : e.symm (T z) = S (e.symm z) := by
      apply e.injective
      simpa only [e.apply_symm_apply] using (h (e.symm z)).symm
    have H := measureEntropy_map_semiconj_le (μ.map e) e.symm e.symm.measurable T S hS hi
    have hmap : (μ.map e).map e.symm = μ := by
      rw [Measure.map_map e.symm.measurable e.measurable]
      have he : e.symm ∘ e = id := by funext y; exact e.symm_apply_apply y
      rw [he, Measure.map_id]
    rwa [hmap] at H

lemma reindex_diagonalOneParameter {n : ℕ} (e : Equiv.Perm (Fin n))
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    reindexSpecialLinear ℝ e (diagonalOneParameter ell hell t) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) t := by
  apply Subtype.ext
  ext i j
  change (Matrix.diagonal (fun k => Real.exp (ell k * t))) (e.symm i) (e.symm j) =
    (Matrix.diagonal (fun k => Real.exp (ell (e.symm k) * t))) i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun h => hij (e.symm.injective h)),
      Matrix.diagonal_apply_ne _ hij]

theorem diagonal_entropy_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1))) (ell : Fin (d+1) → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    measureEntropy (μ.map (quotientReindex e))
      (fun x => rightAction x (diagonalOneParameter
        (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) t)) =
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) := by
  exact measureEntropy_map_measurableEquiv μ (quotientReindexHomeomorph e).toMeasurableEquiv
    _ _ (continuous_rightAction _).measurable (continuous_rightAction _).measurable
    (fun x => by
      change quotientReindex e (rightAction x _) = rightAction (quotientReindex e x) _
      rw [quotientReindex_rightAction, reindex_diagonalOneParameter])

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylDiagonalAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal invariance and ergodicity under coordinate permutations -/

noncomputable section
open MeasureTheory Set Filter
namespace DukePrimeDegree
open PrimeDegreePackets

lemma reindex_diagonalFlow (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) :
    reindexSpecialLinear ℝ e (diagonalFlow u) = diagonalFlow (reindexLogCoordinates d e u) := by
  have hs := restoredLogCoordinates_sum u
  have he : diagonalOneParameter (restoredLogCoordinates u) hs 1=diagonalFlow u := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    congr 1
    funext i
    simp only [restoredLogCoordinates,Fin.snoc_castSucc,mul_one]
  rw [←he,reindex_diagonalOneParameter,diagonalOneParameter_eq_diagonalFlow]
  congr 1
  funext i
  simp only [reindexLogCoordinates,mul_one]

lemma reindex_diagonalFlow_conjugacy (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) (x : X (d+1)) :
    quotientReindex e (rightAction x (diagonalFlow u)) =
      rightAction (quotientReindex e x) (diagonalFlow (reindexLogCoordinates d e u)) := by
  rw [quotientReindex_rightAction,reindex_diagonalFlow]

lemma reindex_diagonalFlow_reverse (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (u : LogCoordinates d) (x : X (d+1)) :
    quotientReindex e (rightAction x (diagonalFlow (reindexLogCoordinates d e.symm u))) =
      rightAction (quotientReindex e x) (diagonalFlow u) := by
  apply (quotientReindexHomeomorph e.symm).injective
  change quotientReindex e.symm (quotientReindex e
    (rightAction x (diagonalFlow (reindexLogCoordinates d e.symm u)))) =
      quotientReindex e.symm (rightAction (quotientReindex e x) (diagonalFlow u))
  rw [quotientReindex_symm_apply,reindex_diagonalFlow_conjugacy,
    quotientReindex_symm_apply]

/-- The full diagonal action remains invariant after reindexing. -/
theorem diagonal_invariant_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (u : LogCoordinates d) :
    (μ.map (quotientReindex e)).map (fun x => rightAction x (diagonalFlow u)) =
      μ.map (quotientReindex e) := by
  rw [Measure.map_map (continuous_rightAction _).measurable
    (continuous_quotientReindex e).measurable]
  have he : (fun x => rightAction x (diagonalFlow u)) ∘ quotientReindex e =
      quotientReindex e ∘ (fun x => rightAction x
        (diagonalFlow (reindexLogCoordinates d e.symm u))) := by
    funext x
    exact (reindex_diagonalFlow_reverse d e u x).symm
  rw [he,←Measure.map_map (continuous_quotientReindex e).measurable
    (continuous_rightAction _).measurable,hA]

/-- Ergodicity uses the full diagonal group, whose parameters are permuted
along with the coordinates. -/
theorem diagonal_ergodic_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    (μ : Measure (X (d+1)))
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
      (μ.map (quotientReindex e)) := by
  let E := (quotientReindexHomeomorph e).toMeasurableEquiv
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro u S hS
    exact (show MeasurePreserving (fun x => rightAction x (diagonalFlow u.toAdd))
      (μ.map (quotientReindex e)) (μ.map (quotientReindex e)) from
      ⟨(continuous_rightAction _).measurable,diagonal_invariant_reindex d e μ hA _⟩).measure_preimage
        hS.nullMeasurableSet
  · intro S hS hfix
    change EventuallyConst S (ae (μ.map E))
    rw [←E.map_ae μ,←eventuallyConst_preimage]
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
      (G := Multiplicative (LogCoordinates d)) (hS.preimage E.measurable)
    intro u
    have h := ae_of_ae_map E.measurable.aemeasurable
      (hfix (Multiplicative.ofAdd (reindexLogCoordinates d e u.toAdd))).mem_iff
    filter_upwards [h] with x hx
    apply propext
    change rightAction x (diagonalFlow u.toAdd) ∈ E ⁻¹' S ↔ x ∈ E ⁻¹' S
    change rightAction (quotientReindex e x)
      (diagonalFlow (reindexLogCoordinates d e u.toAdd)) ∈ S ↔ quotientReindex e x ∈ S at hx
    change quotientReindex e (rightAction x (diagonalFlow u.toAdd)) ∈ S ↔
      quotientReindex e x ∈ S
    rw [reindex_diagonalFlow_conjugacy]
    exact hx

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiagonalPeriodicity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodicity of one diagonal map under full diagonal ergodicity

The chosen map need not itself be ergodic.  Its period-n fixed sets are
invariant under every diagonal translation, hence each has measure zero
or one.  There is either a common positive period almost everywhere or
almost every point has no positive period.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_periodicity_dichotomy (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    (∃ n : ℕ, 0 < n ∧ ∀ᵐ x ∂μ,
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x = x) ∨
    (∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n →
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x ≠ x) := by
  let T : X (d + 1) → X (d + 1) :=
    fun x => rightAction x (diagonalOneParameter ell hell t)
  have hcomm (u : Multiplicative (LogCoordinates d)) :
      Function.Commute T (fun x => u • x) := by
    intro x
    change rightAction (rightAction x (diagonalFlow u.toAdd))
      (diagonalOneParameter ell hell t) =
        rightAction (rightAction x (diagonalOneParameter ell hell t)) (diagonalFlow u.toAdd)
    rw [rightAction_mul, rightAction_mul]
    congr 1
    apply Subtype.ext
    exact (Matrix.commute_diagonal _ _).eq
  have hzeroone (n : ℕ) :
      (∀ᵐ x ∂μ, T^[n] x = x) ∨ (∀ᵐ x ∂μ, T^[n] x ≠ x) := by
    let E : Set (X (d + 1)) := {x | T^[n] x = x}
    have hE : MeasurableSet E :=
      (isClosed_eq ((continuous_rightAction _).iterate n) continuous_id).measurableSet
    have he : EventuallyConst E (ae μ) :=
      ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
      (G := Multiplicative (LogCoordinates d)) (α := X (d + 1)) (μ := μ) hE (by
        intro u
        apply Filter.Eventually.of_forall
        intro x
        change (T^[n] (u • x) = u • x) = (T^[n] x = x)
        apply propext
        rw [(hcomm u).iterate_left n x]
        exact (MulAction.injective u).eq_iff)
    exact eventuallyConst_set.mp he
  by_cases hp : ∃ n : ℕ, 0 < n ∧ ∀ᵐ x ∂μ, T^[n] x = x
  · exact Or.inl hp
  · right
    apply ae_all_iff.mpr
    intro n
    by_cases hn : 0 < n
    · rcases hzeroone n with hyes | hno
      · exact (hp ⟨n, hn, hyes⟩).elim
      · exact hno.mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ hx => (hn hx).elim)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PeriodicEntropyZero
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere periodicity gives zero finite-observation entropy

A common positive period makes every long orbit name a deterministic
extension of one fixed finite name.  Thus block entropy stays bounded and
its entropy rate is zero.  Combining this with full-A ergodicity isolates
the aperiodic branch without asserting ergodicity of the chosen map.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma ae_orbitName_periodic_extension {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T : Y → Y) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ᵐ x ∂μ, T^[n] x = x) (P : Y → α) (N : ℕ) :
    orbitName T P N =ᵐ[μ] fun x => periodicNameExtension α n hn N (orbitName T P n x) := by
  filter_upwards [hperiod] with x hx
  funext j
  change P (T^[j.val] x) = P (T^[j.val % n] x)
  exact congrArg P ((show Function.IsPeriodicPt T n x from hx).iterate_mod_apply j.val).symm

/-- The bound is independent of the length of the observed orbit. -/
theorem orbitEntropy_le_period_name {Y α : Type*}
    [MeasurableSpace Y] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (T : Y → Y) (hT : Measurable T)
    (n : ℕ) (hn : 0 < n) (hperiod : ∀ᵐ x ∂μ, T^[n] x = x)
    (P : Y → α) (hP : Measurable P) (N : ℕ) :
    observationEntropy μ (orbitName T P N) ≤ observationEntropy μ (orbitName T P n) := by
  let Q := orbitName T P n
  have hQ : Measurable Q := measurable_pi_iff.mpr (fun j => hP.comp (hT.iterate j.val))
  rw [observationEntropy_eq_of_ae_eq μ _ _
    (ae_orbitName_periodic_extension μ T n hn hperiod P N)]
  apply observationEntropy_le_of_refines μ _ Q
    (fun w => ((measurable_of_finite (periodicNameExtension α n hn N)).comp hQ)
      (measurableSet_singleton w))
    (fun w => hQ (measurableSet_singleton w))
  intro x y hxy
  exact congrArg (periodicNameExtension α n hn N) hxy

theorem observationEntropyRate_zero_of_ae_periodic {Y α : Type*}
    [MeasurableSpace Y] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ᵐ x ∂μ, T^[n] x = x) (P : Y → α) (hP : Measurable P) :
    observationEntropyRate μ T P = 0 := by
  have hPf (a : α) : MeasurableSet {x | P x = a} := hP (measurableSet_singleton a)
  have hu : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N) / (N : ℝ) ≤
        observationEntropy μ (orbitName T P n) / (N : ℝ) :=
    Filter.Eventually.of_forall fun N => div_le_div_of_nonneg_right
      (orbitEntropy_le_period_name μ T hT.measurable n hn hperiod P hP N) (Nat.cast_nonneg N)
  have hz : Tendsto (fun N : ℕ => observationEntropy μ (orbitName T P n) / (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact le_antisymm
    (le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hPf) hz hu)
    (observationEntropyRate_nonneg μ hT.measurable P hPf)

theorem measureEntropy_zero_of_ae_periodic {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ᵐ x ∂μ, T^[n] x = x) : measureEntropy μ T = 0 := by
  apply le_antisymm
  · change (⨆ k : ℕ, ⨆ P : Y → Fin k,
      ⨆ (_hP : ∀ a, MeasurableSet {y | P y = a}),
        ENNReal.ofReal (observationEntropyRate μ T P)) ≤ (0 : ℝ≥0∞)
    simp only [iSup_le_iff]
    intro k P hP
    rw [observationEntropyRate_zero_of_ae_periodic μ hT n hn hperiod P
      (measurable_to_countable' hP), ENNReal.ofReal_zero]
  · exact bot_le

/-- Full diagonal ergodicity gives a zero-entropy/aperiodic dichotomy for
every fixed real-time diagonal map. -/
theorem diagonal_entropy_zero_or_aperiodic (d : ℕ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell t)) = 0 ∨
    (∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n →
      (fun y => rightAction y (diagonalOneParameter ell hell t))^[n] x ≠ x) := by
  rcases diagonal_periodicity_dichotomy d ell hell t μ with ⟨n, hn, hp⟩ | hap
  · left
    have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
      (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
    have hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell t)) μ μ := by
      refine ⟨(continuous_rightAction _).measurable, ?_⟩
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hA _
    exact measureEntropy_zero_of_ae_periodic μ hT n hn hp
  · exact Or.inr hap

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CanonicalRootBasic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean root coefficients and their elementary properties

The coefficient is the mean leaf information at unit scale. Diagonal
covariance makes real-time mean information linear in time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

lemma canonicalRootCoefficient_diagonal (i : Fin (d + 1)) :
    canonicalRootCoefficient d μ i i = 0 := by simp [canonicalRootCoefficient]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SparseUpperRootComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse fine returns remove the transverse part of a future lift -/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_conull_future1_root_relation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell (-1))) μ μ)
    (Q R : X n → ℕ)
    (hrel : ∀ᵐ x ∂μ, ∀ y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y)=
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
        R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y) :
    ∃ E : Set (X n), (∀ᵐ x ∂μ, x ∈ E) ∧
      ∀ x ∈ E, ∀ y ∈ E,
        (∀ k : ℕ,
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        (∀ k : ℕ,
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] y)=
          R ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
        ∃ u : UpperRootTime n, rightAction x ((completeRootChain n).word u)=y := by
  let a := diagonalOneParameter ell hell (-1)
  let T : X n → X n := fun x => rightAction x a
  have hs := hT.quasiMeasurePreserving.ae hrel
  refine ⟨{x | ∀ y,
    (∀ k : ℕ, Q (T^[k] y)=Q (T^[k] (T x))) →
    (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] (T x))) →
    ∃ u : UpperRootTime n, rightAction (T x) ((completeRootChain n).word u)=y},hs,?_⟩
  intro x hx y _hy hq hr
  obtain ⟨u,hu⟩ := hx (T y)
    (fun k => by simpa only [Function.iterate_succ_apply] using hq k)
    (fun k => by simpa only [Function.iterate_succ_apply] using hr (k+1))
  refine ⟨(completeRootChain n).rootDilation ell (-1) u,?_⟩
  apply (rightActionHomeomorph a).injective
  change rightAction (rightAction x _) a=rightAction y a
  calc
    _ = rightAction (rightAction x a) ((completeRootChain n).word u) := by
      rw [rightAction_mul,rightAction_mul,(completeRootChain n).word_rootDilation ell hell]
      congr 1
      dsimp only [a]
      rw [diagonalOneParameter_neg]
      group
    _ = _ := hu

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularRootEntropyActual
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual regular entropy upper bound

The aperiodic case uses small complete orbit sections and actual quotient
charts. The periodic case has zero entropy. Full diagonal ergodicity is
used only for that dichotomy, never as ergodicity of the selected map.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma measurableSet_aperiodic {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] {T : Y → Y} (hT : Continuous T) :
    MeasurableSet {x | ∀ k : ℕ, 0 < k → T^[k] x ≠ x} := by
  rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : 0 < k
  · simpa only [hk,true_implies,Function.id_def,compl_ofPred] using
      (isClosed_eq (hT.iterate k) continuous_id).measurableSet.compl
  · simpa only [hk,false_implies,ofPred_true] using (MeasurableSet.univ : MeasurableSet (univ : Set Y))

theorem negative_diagonal_entropy_le_root_sum (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal (∑ p : allPositiveRoots (d+1),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2) := by
  rcases diagonal_entropy_zero_or_aperiodic d ell hell (-1) μ with hz | hap
  · rw [hz]
    exact bot_le
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hord : StrictMono ell := by
    intro i j hij
    have hh := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
    have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp at hh
    linarith
  obtain ⟨B,r₀,H,Q,hB,hr₀,hr₀1,hH,hQ,_hheight,hinj,_hcompact,_hfiniteLevels,
      _hheightEntropy,hlift,hbound,hgood,_hstep,_hheightRefinement,hneutral,_hfactor,hbranch,_hcode⟩ :=
    exists_bounded_branching_subordinate_observation_with_lifts d ell hell hgap μ hA
      (by norm_num : (0:ℝ) < 1)
  apply negative_diagonal_entropy_le_root_sum_of_small_auxiliary d ell hell μ Q hQ
    hbound hgood hbranch
  · intro x y hy
    exact hneutral x y hy.1 hy.2
  intro ε hε
  let E : Set (X (d+1)) := {x | ∀ k : ℕ, 0 < k → T^[k] x ≠ x}
  have hE : MeasurableSet E := measurableSet_aperiodic (continuous_rightAction _)
  have hEfull : ∀ᵐ x ∂μ, x ∈ E := hap
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  have hr (m : ℕ) : 0 < r m := mul_pos hr₀ (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    apply le_trans _ hr₀1
    apply mul_le_of_le_one_right hr₀.le
    exact Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (α := ℝ) m)])
  have hanti : Antitone r := by
    intro i j hij
    apply mul_le_mul_of_nonneg_left _ hr₀.le
    apply Real.exp_le_exp.mpr
    have hc : (i:ℝ) ≤ j := Nat.cast_le.mpr hij
    exact mul_le_mul_of_nonpos_left hc (by linarith)
  obtain ⟨R,hR,hRs,hsmall,hcomparison⟩ := exists_sparse_upperRoot_comparison
    ell hell hord μ hT E hE (fun x hx => hx) H hH r hr hr1 hanti hinj Q hlift hε
  have hfull : ∀ᵐ x ∂μ, ∀ y,
      (∀ k : ℕ, Q (T^[k] y)=Q (T^[k] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) →
      ∃ u : UpperRootTime (d+1), rightAction x ((completeRootChain (d+1)).word u)=y := by
    filter_upwards [hEfull,hcomparison] with x hxE hx
    exact hx hxE
  obtain ⟨F,hF,hrelative⟩ := exists_conull_future1_root_relation ell hell μ hT Q R hfull
  exact ⟨R,hR,hRs,hsmall,F,hF,hrelative⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylRootBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing actual root boxes without changing the root parameter

A coordinate permutation carries the pivot, transverse slice, and quotient
root box to their permuted versions.  The real root coordinate is unchanged,
so disintegration transports the conditional measure without a rescaling.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma reindex_domain (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) :
    (reindex B e).domain = rootReindexCoordinates e i j k '' B.domain := by
  ext z
  constructor
  · rintro ⟨⟨s, hs, hse⟩, ht⟩
    exact ⟨(s, z.2), ⟨hs, ht⟩, Prod.ext hse rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z.1, hz.1, rfl⟩, hz.2⟩

theorem reindex_coordinateMeasure (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (μ : Measure (X n)) :
    (reindex B e).coordinateMeasure (μ.map (quotientReindex e)) =
      (B.coordinateMeasure μ).map (rootReindexCoordinates e i j k) := by
  let E := rootReindexCoordinates e i j k
  let Q := quotientReindexHomeomorph e
  ext S hS
  rw [PrimeDegreePackets.RootBox.coordinateMeasure_apply _ _ hS,
    Measure.map_apply E.measurable hS,
    PrimeDegreePackets.RootBox.coordinateMeasure_apply _ _ (E.measurable hS)]
  have he : rootQuotientParametrization (e.injective.ne hij) ''
        (S ∩ (reindex B e).domain) =
      Q '' (rootQuotientParametrization hij '' (E ⁻¹' S ∩ B.domain)) := by
    rw [reindex_domain]
    ext x
    constructor
    · rintro ⟨z, ⟨hzS, w, hw, rfl⟩, rfl⟩
      exact ⟨rootQuotientParametrization hij w, ⟨w, ⟨hzS, hw⟩, rfl⟩,
        (rootReindexCoordinates_param e hij w).symm⟩
    · rintro ⟨_, ⟨w, ⟨hwS, hw⟩, rfl⟩, rfl⟩
      exact ⟨E w, ⟨hwS, ⟨w, hw, rfl⟩⟩, rootReindexCoordinates_param e hij w⟩
  change (μ.map Q) (rootQuotientParametrization (e.injective.ne hij) ''
    (S ∩ (reindex B e).domain)) = _
  rw [he, Q.isOpenEmbedding.measurableEmbedding.map_apply, Q.injective.preimage_image]

theorem reindex_marginal (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (μ : Measure (X n)) :
    ((reindex B e).coordinateMeasure (μ.map (quotientReindex e))).fst =
      ((B.coordinateMeasure μ).fst).map (rootSliceReindexHomeomorph e i j k) := by
  rw [reindex_coordinateMeasure]
  exact fst_map_measurableEquiv (B.coordinateMeasure μ)
    (rootSliceReindexHomeomorph e i j k).toMeasurableEquiv
    (MeasurableEquiv.refl ℝ)

theorem reindex_conditionalKernel (B : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (reindex B e).conditionalKernel (μ.map (quotientReindex e))
        (rootSliceReindexHomeomorph e i j k s) = B.conditionalKernel μ s := by
  simp only [PrimeDegreePackets.RootBox.conditionalKernel, reindex_coordinateMeasure]
  have H := condKernel_map_measurableEquiv (B.coordinateMeasure μ)
    (rootSliceReindexHomeomorph e i j k).toMeasurableEquiv
    (MeasurableEquiv.refl ℝ)
  change ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
    ((B.coordinateMeasure μ).map (rootReindexCoordinates e i j k)).condKernel
      (rootSliceReindexHomeomorph e i j k s) =
        ((B.coordinateMeasure μ).condKernel s).map id at H
  simpa only [Measure.map_id] using H

end RootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_WeylRootLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical covariance of the intrinsic root leaves under permutations

The actual normalized leaf is identified in reindexed boxes by disintegration
on arbitrarily long root intervals.  The time coordinate and its unit ball
do not change, so the normalized measures themselves agree.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma ae_root_free_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n))
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ y ∂μ.map (quotientReindex e), ∀ t : ℝ,
      rightAction y (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t) = y →
        t = 0 := by
  let Q := (quotientReindexHomeomorph e).toMeasurableEquiv
  change ∀ᵐ y ∂μ.map Q, _
  rw [← Q.map_ae μ]
  change ∀ᵐ x ∂μ, ∀ t : ℝ,
    rightAction (Q x) (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t) =
      Q x → t = 0
  filter_upwards [hfree] with x hx
  intro t ht
  apply hx t
  apply Q.injective
  change quotientReindex e (rightAction x _) = quotientReindex e x
  rw [quotientReindex_rightAction, reindex_transvection]
  exact ht

namespace RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

theorem ae_leafMeasure_reindex (A : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (reindex A e).leafMeasure R (μ.map (quotientReindex e))
        (rootSliceReindexHomeomorph e i j k s) = A.leafMeasure R μ s := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let S := rootSliceReindexHomeomorph e i j k
  let nu := μ.map (quotientReindex e)
  have hfree' := ae_root_free_reindex e hij μ hfree
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
        (reindex B.val e).conditionalKernel nu (S s) = B.val.conditionalKernel μ s := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact PrimeDegreePackets.RootBox.base_ae_of_ae A B.val (hinc m B) μ
      (reindex_conditionalKernel B.val e μ)
  have htrans : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
        ((reindex A e).leafMeasure R nu (S s)).restrict B.val.time =
          (anchorNormalize ((reindex B.val e).conditionalKernel nu (S s))
            A.time).restrict B.val.time := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := (reindex A e).ae_leafMeasure_restrict R hAR nu hfree'
      (reindex B.val e) (hinc m B)
    rw [reindex_marginal A e μ] at H
    have H' := ae_of_ae_map S.measurable.aemeasurable H
    filter_upwards [H'] with s hs
    intro hsB
    exact (hs (mem_image_of_mem S hsB)).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree, hcov, htrans] with s hs hi hc ht
  apply measure_eq_of_restrictionChain (rootLeafWindow R) (rootLeafWindow_mono R)
    (rootLeafWindow_cover R)
  intro m
  obtain ⟨B, hBC, hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B, hBC⟩
  have he := ht m B' hsB
  rw [hc m B' hsB] at he
  change ((reindex A e).leafMeasure R nu (S s)).restrict B.time =
    (anchorNormalize (B.conditionalKernel μ s) A.time).restrict B.time at he
  rw [rootLongBoxFamily_time hij k R m B hBC] at he
  exact he.trans (hs.2.2.2 m B hBC hsB).symm

lemma ae_basedLeaf_reindex (A : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (reindex A e).basedLeaf R (μ.map (quotientReindex e))
        (rootReindexCoordinates e i j k z) = A.basedLeaf R μ z := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (ae_leafMeasure_reindex A e R hAR μ hfree)
  filter_upwards [H] with z hz
  change basedRealMeasure ((reindex A e).leafMeasure R (μ.map (quotientReindex e))
    (rootSliceReindexHomeomorph e i j k z.1)) z.2 = _
  rw [hz]
  rfl

lemma ae_intrinsicRootLeaf_reindex_restrict (A : PrimeDegreePackets.RootBox hij k)
    (e : Equiv.Perm (Fin n)) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ x ∂μ.restrict A.range,
      intrinsicRootLeaf (e.injective.ne hij) (μ.map (quotientReindex e))
        (quotientReindex e x) = intrinsicRootLeaf hij μ x := by
  apply A.ae_of_coordinate μ
  have HT := (reindex A e).ae_intrinsicRootLeaf_coordinates R hAR
    (μ.map (quotientReindex e)) (ae_root_free_reindex e hij μ hfree)
  rw [reindex_coordinateMeasure A e μ] at HT
  have HT' := ae_of_ae_map (rootReindexCoordinates e i j k).measurable.aemeasurable HT
  filter_upwards [HT', A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_reindex A e R hAR μ hfree] with z ht ha hc
  rw [rootReindexCoordinates_param] at ht
  exact ht.trans (hc.trans ha.symm)

end RootBox

/-- Numeric leaf covariance on the actual quotient, not just preservation
of the atomic/non-atomic alternative. -/
theorem ae_intrinsicRootLeaf_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf (e.injective.ne hij) (μ.map (quotientReindex e))
      (quotientReindex e x) = intrinsicRootLeaf hij μ x := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ)
    (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_reindex_restrict B.val.box e
      B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WeylRootInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual root information and coefficients under coordinate permutations

The reindexed measure is the pushforward on the arithmetic quotient.  The
preceding box-level transport proves covariance of the normalized intrinsic
leaves, so their small-ball logarithms and integrated coefficients agree.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_rootInformation_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ s : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij s) = x → s = 0)
    (t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation (e.injective.ne hij) (μ.map (quotientReindex e)) t
      (quotientReindex e x) = rootInformation hij μ t x := by
  filter_upwards [ae_intrinsicRootLeaf_reindex e hij μ hfree] with x hx
  simp only [rootInformation, hx]

theorem rootInformationMean_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ s : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij s) = x → s = 0)
    (t : ℝ) :
    rootInformationMean (e.injective.ne hij) (μ.map (quotientReindex e)) t =
      rootInformationMean hij μ t := by
  unfold rootInformationMean
  exact (lintegral_map_equiv
    (fun x => ENNReal.ofReal (rootInformation (e.injective.ne hij)
      (μ.map (quotientReindex e)) t x))
    (quotientReindexHomeomorph e).toMeasurableEquiv).trans
      (lintegral_congr_ae ((ae_rootInformation_reindex e hij μ hfree t).mono
        (fun _ hx => congrArg ENNReal.ofReal hx)))

/-- No entropy formula is used to permute the actual canonical root
coefficients; this follows by transporting their defining leaf integrals. -/
theorem canonicalRootCoefficient_reindex (d : ℕ) (e : Equiv.Perm (Fin (d + 1)))
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (i j : Fin (d + 1)) :
    canonicalRootCoefficient d (μ.map (quotientReindex e)) (e i) (e j) =
      canonicalRootCoefficient d μ i j := by
  haveI : IsProbabilityMeasure (μ.map (quotientReindex e)) :=
    Measure.isProbabilityMeasure_map (quotientReindexHomeomorph e).continuous.measurable.aemeasurable
  by_cases hij : i = j
  · subst j
    rw [canonicalRootCoefficient_diagonal, canonicalRootCoefficient_diagonal]
  have hfree : ∀ᵐ x ∂μ, ∀ s : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij s) = x → s = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono (fun x hx => hx i j hij)
  simp only [canonicalRootCoefficient, dite_eq_right hij, dite_eq_right (e.injective.ne hij)]
  rw [rootInformationMean_reindex e hij μ hfree]

/-- The complete finite root-information form is unchanged when both
the measure and the diagonal weights are reindexed. -/
theorem rootEntropyForm_canonical_reindex (d : ℕ)
    (e : Equiv.Perm (Fin (d + 1))) (μ : Measure (X (d + 1)))
    [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d + 1) → ℝ) :
    rootEntropyForm (canonicalRootCoefficient d (μ.map (quotientReindex e)))
        (fun i => ell (e.symm i)) =
      rootEntropyForm (canonicalRootCoefficient d μ) ell := by
  have hc (i j : Fin (d + 1)) :
      canonicalRootCoefficient d (μ.map (quotientReindex e)) i j =
        canonicalRootCoefficient d μ (e.symm i) (e.symm j) := by
    simpa only [e.apply_symm_apply] using
      canonicalRootCoefficient_reindex d e μ hA (e.symm i) (e.symm j)
  unfold rootEntropyForm
  apply Fintype.sum_equiv e.symm _ _
  intro i
  apply Fintype.sum_equiv e.symm _ _
  intro j
  rw [hc]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularEntropyTests
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularRootEntropySandwich
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regular entropy lower bounds and the upper-bound criterion

The expanding-root kernel gives one chamber's lower bound. Weyl
covariance transports it to the opposite chamber. The finite regular
upper estimates therefore imply the entropy identities and coefficient
balance required by prime-degree rigidity.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootEntropyForm_neg_of_monotone {n : ℕ}
    (w : Fin n → Fin n → ℝ) (ell : Fin n → ℝ) (hmono : Monotone ell) :
    rootEntropyForm w (fun i => -ell i) =
      ∑ p : allPositiveRoots n, (ell p.val.2 - ell p.val.1) * w p.val.1 p.val.2 := by
  classical
  rw [← Finset.sum_subtype (allPositiveRoots n) (by intro p; rfl)
    (fun p : Fin n × Fin n => (ell p.2 - ell p.1) * w p.1 p.2)]
  simp only [allPositiveRoots, Finset.sum_filter, Fintype.sum_prod_type, rootEntropyForm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · rw [ite_eq_left hij, neg_sub_neg, max_eq_left (sub_nonneg.mpr (hmono hij.le))]
    ring
  · rw [ite_eq_right hij, neg_sub_neg,
      max_eq_right (sub_nonpos.mpr (hmono (le_of_not_gt hij))), mul_zero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularEntropyDischarge
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite regular entropy identities and prime-degree rigidity

The negative-time upper bound uses the actual root-future construction.
Weyl reindexing supplies the positive-time upper bound with the actual
transported leaf coefficients. Together with the proved lower bounds,
these discharge the finite regular tests and the prime-degree EKL input.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

section Measure
variable {d : ℕ} (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]

/-- The actual negative-time entropy is bounded by its canonical root form. -/
theorem regular_entropy_le_root_form_neg
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (fun i => -ell i)) := by
  have hmono : Monotone ell := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · have h := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩⟩
      have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
      linarith
    · exact le_rfl
  rw [rootEntropyForm_neg_of_monotone _ ell hmono]
  exact negative_diagonal_entropy_le_root_sum d ell hell hgap μ

/-- Reverse the coordinate order and weights to obtain the positive-time
bound without assuming symmetry of opposite root coefficients. -/
theorem regular_entropy_le_root_form_pos
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell 1)) ≤
      ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) ell) := by
  let e : Equiv.Perm (Fin (d+1)) := Fin.revPerm
  let nu := μ.map (quotientReindex e)
  haveI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map (continuous_quotientReindex e).measurable.aemeasurable
  let ellR := fun i => -ell (e.symm i)
  have hsum : ∑ i, ellR i=0 := by
    simp only [ellR,Finset.sum_neg_distrib,Equiv.sum_comp,hell,neg_zero]
  have hgapR (p : allPositiveRoots (d+1)) :
      Real.log 4 ≤ ellR p.val.2-ellR p.val.1 := by
    have hrev : p.val.2.rev < p.val.1.rev :=
      Fin.rev_lt_rev.mpr (Finset.mem_filter.mp p.prop).2
    have h := hgap ⟨(p.val.2.rev,p.val.1.rev),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrev⟩⟩
    simpa only [ellR,e,Fin.revPerm_symm,Fin.revPerm_apply,neg_sub_neg] using h
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) nu :=
    diagonal_ergodic_reindex d e μ
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hform : rootEntropyForm (canonicalRootCoefficient d nu) (fun i => -ellR i) =
      rootEntropyForm (canonicalRootCoefficient d μ) ell := by
    simp only [ellR,neg_neg]
    exact rootEntropyForm_canonical_reindex d e μ hA ell
  have he : diagonalOneParameter ellR hsum (-1) =
      diagonalOneParameter (fun i => ell (e.symm i)) (permutedWeight_sum e ell hell) 1 := by
    simpa only [ellR,neg_neg] using
      diagonalOneParameter_neg_weights (fun i => ell (e.symm i))
        (permutedWeight_sum e ell hell) (-1)
  have hb := regular_entropy_le_root_form_neg nu ellR hsum hgapR
  rw [hform,he] at hb
  exact (diagonal_entropy_reindex d e μ ell hell 1).symm.trans_le hb

/-- Both finite families of regular upper bounds hold without
additional entropy or leaf-measure hypotheses. -/
theorem canonicalRegularEntropyUpperBounds_proved : CanonicalRegularEntropyUpperBounds d μ := by
  intro a
  have hg (p : allPositiveRoots (d+1)) :
      Real.log 4 ≤ regularEntropyTest d a p.val.2-regularEntropyTest d a p.val.1 :=
    regularEntropyTest_gap d a (Finset.mem_filter.mp p.prop).2
  exact ⟨regular_entropy_le_root_form_pos μ _ _ hg,
    regular_entropy_le_root_form_neg μ _ _ hg⟩

end Measure

/-- The published rigidity specialization required by the packet proof,
with all its mathematical input proved for this application. -/
theorem eklPrimeInput_unconditional_oai (d : ℕ) : EKLPrimeInput d := by
  apply eklPrimeInput_of_regular_entropy_upper_bounds d
  intro μ hμ hμerg
  let : IsProbabilityMeasure μ := hμ
  let : ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ := hμerg
  exact canonicalRegularEntropyUpperBounds_proved μ

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.eklPrimeInput_unconditional_oai := @OAI.DukePrimeDegree.eklPrimeInput_unconditional_oai
