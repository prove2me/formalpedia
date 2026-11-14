-- Prove2me | solution 1 for OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:54.645204+00:00
-- url     : https://prove2.me/submissions/ae64625d-0c4b-4531-9fc9-1f2b953c8cc5

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
import Theorems.Thm_OAI_DukePrimeDegree_countable_patch_name_entropy_sublinear
import Theorems.Thm_OAI_DukePrimeDegree_exists_atomic_neutral_future_cover
import Theorems.Thm_OAI_DukePrimeDegree_exists_small_future_observation
import Theorems.Thm_OAI_DukePrimeDegree_measureEntropy_le_of_bilateral_heightClip_bounds

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientMeasurableSection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable section of the actual arithmetic quotient

Local inverse charts and a countable disjoint cover give the section. It
is used to lift an arbitrary quotient measure before taking neutral leaf
coordinates; no absolute continuity with respect to Haar is required.
-/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_measurable_quotient_section (n : ℕ) :
    ∃ s : X n → G n, Measurable s ∧
      ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x := by
  classical
  let q : G n → X n := Quotient.mk (QuotientGroup.rightRel (integralGroup n))
  have hq := (quotient_covering n).isLocalHomeomorph
  choose e he hqe using hq
  have hcover : (⋃ g : G n, (e g).target)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨g,rfl⟩ := Quotient.mk_surjective x
    apply mem_iUnion.mpr
    refine ⟨g,?_⟩
    have h := (e g).map_source (he g)
    rwa [←hqe g] at h
  obtain ⟨S,hSuniv,hSc,hS⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => (e g).target) (fun g _ => (e g).open_target)
  obtain ⟨a,ha⟩ := Set.countable_iff_exists_subset_range.mp hSc
  have hSall : (⋃ g ∈ S, (e g).target)=univ := hS.trans (by simpa using hcover)
  let U : ℕ → Set (X n) := fun i => (e (a i)).target
  have hU : (⋃ i, U i)=univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ g ∈ S, (e g).target := by
      rw [hSall]
      trivial
    obtain ⟨g,hg,hxg⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,rfl⟩ := ha hg
    exact mem_iUnion.mpr ⟨i,hxg⟩
  let D : ℕ → Set (X n) := disjointed U
  have hD (i : ℕ) : MeasurableSet (D i) :=
    MeasurableSet.disjointed (fun j => (e (a j)).open_target.measurableSet) i
  let f : ℕ → X n → G n := fun i => (U i).piecewise (e (a i)).symm (fun _ => 1)
  have hf (i : ℕ) : Measurable (f i) :=
    (e (a i)).continuousOn_invFun.measurable_piecewise continuous_const.continuousOn
      (e (a i)).open_target.measurableSet
  obtain ⟨s,hs,hsi⟩ := exists_measurable_piecewise D hD f hf (by
    intro i j hij x hx
    exact ((Set.disjoint_left.mp ((disjoint_disjointed U) hij)) hx.1 hx.2).elim)
  refine ⟨s,hs,?_⟩
  intro x
  have hx : x ∈ ⋃ i, D i := by rw [iUnion_disjointed,hU]; trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hui : x ∈ U i := disjointed_subset U i hi
  rw [hsi i hi]
  change q ((U i).piecewise (e (a i)).symm (fun _ => 1) x)=x
  rw [piecewise_eq_of_mem _ _ _ hui]
  dsimp only [q]
  rw [hqe (a i)]
  exact (e (a i)).right_inv hui

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalShannon
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_FiniteGeneratingObservations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralConditionalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorSymbols
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

theorem exists_finite_predecessor_observation {Y : Type*} [MeasurableSpace Y]
    (T : Y → Y) (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (hfinite : UniformFinitePredecessors T Q) :
    ∃ (M : ℕ) (B : Y → Fin (M+1)) (decode : ℕ → Fin (M+1) → ℕ),
      Measurable B ∧
      (∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y) ∧
      ∀ x, decode (Q (T x)) (B x)=Q x := by
  classical
  obtain ⟨M,hM⟩ := hfinite
  choose F hF hcard using hM
  let code : ℕ × ℕ → Fin (M+1) := fun p =>
    if hv : p.2 ∈ F p.1 then
      ⟨((F p.1).equivFin ⟨p.2,hv⟩).val,
        lt_of_lt_of_le ((F p.1).equivFin ⟨p.2,hv⟩).isLt
          (Nat.le_succ_of_le (hcard p.1))⟩
    else 0
  let decode : ℕ → Fin (M+1) → ℕ := fun q b =>
    if hb : b.val < (F q).card then
      ((F q).equivFin.symm ⟨b.val,hb⟩).val
    else 0
  let B : Y → Fin (M+1) := fun x => code (Q (T x),Q x)
  refine ⟨M,B,decode,?_,?_,?_⟩
  · exact (measurable_of_countable code).comp ((hQ.comp hT).prodMk hQ)
  · intro x y hxy hTxy
    dsimp only [B]
    rw [hxy,hTxy]
  · intro x
    have hx : Q x ∈ F (Q (T x)) := hF (Q (T x)) ⟨x,rfl,rfl⟩
    have hb : ((F (Q (T x))).equivFin ⟨Q x,hx⟩).val < (F (Q (T x))).card :=
      ((F (Q (T x))).equivFin ⟨Q x,hx⟩).isLt
    dsimp only [B,code]
    rw [dite_eq_left hx]
    dsimp only [decode]
    rw [dite_eq_left hb]
    exact congrArg Subtype.val ((F (Q (T x))).equivFin.symm_apply_apply ⟨Q x,hx⟩)

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

theorem predecessor_clippedWord_conditionalEntropy_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Y → Y) (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin M) (hB : Measurable B)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N L : ℕ) :
    conditionalSigmaEntropy μ (orbitName T (heightClip Q L) N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) ≤
      conditionalSigmaEntropy μ (orbitName T B N)
        (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) := by
  have hPN : Measurable (orbitName T (heightClip Q L) N) :=
    measurable_pi_iff.mpr fun i => (heightClip_measurable hQ L).comp (hT.iterate i.val)
  have hBN : Measurable (orbitName T B N) :=
    measurable_pi_iff.mpr fun i => hB.comp (hT.iterate i.val)
  apply conditionalSigmaEntropy_le_of_fiber_refinement μ (Q ∘ T^[N])
    (hQ.comp (hT.iterate N)) _ hPN _ hBN
  intro x y hterm hword
  have heq := predecessor_word_recovers T Q B decode hdecode hterm
    (fun k hk => congrFun hword ⟨k,hk⟩)
  funext i
  change heightClip Q L (T^[i.val] x)=heightClip Q L (T^[i.val] y)
  apply Fin.ext
  change min (Q (T^[i.val] x)) L=min (Q (T^[i.val] y)) L
  rw [heq i.val i.isLt.le]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureLabelBlocks
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableObservationInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_IncreasingConditioningChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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

theorem conditionalSigmaEntropy_comp_preserving_iSup_nat
    {Y α : Type*} [mY : MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (F : ℕ → Y → ℕ) (hF : ∀ N, Measurable (F N))
    (hmono : Monotone (fun N => observationSigma (F N)))
    (hmonoT : Monotone (fun N => observationSigma (F N ∘ T))) :
    conditionalSigmaEntropy (mY := mY) μ (P ∘ T)
        (⨆ N, observationSigma (F N ∘ T)) =
      conditionalSigmaEntropy (mY := mY) μ P (⨆ N, observationSigma (F N)) := by
  have h₁ := conditionalSigmaEntropy_tendsto_iSup μ (P ∘ T) _ hmonoT
    (fun N => ((hF N).comp hT.measurable).comap_le)
  have h₂ := conditionalSigmaEntropy_tendsto_iSup μ P _ hmono
    (fun N => (hF N).comap_le)
  apply tendsto_nhds_unique h₁
  apply h₂.congr
  intro N
  exact (conditionalSigmaEntropy_comp_preserving_nat μ hT P hP (F N) (hF N)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

lemma observationSigma_comp {Y Z α : Type*} (P : Y → α) (S : Z → Y) :
    observationSigma (P ∘ S)=MeasurableSpace.comap S (observationSigma P) := by
  unfold observationSigma
  exact MeasurableSpace.comap_comp.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorWholeFutureSigma
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One predecessor restores exactly one level of the whole future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma fullFutureSigma_one {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    fullFutureSigma T Q 1=
      MeasurableSpace.comap (entireFutureObservation T Q) inferInstance := by
  simpa only [fullFutureSigma,Nat.add_comm] using countableFutureSigma_eq_comap T Q

lemma fullFutureSigma_comap {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r s : ℕ) :
    MeasurableSpace.comap (T^[r]) (fullFutureSigma T Q s)=fullFutureSigma T Q (r+s) := by
  unfold fullFutureSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_congr
  intro k
  rw [←observationSigma_comp]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [←Function.iterate_add_apply]
  rw [show s+k+r=r+s+k by omega]

lemma fullFutureSigma_zero {Y : Type*} (T : Y → Y) (Q : Y → ℕ) :
    fullFutureSigma T Q 0=observationSigma Q ⊔ fullFutureSigma T Q 1 := by
  have H := (sup_iSup_nat_succ (fun k : ℕ => observationSigma (fun x => Q (T^[k] x)))).symm
  simpa only [fullFutureSigma,Nat.zero_add,Nat.add_zero,Function.iterate_zero_apply,
    Nat.add_comm] using H

lemma futureLabelBlock_shift_generate {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    (⨆ N, observationSigma (futureLabelBlock T Q N ∘ T^[r]))=
      fullFutureSigma T Q (r+1) := by
  simp_rw [observationSigma_comp]
  rw [←MeasurableSpace.comap_iSup,futureLabelBlock_sigma_generate,
    countableFutureSigma_eq_comap,←fullFutureSigma_one,fullFutureSigma_comap]

lemma futureLabelBlock_shift_monotone {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    Monotone (fun N => observationSigma (futureLabelBlock T Q N ∘ T^[r])) := by
  intro i j hij
  simp only [observationSigma_comp]
  exact MeasurableSpace.comap_mono (futureLabelBlock_sigma_monotone T Q hij)

theorem conditionalSigmaEntropy_chain_fullFuture
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (R : Y → β) (hR : ∀ b, MeasurableSet {y | R y=b}) (r : ℕ) :
    conditionalSigmaEntropy μ (fun y => (P y,R y)) (fullFutureSigma T Q (r+1)) =
      conditionalSigmaEntropy μ P (fullFutureSigma T Q (r+1)) +
        conditionalSigmaEntropy μ R (fullFutureSigma T Q (r+1) ⊔ observationSigma P) := by
  have H := conditionalSigmaEntropy_chain_iSup_nat μ P hP R hR
    (fun N => futureLabelBlock T Q N ∘ T^[r])
    (fun N => (futureLabelBlock_measurable hT hQ N).comp (hT.iterate r))
    (futureLabelBlock_shift_monotone T Q r)
  simpa only [futureLabelBlock_shift_generate] using H

theorem conditionalSigmaEntropy_comp_preserving_fullFuture
    {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (Q : Y → ℕ) (hQ : Measurable Q)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) (r : ℕ) :
    conditionalSigmaEntropy μ (P ∘ T^[r]) (fullFutureSigma T Q (r+1)) =
      conditionalSigmaEntropy μ P (fullFutureSigma T Q 1) := by
  have H := conditionalSigmaEntropy_comp_preserving_iSup_nat μ (hT.iterate r) P hP
    (futureLabelBlock T Q) (futureLabelBlock_measurable hT.measurable hQ)
    (futureLabelBlock_sigma_monotone T Q) (futureLabelBlock_shift_monotone T Q r)
  simpa only [futureLabelBlock_shift_generate,futureLabelBlock_sigma_generate,
    countableFutureSigma_eq_comap,←fullFutureSigma_one] using H

theorem fullFutureSigma_predecessor {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x) :
    fullFutureSigma T Q 0=fullFutureSigma T Q 1 ⊔ observationSigma B := by
  have ht : observationSigma (Q ∘ T) ≤ fullFutureSigma T Q 1 := by
    simpa only [Function.comp_def,Nat.add_zero,Function.iterate_one] using
      (le_iSup (fun k : ℕ => observationSigma (fun x => Q (T^[1+k] x))) 0)
  have hb : observationSigma B ≤ observationSigma Q ⊔ observationSigma (Q ∘ T) := by
    rw [←observationSigma_pair_eq]
    apply observationSigma_le_of_fiber_refinement
    intro x y hxy
    exact href x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hq : observationSigma Q ≤ observationSigma B ⊔ observationSigma (Q ∘ T) := by
    rw [←observationSigma_pair_eq]
    apply observationSigma_le_of_fiber_refinement
    intro x y hxy
    have hb : B x=B y := congrArg Prod.fst hxy
    have hq : Q (T x)=Q (T y) := congrArg Prod.snd hxy
    rw [←hdecode x,←hdecode y,hb,hq]
  rw [fullFutureSigma_zero]
  exact sup_le
    (hq.trans (sup_le le_sup_right (ht.trans le_sup_left))) le_sup_left |>.antisymm
      (sup_le le_sup_right (hb.trans (sup_le le_sup_left (ht.trans le_sup_right))))

theorem fullFutureSigma_predecessor_at {Y : Type*} {M : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (B : Y → Fin M)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (r : ℕ) :
    fullFutureSigma T Q r=
      fullFutureSigma T Q (r+1) ⊔ observationSigma (B ∘ T^[r]) := by
  have H := congrArg (MeasurableSpace.comap (T^[r]))
    (fullFutureSigma_predecessor T Q B href decode hdecode)
  simpa only [MeasurableSpace.comap_sup,fullFutureSigma_comap,Nat.add_zero,
    ←observationSigma_comp] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorWholeFutureEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact predecessor-word entropy conditioned on the whole terminal future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma fullFutureObservation_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) (r : ℕ) :
    Measurable (fullFutureObservation T Q r) :=
  measurable_pi_iff.mpr fun k => hQ.comp (hT.iterate (r+k))

lemma fullFutureSigma_eq_comap {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    fullFutureSigma T Q r=
      MeasurableSpace.comap (fullFutureObservation T Q r) inferInstance :=
  (MeasurableSpace.comap_process_pi (fun k y => Q (T^[r+k] y))).symm

lemma orbitName_eq_iff_last_initial {Y α : Type*} (T : Y → Y) (B : Y → α)
    (N : ℕ) (x y : Y) :
    orbitName T B (N+1) x=orbitName T B (N+1) y ↔
      B (T^[N] x)=B (T^[N] y) ∧ orbitName T B N x=orbitName T B N y := by
  constructor
  · intro h
    exact ⟨congrFun h (Fin.last N),funext fun i => congrFun h i.castSucc⟩
  · rintro ⟨hl,hw⟩
    funext i
    by_cases hi : i.val<N
    · exact congrFun hw ⟨i.val,hi⟩
    · have he : i.val=N := by omega
      change B (T^[i.val] x)=B (T^[i.val] y)
      simpa only [he] using hl

theorem predecessor_word_wholeFuture_increment
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B (N+1)) (fullFutureSigma T Q (N+1)) =
      conditionalSigmaEntropy μ B (fullFutureSigma T Q 1) +
        conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) := by
  let P := B ∘ T^[N]
  let W := orbitName T B N
  have hP : Measurable P := hB.comp (hT.measurable.iterate N)
  have hW : Measurable W := measurable_pi_iff.mpr fun i =>
    hB.comp (hT.measurable.iterate i.val)
  have hV : Measurable (orbitName T B (N+1)) := measurable_pi_iff.mpr fun i =>
    hB.comp (hT.measurable.iterate i.val)
  have he : conditionalSigmaEntropy μ (orbitName T B (N+1))
        (fullFutureSigma T Q (N+1)) =
      conditionalSigmaEntropy μ (fun y => (P y,W y))
        (fullFutureSigma T Q (N+1)) := by
    rw [fullFutureSigma_eq_comap]
    have hF := fullFutureObservation_measurable hT.measurable hQ (N+1)
    apply le_antisymm
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ _ hF _ hV _ (hP.prodMk hW)
      intro x y _ hxy
      exact (orbitName_eq_iff_last_initial T B N x y).mpr (Prod.mk.inj hxy)
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ _ hF _ (hP.prodMk hW) _ hV
      intro x y _ hxy
      exact Prod.ext
        ((orbitName_eq_iff_last_initial T B N x y).mp hxy).1
        ((orbitName_eq_iff_last_initial T B N x y).mp hxy).2
  rw [he,conditionalSigmaEntropy_chain_fullFuture μ hT.measurable Q hQ P
    (fun b => hP (measurableSet_singleton b)) W
    (fun w => hW (measurableSet_singleton w)) N]
  rw [conditionalSigmaEntropy_comp_preserving_fullFuture μ hT Q hQ B
    (fun b => hB (measurableSet_singleton b)) N,
    ←fullFutureSigma_predecessor_at T Q B href decode hdecode N]

theorem predecessor_word_wholeFuture_entropy
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) =
      (N : ℝ)*conditionalSigmaEntropy μ B (fullFutureSigma T Q 1) := by
  induction N with
  | zero =>
      rw [fullFutureSigma_eq_comap,conditionalSigmaEntropy_comap_eq_integral μ _
        (fullFutureObservation_measurable hT.measurable hQ 0) _
        (orbitName_measurable_fiber hT.measurable
          (fun b => hB (measurableSet_singleton b)) 0)]
      simp only [observationEntropy_unique,integral_zero,Nat.cast_zero,zero_mul]
  | succ N ih =>
      rw [predecessor_word_wholeFuture_increment μ hT Q hQ B hB href decode hdecode N,ih]
      push_cast
      ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PredecessorEntropySum
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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

theorem predecessor_clipped_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (L : ℕ) :
    observationEntropyRate μ T (heightClip Q L) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  apply le_of_tendsto_of_tendsto
    (conditional_boundary_entropy_rate μ hT (heightClip Q L)
      (fun a => heightClip_measurable hQ L (measurableSet_singleton a)) Q hQ)
    (predecessor_word_conditional_rate μ hT Q hQ B hB href decode hdecode)
  apply Filter.Eventually.of_forall
  intro N
  exact div_le_div_of_nonneg_right
    (predecessor_clippedWord_conditionalEntropy_le μ T hT.measurable Q hQ B hB decode hdecode N L)
    (Nat.cast_nonneg N)

theorem finite_predecessors_entropy_upper
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q) (hfinite : UniformFinitePredecessors T Q) :
    ∃ (M : ℕ) (B : Y → Fin (M+1)) (decode : ℕ → Fin (M+1) → ℕ),
      Measurable B ∧
      (∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y) ∧
      (∀ x, decode (Q (T x)) (B x)=Q x) ∧
      ∀ L : ℕ, observationEntropyRate μ T (heightClip Q L) ≤
        conditionalSigmaEntropy μ B
          (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) := by
  obtain ⟨M,B,decode,hB,href,hdecode⟩ :=
    exists_finite_predecessor_observation T hT.measurable Q hQ hfinite
  exact ⟨M,B,decode,hB,href,hdecode,
    predecessor_clipped_entropyRate_le μ hT Q hQ B hB href decode hdecode⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureEntropyCriterion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear terminal-future name bounds force zero predecessor information -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_information_zero_of_sublinear_words
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) ≤ C+N*ε) :
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance)=0 := by
  let I := conditionalSigmaEntropy μ B (fullFutureSigma T Q 1)
  have hI : 0 ≤ I := by
    rw [show I=conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) from
      congrArg (conditionalSigmaEntropy μ B) (fullFutureSigma_one T Q)]
    exact conditionalSigmaEntropy_comap_nonneg μ _
      (entireFutureObservation_measurable hT.measurable hQ) B
      (fun b => hB (measurableSet_singleton b))
  have hupper (ε : ℝ) (hε : 0 < ε) : I ≤ ε := by
    obtain ⟨C,hC⟩ := hsub ε hε
    have hlim : Tendsto (fun N : ℕ => C/(N : ℝ)+ε) atTop (𝓝 ε) := by
      simpa only [zero_add] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const ε
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hc := hC N
    rw [predecessor_word_wholeFuture_entropy μ hT Q hQ B hB href decode hdecode N] at hc
    change (N : ℝ)*I ≤ C+N*ε at hc
    calc
      I ≤ (C+N*ε)/N := (le_div_iff₀ hn).mpr (by nlinarith)
      _ = C/N+ε := by rw [add_div,mul_div_cancel_left₀ _ hn.ne']
  have hz : I=0 := by
    apply le_antisymm _ hI
    by_contra hn
    have hp : 0 < I := lt_of_not_ge hn
    have H := hupper (I/2) (by positivity)
    linarith
  simpa only [I,fullFutureSigma_one] using hz

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_AtomicRootEntropyZero
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Atomic expanding roots force zero metric entropy -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_entropy_zero_of_atomic_positive_roots_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hatom : ∀ p : ↥(allPositiveRoots (d+1) \ ∅), ∀ᵐ x ∂μ,
      intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x =
        Measure.dirac 0) :
    measureEntropy μ (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=0 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hA' (v : transverseNeutralSpace (d+1)) :
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ := by
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hord : StrictMono ell := by
    intro i j hij
    have hh := hgap ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
    have hp : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp at hh
    linarith
  obtain ⟨H,Q,r,hH,hQ,hanti,hr,hinj,hbranch,hlift,hbilateral⟩ :=
    exists_small_future_observation d ell hell hgap μ hA
  obtain ⟨s,hsm,hs⟩ := exists_measurable_quotient_section (d+1)
  let K₀ : PositiveCompacts (transverseNeutralSpace (d+1)) := Classical.arbitrary _
  let η := Measure.addHaarMeasure K₀
  let z₀ : NeutralCoordinateBase (d+1) × transverseNeutralSpace (d+1) :=
    ((⟨upperRootIdentity (d+1),by intro i; simp [upperRootIdentity]⟩,
      (completeRootChain (d+1)).zeroTime),0)
  obtain ⟨E,hE,hfull,hpair⟩ := exists_atomic_neutral_future_cover d ell hell hord Q H hH
    r hanti hr hinj hlift μ s hsm hs hA' η K₀ K₀.isCompact Measure.addHaarMeasure_self
    z₀ hatom
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp only [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨M,B,decode,hB,href,hdecode,hupper⟩ :=
    finite_predecessors_entropy_upper μ hT Q hQ hbranch
  have hzero := predecessor_information_zero_of_sublinear_words μ hT Q hQ B hB href
    decode hdecode (fun ε hε =>
      countable_patch_name_entropy_sublinear ell hell Q hQ E hE hpair μ hfull hT B hB hε)
  apply le_antisymm _ bot_le
  have hbound := measureEntropy_le_of_bilateral_heightClip_bounds d ell hell Q hQ μ hA
    (fun x y hxy => hbilateral x y hxy.1 hxy.2) 0
    (fun L => by simpa only [hzero] using hupper L)
  simpa only [ENNReal.ofReal_zero,bot_eq_zero] using hbound

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots_oai := @OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots_oai
