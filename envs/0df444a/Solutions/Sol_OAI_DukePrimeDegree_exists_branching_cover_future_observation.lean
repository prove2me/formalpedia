-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_branching_cover_future_observation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:48:06.050364+00:00
-- url     : https://prove2.me/submissions/0a9f7c00-d5fb-43c8-b8c0-1c2ae406d07f

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
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_exists_separated_exponential_cut_family

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets



theorem cube_grid_cover (d : ℕ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset (Fin d → ℝ),
      (∀ u ∈ s, ∀ i, |u i| ≤ R+1) ∧
      (s.card : ℝ) ≤ (2*R+2)^d / r^d ∧
      ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ R) →
        ∃ u ∈ s, ∀ i, |x i-u i| < r := by
  classical
  let N : ℕ := ⌈2*R/r⌉₊
  let g (k : Fin d → Fin (N+1)) : Fin d → ℝ := fun i => -R + (k i : ℕ)*r
  let s : Finset (Fin d → ℝ) := Finset.univ.image g
  have hN : (N:ℝ) < 2*R/r+1 := by
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) hr.le)
  have hNr : (N:ℝ)*r < 2*R+r := by
    have := (mul_lt_mul_iff_left₀ hr).mpr hN
    field_simp at this
    nlinarith
  refine ⟨s, ?_, ?_, ?_⟩
  · intro u hu i
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
    dsimp [g]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (k i).val) hr.le]
    · have hki : ((k i).val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (k i).isLt)
      nlinarith [mul_le_mul_of_nonneg_right hki hr.le]
  · have hcard : s.card ≤ (N+1)^d := by
      calc
        _ ≤ (Finset.univ : Finset (Fin d → Fin (N+1))).card := Finset.card_image_le
        _ = _ := by simp
    have hN1 : ((N+1:ℕ):ℝ) ≤ (2*R+2)/r := by
      apply (le_div_iff₀ hr).mpr
      push_cast
      nlinarith
    calc
      (s.card:ℝ) ≤ (((N+1)^d:ℕ):ℝ) := Nat.cast_le.mpr hcard
      _ = (((N+1:ℕ):ℝ))^d := Nat.cast_pow _ _
      _ ≤ ((2*R+2)/r)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hN1 d
      _ = _ := div_pow _ _ _
  · intro x hx
    have hx0 (i : Fin d) : 0 ≤ (x i+R)/r := by
      apply div_nonneg _ hr.le
      have := (abs_le.mp (hx i)).1
      linarith
    let k (i : Fin d) : Fin (N+1) := ⟨⌊(x i+R)/r⌋₊, by
      apply Nat.lt_succ_of_le
      apply (Nat.floor_mono ?_).trans (Nat.floor_le_ceil _)
      apply div_le_div_of_nonneg_right _ hr.le
      have := (abs_le.mp (hx i)).2
      linarith⟩
    refine ⟨g k, Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
    intro i
    have hlo := Nat.floor_le (hx0 i)
    have hhi := Nat.lt_floor_add_one ((x i+R)/r)
    have Hlo : (⌊(x i+R)/r⌋₊ : ℝ)*r ≤ x i+R := (le_div_iff₀ hr).mp hlo
    have Hhi : x i+R < ((⌊(x i+R)/r⌋₊ : ℝ)+1)*r := (div_lt_iff₀ hr).mp hhi
    dsimp [g,k]
    rw [abs_of_nonneg (by linarith)]
    linarith

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets

lemma visitCount_cast {Y : Type*} (T : Y → Y) (B : Set Y) (N : ℕ) (x : Y) :
    (visitCount T B N x : ℝ) = ∑ j ∈ Finset.range N, B.indicator (fun _ => (1:ℝ)) (T^[j] x) := by
  classical
  rw [visitCount,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : T^[j] x ∈ B <;> simp [hx]

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
namespace PrimeDegreePackets

lemma matrixBall_mono {n : ℕ} {r s : ℝ} (hrs : r ≤ s) :
    matrixBall n r ⊆ matrixBall n s := by
  intro g hg i j
  exact (hg i j).trans_le hrs



lemma left_div_entry_bound {n : ℕ} (g h : G n) {C b : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ i j, |g⁻¹.1 i j| ≤ C)
    (hgh : ∀ i j, |h.1 i j-g.1 i j| ≤ b) :
    ∀ i j, |(g⁻¹*h).1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ n*C*b := by
  intro i j
  have heq : (g⁻¹*h).1 - (1 : Matrix (Fin n) (Fin n) ℝ) = g⁻¹.1*(h.1-g.1) := by
    rw [Matrix.mul_sub]
    simp only [← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
  change |((g⁻¹*h).1-(1 : Matrix (Fin n) (Fin n) ℝ)) i j| ≤ _
  rw [heq,Matrix.mul_apply]
  calc
    |∑ k, g⁻¹.1 i k*(h.1-g.1) k j| ≤ ∑ k, |g⁻¹.1 i k*(h.1-g.1) k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, C*b := Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hg i k) (hgh k j) (abs_nonneg _) hC
    _ = n*C*b := by simp <;> ring



end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite maximal ergodic inequality

The maximal recurrence estimate used in EKL (2006), Section 4.3, follows
from this elementary finite Hopf inequality. The running maximum is built
recursively, so its integrability and its coboundary bound require no
pointwise ergodic theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

lemma positiveRunningSum_nonneg {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : 0 ≤ positiveRunningSum T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma positiveRunningSum_mono {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (x : Y) : Monotone (fun n => positiveRunningSum T f n x) := by
  suffices h : ∀ n x, positiveRunningSum T f n x ≤ positiveRunningSum T f (n + 1) x
    from monotone_nat_of_le_succ (fun n => h n x)
  intro n
  induction n with
  | zero => exact fun x => positiveRunningSum_nonneg T f 1 x
  | succ n ih =>
    intro x
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma birkhoffSum_le_positiveRunningSum {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : birkhoffSum T f n x ≤ positiveRunningSum T f n x := by
  induction n generalizing x with
  | zero => simp [positiveRunningSum]
  | succ n ih =>
    rw [birkhoffSum_succ']
    exact (add_le_add le_rfl (ih (T x))).trans (le_max_right _ _)

lemma measurable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} {f : Y → ℝ} (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (positiveRunningSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma integrable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (positiveRunningSum T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
    exact (integrable_zero _ _ _).sup (hf.add (hT.integrable_comp_of_integrable ih))

/-- A finite running maximum has nonnegative signed mass on its positive set. -/
theorem finite_hopf_maximal {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (hfmeas : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < positiveRunningSum T f n x}, f x ∂μ := by
  let m := positiveRunningSum T f n
  let E := {x | 0 < m x}
  have hm : Integrable m μ := integrable_positiveRunningSum hT hf n
  have hmmeas : Measurable m := measurable_positiveRunningSum hT.measurable hfmeas n
  have hE : MeasurableSet E := measurableSet_lt measurable_const hmmeas
  have hpoint (x : Y) : m x - m (T x) ≤ E.indicator f x := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      have hle := positiveRunningSum_mono T f x (Nat.le_succ n)
      change m x ≤ max 0 (f x + m (T x)) at hle
      have hpos : 0 < m x := hx
      have hle' := (le_max_iff.mp hle).resolve_left (not_le_of_gt hpos)
      linarith
    · rw [indicator_of_notMem hx]
      have hz : m x = 0 := le_antisymm (le_of_not_gt hx)
        (positiveRunningSum_nonneg T f n x)
      rw [hz]
      linarith [positiveRunningSum_nonneg T f n (T x)]
  have hcomp : ∫ x, m (T x) ∂μ = ∫ x, m x ∂μ := by
    have hmap : AEStronglyMeasurable m (μ.map T) := by
      simpa only [hT.map_eq] using hm.aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hmap).symm.trans
      (by rw [hT.map_eq])
  have hle := integral_mono (hm.sub (hT.integrable_comp_of_integrable hm))
    (hf.indicator hE) hpoint
  simp only [Pi.sub_apply, Function.comp_apply] at hle
  have hmt : Integrable (fun x => m (T x)) μ := hT.integrable_comp_of_integrable hm
  rw [integral_sub hm hmt, hcomp, sub_self,
    integral_indicator hE] at hle
  exact hle

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MaximalOccupation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of visits to decreasing exceptional sets

The finite Hopf inequality bounds the probability of ever having an
excessive occupation average. Applied to decreasing null-intersection
sets, it gives almost-sure uniform control over every time interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma visitCount_mono {Y : Type*} (T : Y → Y) {A B : Set Y}
    (hAB : A ⊆ B) (n : ℕ) (x : Y) : visitCount T A n x ≤ visitCount T B n x := by
  classical
  unfold visitCount
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,hAB (Finset.mem_filter.mp hj).2⟩

theorem excessiveOccupation_measure_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {A : Set Y} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal δ * μ (excessiveOccupation T A δ) ≤ μ A := by
  let u : Y → ℝ := A.indicator (fun _ => 1)
  let f : Y → ℝ := fun x => u x-δ
  have hui : Integrable u μ := (integrable_const (1:ℝ)).indicator hA
  have hum : Measurable u := measurable_const.indicator hA
  have hfi : Integrable f μ := hui.sub (integrable_const δ)
  have hfm : Measurable f := hum.sub measurable_const
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hEm n : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfm n)
  have hmono : Monotone E := fun i j hij x hx =>
    hx.trans_le (positiveRunningSum_mono T f x hij)
  have hEn n : ENNReal.ofReal δ * μ (E n) ≤ μ A := by
    have h0 := finite_hopf_maximal hT hfi hfm n
    change 0 ≤ ∫ x in E n, u x-δ ∂μ at h0
    rw [integral_sub hui.integrableOn (integrable_const δ),setIntegral_const,smul_eq_mul] at h0
    have hle : (∫ x in E n, u x ∂μ) ≤ μ.real A := by
      rw [←integral_indicator_one hA]
      exact setIntegral_le_integral hui (ae_of_all _ fun x => by
        by_cases hx : x ∈ A <;> simp [u,hx])
    have hb : δ*μ.real (E n) ≤ μ.real A := by linarith
    have H := ENNReal.ofReal_le_ofReal hb
    simpa only [ENNReal.ofReal_mul hδ.le,measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ (E n)),ENNReal.ofReal_toReal (measure_ne_top μ A)] using H
  have hsub : excessiveOccupation T A δ ⊆ ⋃ n, E n := by
    rintro x ⟨n,hn⟩
    apply mem_iUnion.mpr
    refine ⟨n,lt_of_lt_of_le ?_ (birkhoffSum_le_positiveRunningSum T f n x)⟩
    change 0 < ∑ j ∈ Finset.range n, (u (T^[j] x)-δ)
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hv := visitCount_cast T A n x
    change (visitCount T A n x : ℝ) = ∑ j ∈ Finset.range n, u (T^[j] x) at hv
    linarith
  calc
    _ ≤ ENNReal.ofReal δ * μ (⋃ n, E n) := mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ μ A := by
      rw [hmono.measure_iUnion,ENNReal.mul_iSup]
      exact iSup_le hEn

theorem ae_uniform_small_occupation_of_decreasing {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (A : ℕ → Set Y) (hA : ∀ m, MeasurableSet (A m)) (hmono : Antitone A)
    (hz : μ (⋂ m, A m)=0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ, ∃ m, ∀ n : ℕ, (visitCount T (A m) n x : ℝ) ≤ δ*n := by
  let E : ℕ → Set Y := fun m => excessiveOccupation T (A m) δ
  have hI : ENNReal.ofReal δ * μ (⋂ m, E m) ≤ 0 := by
    have ht := tendsto_measure_iInter_atTop (fun m => (hA m).nullMeasurableSet) hmono
      ⟨0,measure_ne_top μ _⟩
    rw [hz] at ht
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun m => (mul_le_mul' le_rfl (measure_mono (iInter_subset E m))).trans
      (excessiveOccupation_measure_bound μ hT (hA m) hδ)
  have hzero : μ (⋂ m, E m)=0 := by
    exact (mul_eq_zero.mp (le_antisymm hI bot_le)).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  have hgood : ∀ᵐ x ∂μ, x ∉ ⋂ m, E m := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using hzero
  filter_upwards [hgood] with x hx
  obtain ⟨m,hm⟩ := not_forall.mp (fun h => hx (mem_iInter.mpr h))
  refine ⟨m,?_⟩
  intro n
  exact not_lt.mp (fun hn => hm ⟨n,hn⟩)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SummablePartitionBoundaries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma realBoundaryStrip_measurableSet {f : Y → ℝ} (hf : Measurable f) (r ε : ℝ) :
    MeasurableSet (realBoundaryStrip f r ε) := by
  simp only [realBoundaryStrip,abs_le]
  exact (measurableSet_le measurable_const (hf.sub_const r)).inter
    (measurableSet_le (hf.sub_const r) measurable_const)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ContractingCutItineraries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neighborhoods inside cut-itinerary atoms

Summable boundary avoidance and uniform contraction leave an entire
parameter neighborhood in the same infinite itinerary atom. The
contraction estimate is explicit, so it can be supplied by root dynamics.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree

lemma cut_agrees_of_abs_sub_le {u v r ε : ℝ}
    (hnear : |u-v| ≤ ε) (haway : ε < |v-r|) :
    (u < r ↔ v < r) := by
  have hn := abs_le.mp hnear
  by_cases hvr : v < r
  · rw [abs_of_neg (sub_neg.mpr hvr)] at haway
    have hur : u < r := by linarith
    exact iff_of_true hur hvr
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hvr))] at haway
    have hur : ¬ u < r := by linarith
    exact iff_of_false hur hvr

theorem ae_avoid_cut_boundary_at_all_times
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {T : Y → Y} (hT : MeasurePreserving T μ μ) {f : Y → ℝ} (r : ℝ)
    (hr : μ {x | f x=r}=0) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, f (T^[n] x) ≠ r := by
  apply ae_all_iff.mpr
  intro n
  rw [ae_iff]
  simp only [not_not]
  change μ ((T^[n]) ⁻¹' {x | f x=r})=0
  exact (hT.iterate n).preimage_null hr

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixLogLength
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma matrixLogLength_le_displacements {n : ℕ} (g : G n) :
    matrixLogLength g ≤ ‖g.val-1‖+‖(g⁻¹).val-1‖ := by
  have h₁ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+‖g.val-1‖)
  have h₂ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+‖(g⁻¹).val-1‖)
  unfold matrixLogLength
  linarith

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma quotientLogDistance_nonneg {n : ℕ} (x y : X n) : 0 ≤ quotientLogDistance x y := by
  apply le_csInf (rightDisplacementLengths_nonempty x y)
  rintro r ⟨g,_,rfl⟩
  exact matrixLogLength_nonneg g

lemma quotientLogDistance_le_length {n : ℕ} (x y : X n) (g : G n)
    (hg : rightAction x g=y) : quotientLogDistance x y ≤ matrixLogLength g :=
  csInf_le (rightDisplacementLengths_bddBelow x y) ⟨g,hg,rfl⟩

lemma quotientLogDistance_self {n : ℕ} (x : X n) : quotientLogDistance x x=0 := by
  apply le_antisymm _ (quotientLogDistance_nonneg x x)
  simpa only [matrixLogLength_one] using quotientLogDistance_le_length x x 1 (rightAction_one x)

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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDilation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal dynamics in ordered upper-root coordinates

Conjugation by a diagonal element is exactly the product of the root
coordinate dilations, with each factor carrying its own root weight.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem upperRootWord_diagonal (n : ℕ) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (t : UpperRootTime n) :
    (upperRootWordHomeomorph n ((completeRootChain n).rootDilation ell r t)).val =
      diagonalOneParameter ell hell r * (upperRootWordHomeomorph n t).val *
        diagonalOneParameter ell hell (-r) :=
  (completeRootChain n).word_rootDilation ell hell r t

theorem upperRoot_orbit_diagonal (n : ℕ) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (x : X n) (t : UpperRootTime n) :
    rightAction (rightAction x (upperRootWordHomeomorph n t).val)
        (diagonalOneParameter ell hell r) =
      rightAction (rightAction x (diagonalOneParameter ell hell r))
        (upperRootWordHomeomorph n ((completeRootChain n).rootDilation ell (-r) t)).val := by
  rw [rightAction_mul, rightAction_mul, upperRootWord_diagonal n ell hell (-r) t, neg_neg,
    diagonalOneParameter_neg]
  congr 1
  group

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One real coordinate for each positive root

The elimination time space is canonically a finite product of real
lines, indexed without repetition by the positive roots. Diagonal
conjugation scales each coordinate by its own root character.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma timeVectorHomeomorph_cube (c : EliminationChain P D) (R : ℝ) (t : c.Time) :
    t ∈ c.cube R ↔ ∀ k, |c.timeVectorHomeomorph t k| < R := by
  induction c with
  | done => simp [cube, roots]
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change t.1 ∈ tail.cube R ∧ t.2 ∈ Ioo (-R) R ↔
        ∀ k : Fin (tail.roots.length + 1),
          |Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ) t.2 (tail.timeVectorHomeomorph t.1) k| < R
      rw [ih, Set.mem_Ioo, ←abs_lt]
      constructor
      · rintro ⟨h₁, h₂⟩ k
        refine Fin.cases ?_ (fun j => ?_) k
        · simpa only [Fin.cons_zero] using h₂
        · simpa only [Fin.cons_succ] using h₁ j
      · intro h
        exact ⟨fun j => by simpa only [Fin.cons_succ] using h j.succ,
          by simpa only [Fin.cons_zero] using h 0⟩

lemma timeVectorHomeomorph_dilation (c : EliminationChain P D) (ell : Fin n → ℝ)
    (r : ℝ) (t : c.Time) (k : Fin c.roots.length) :
    c.timeVectorHomeomorph (c.rootDilation ell r t) k =
      Real.exp ((ell (c.roots.get k).1 - ell (c.roots.get k).2) * r) *
        c.timeVectorHomeomorph t k := by
  induction c with
  | done => exact Fin.elim0 k
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change Fin (tail.roots.length + 1) at k
      change Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
        (Real.exp ((ell a - ell b) * r) * t.2)
          (tail.timeVectorHomeomorph (tail.rootDilation ell r t.1)) k =
        Real.exp ((ell (((a, b) :: tail.roots).get k).1 -
          ell (((a, b) :: tail.roots).get k).2) * r) *
            Fin.cons (α := fun _ : Fin (tail.roots.length + 1) => ℝ)
              t.2 (tail.timeVectorHomeomorph t.1) k
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · exact ih t.1 j

end EliminationChain

lemma upperRootEuclideanCoordinates_cube (n : ℕ) (R : ℝ) (t : UpperRootTime n) :
    t ∈ (completeRootChain n).cube R ↔ ∀ p, |upperRootEuclideanCoordinates n t p| < R := by
  rw [(completeRootChain n).timeVectorHomeomorph_cube]
  constructor
  · intro h p
    exact h ((upperRootIndexEquiv n).symm p)
  · intro h k
    have H := h (upperRootIndexEquiv n k)
    change |(completeRootChain n).timeVectorHomeomorph t
      ((upperRootIndexEquiv n).symm (upperRootIndexEquiv n k))| < R at H
    simpa only [Equiv.symm_apply_apply] using H

lemma upperRootEuclideanCoordinates_dilation (n : ℕ) (ell : Fin n → ℝ)
    (r : ℝ) (t : UpperRootTime n) (p : allPositiveRoots n) :
    upperRootEuclideanCoordinates n ((completeRootChain n).rootDilation ell r t) p =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) * upperRootEuclideanCoordinates n t p := by
  have h := (completeRootChain n).timeVectorHomeomorph_dilation ell r t
    ((upperRootIndexEquiv n).symm p)
  have he : (completeRootChain n).roots.get ((upperRootIndexEquiv n).symm p) = p.val := by
    exact congrArg Subtype.val ((upperRootIndexEquiv n).apply_symm_apply p)
  change (completeRootChain n).timeVectorHomeomorph
    ((completeRootChain n).rootDilation ell r t) ((upperRootIndexEquiv n).symm p) =
      Real.exp ((ell p.val.1 - ell p.val.2) * r) *
        (completeRootChain n).timeVectorHomeomorph t ((upperRootIndexEquiv n).symm p)
  simpa only [he] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationMatrixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Each Gaussian root parameter is its corresponding matrix entry -/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem upperRootEuclideanCoordinates_entry (n : ℕ) (t : UpperRootTime n)
    (p : allPositiveRoots n) :
    ((completeRootChain n).word t).val p.val.1 p.val.2 = upperRootEuclideanCoordinates n t p := by
  have he : (completeRootChain n).roots.get ((upperRootIndexEquiv n).symm p) = p.val :=
    congrArg Subtype.val ((upperRootIndexEquiv n).apply_symm_apply p)
  have H := (completeRootChain n).word_entry_eq_time (by
    intro q hq
    rw [completeRootChain_final] at hq
    exact (Finset.mem_filter.mp hq).2) t ((upperRootIndexEquiv n).symm p)
  change ((completeRootChain n).word t).val p.val.1 p.val.2 =
    (completeRootChain n).timeVectorHomeomorph t ((upperRootIndexEquiv n).symm p)
  simpa only [he] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootContraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contracting diagonal dynamics on full upper-root leaves

The explicit root coordinates identify the contracting unipotent
foliation. Uniform root-weight gaps give an exponential bound on its
Euclidean size; strict gaps give convergence to the identity.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootSize_dilation_le (n : ℕ) (ell : Fin n → ℝ) (ε r : ℝ)
    (hgap : ∀ p : allPositiveRoots n, ε ≤ ell p.val.2 - ell p.val.1)
    (hr : 0 ≤ r) (t : UpperRootTime n) :
    upperRootSize n ((completeRootChain n).rootDilation ell r t) ≤
      Real.exp (-ε * r) * upperRootSize n t := by
  unfold upperRootSize
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro p
  rw [upperRootEuclideanCoordinates_dilation, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (hgap p) hr
    nlinarith
  · exact norm_le_pi_norm _ p
  · exact norm_nonneg _
  · exact (Real.exp_pos _).le

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootUniformContraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform contraction of bounded upper-root boxes

Strictly contracting root weights shrink every bounded root cube into
any prescribed identity neighborhood, uniformly over the cube. This is
the geometric control used by the unstable conditional entropy argument.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_upperRootCube_iff_size_lt (n : ℕ) {R : ℝ} (hR : 0 < R) (t : UpperRootTime n) :
    t ∈ (completeRootChain n).cube R ↔ upperRootSize n t < R := by
  rw [upperRootEuclideanCoordinates_cube, upperRootSize, pi_norm_lt_iff hR]
  simp only [Real.norm_eq_abs]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootLogContraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential root contraction in logarithmic matrix length -/

noncomputable section
open Matrix Set
open scoped Matrix.Norms.Operator Topology BigOperators NNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma inverse_displacement_le_twice {d : ℕ} (g : G (d+1))
    (hg : ‖g.val-1‖ ≤ 1/2) : ‖(g⁻¹).val-1‖ ≤ 2*‖g.val-1‖ := by
  have he : (g⁻¹).val*g.val=1 := congrArg Subtype.val (inv_mul_cancel g)
  have hid : (g⁻¹).val-1 = -((g⁻¹).val*(g.val-1)) := by
    rw [mul_sub,he,mul_one]
    abel
  have hnorm : ‖(g⁻¹).val-1‖ ≤ ‖(g⁻¹).val‖*‖g.val-1‖ := by
    rw [hid,norm_neg]
    exact norm_mul_le _ _
  have hi : ‖(g⁻¹).val‖ ≤ ‖(g⁻¹).val-1‖+1 := by
    simpa only [sub_add_cancel,norm_one] using norm_add_le ((g⁻¹).val-1) 1
  have hb := mul_le_mul_of_nonneg_right hi (norm_nonneg (g.val-1))
  nlinarith [norm_nonneg ((g⁻¹).val-1)]

lemma matrixLogLength_le_three_displacement {d : ℕ} (g : G (d+1))
    (hg : ‖g.val-1‖ ≤ 1/2) : matrixLogLength g ≤ 3*‖g.val-1‖ := by
  have h₁ := matrixLogLength_le_displacements g
  have h₂ := inverse_displacement_le_twice g hg
  linarith

lemma matrix_opNorm_le_card_mul_entryBound {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i j, |M i j| ≤ C) : ‖M‖ ≤ (n:ℝ)*C := by
  let c : ℝ≥0 := ⟨C,hC⟩
  have H : ‖M‖₊ ≤ (n:ℝ≥0)*c := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc
      ∑ j, ‖M i j‖₊ ≤ ∑ _j : Fin n, c := by
        apply Finset.sum_le_sum
        intro j _
        exact_mod_cast hM i j
      _ = (n:ℝ≥0)*c := by simp
  exact_mod_cast H

lemma upperRoot_displacement_le_size (n : ℕ) (t : UpperRootTime n) :
    ‖((completeRootChain n).word t).val-1‖ ≤ (n:ℝ)*upperRootSize n t := by
  apply matrix_opNorm_le_card_mul_entryBound _ (norm_nonneg _)
  intro i j
  by_cases hij : i < j
  · let p : allPositiveRoots n := ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
    have H := norm_le_pi_norm (upperRootEuclideanCoordinates n t) p
    rw [Matrix.sub_apply,Matrix.one_apply,ite_eq_right (ne_of_lt hij),sub_zero]
    have he := upperRootEuclideanCoordinates_entry n t p
    change ((completeRootChain n).word t).val i j = upperRootEuclideanCoordinates n t p at he
    rw [he]
    simpa only [Real.norm_eq_abs,upperRootSize] using H
  · have H := positiveRootGeneratedGroup_pattern (allPositiveRoots n) (allPositiveRoots_closed n)
      (upperRootWord_mem n t) i j (by simpa only [allPositiveRoots,Finset.mem_filter,Finset.mem_univ,true_and] using hij)
    rw [Matrix.sub_apply,H,sub_self,abs_zero]
    exact norm_nonneg _

theorem upperRoot_logLength_contraction {d : ℕ}
    (ell : Fin (d+1) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    {R : ℝ} (hR : 0 < R) (hsmall : 3*(d+1:ℝ)*R ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) {t : UpperRootTime (d+1)}
    (ht : t ∈ (completeRootChain (d+1)).cube R) :
    matrixLogLength ((completeRootChain (d+1)).word
      ((completeRootChain (d+1)).rootDilation ell r t)) ≤ Real.exp (-ε*r) := by
  let w := (completeRootChain (d+1)).word ((completeRootChain (d+1)).rootDilation ell r t)
  have hs : upperRootSize (d+1) t ≤ R := ((mem_upperRootCube_iff_size_lt (d+1) hR t).mp ht).le
  have hscale := upperRootSize_dilation_le (d+1) ell ε r hgap hr t
  have hnorm : ‖w.val-1‖ ≤ (d+1:ℝ)*Real.exp (-ε*r)*R := by
    have H := upperRoot_displacement_le_size (d+1)
      ((completeRootChain (d+1)).rootDilation ell r t)
    dsimp only [w]
    calc
      _ ≤ (d+1:ℝ)*upperRootSize (d+1) ((completeRootChain (d+1)).rootDilation ell r t) := by
        simpa only [Nat.cast_add,Nat.cast_one] using H
      _ ≤ (d+1:ℝ)*(Real.exp (-ε*r)*R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hscale.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)
      _ = _ := by ring
  have he : Real.exp (-ε*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hhalf : ‖w.val-1‖ ≤ 1/2 := by
    have hbound : (d+1:ℝ)*Real.exp (-ε*r)*R ≤ (d+1:ℝ)*R := by
      nlinarith [mul_nonneg (show 0 ≤ (d+1:ℝ) by positivity) hR.le]
    linarith
  have H := matrixLogLength_le_three_displacement w hhalf
  have hlast : 3*((d+1:ℝ)*Real.exp (-ε*r)*R) ≤ Real.exp (-ε*r) := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (-ε*r)).le]
  exact H.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans hlast)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_UpperRootCutItineraries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual diagonal cut itineraries contain root neighborhoods

For each logarithmic distance observable one can choose a cut with
summable boundary returns. The proved matrix contraction then places a
whole upper-root neighborhood in almost every infinite itinerary atom.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRoot_orbit_iterate_diagonal {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (k : ℕ)
    (x : X n) (t : UpperRootTime n) :
    (fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain n).word t)) =
      rightAction ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)
        ((completeRootChain n).word ((completeRootChain n).rootDilation ell k t)) := by
  have hp : (diagonalOneParameter ell hell (-1))^k=diagonalOneParameter ell hell (-(k:ℝ)) := by
    rw [diagonalOneParameter_neg,inv_pow,←diagonalOneParameter_nat,diagonalOneParameter_neg]
  simp only [rightAction_iterate,hp]
  simpa only [neg_neg, upperRootWordHomeomorph_apply] using
    upperRoot_orbit_diagonal n ell hell (-(k:ℝ)) x t

theorem quotientLogDistance_upperRoot_iterate_bound {d : ℕ}
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    {R : ℝ} (hR : 0 < R) (hsmall : 3*(d+1:ℝ)*R ≤ 1)
    (z x : X (d+1)) (k : ℕ) {t : UpperRootTime (d+1)}
    (ht : t ∈ (completeRootChain (d+1)).cube R) :
    |quotientLogDistance z
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word t))) -
      quotientLogDistance z
        ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)| ≤
      Real.exp (-ε*(k:ℝ)) := by
  rw [upperRoot_orbit_iterate_diagonal]
  exact (quotientLogDistance_right_bound z _ _).trans
    (upperRoot_logLength_contraction ell ε hε hgap hR hsmall (Nat.cast_nonneg _) ht)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SublinearHeight
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sublinear growth of a height with bounded upward increments

A high endpoint forces a long preceding interval in a high-level set.
The maximal occupation bound therefore makes every positive linear
slope an eventual upper bound. The height itself need not be integrable.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

private lemma height_iterate_le {Y : Type*} (T : Y → Y) (H : Y → ℕ)
    (hstep : ∀ x, H (T x) ≤ H x+1) (n : ℕ) (x : Y) :
    H (T^[n] x) ≤ H x+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hstep _).trans (by omega)

private lemma height_endpoint_visit_bound {Y : Type*} (T : Y → Y) (H : Y → ℕ)
    (hstep : ∀ x, H (T x) ≤ H x+1) (x : Y) (M n : ℕ) (hx : H x ≤ M) :
    H (T^[n] x)-M ≤ visitCount T {y | M ≤ H y} n x := by
  classical
  let k := H (T^[n] x)-M
  have hkn : k ≤ n := by
    have h := height_iterate_le T H hstep n x
    dsimp [k]
    omega
  have hsub : Finset.Ico (n-k) n ⊆
      (Finset.range n).filter (fun j => M ≤ H (T^[j] x)) := by
    intro j hj
    obtain ⟨hjl,hju⟩ := Finset.mem_Ico.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hju,?_⟩
    have hb := height_iterate_le T H hstep (n-j) (T^[j] x)
    rw [←Function.iterate_add_apply,Nat.sub_add_cancel hju.le] at hb
    dsimp [k] at hjl hkn
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hcard : ((Finset.range n).filter (fun j => M ≤ H (T^[j] x))).card =
      visitCount T {y | M ≤ H y} n x := by
    unfold visitCount
    congr 1
    ext j
    simp only [Finset.mem_filter,Set.mem_ofPred_eq]
  rw [hcard,Nat.sub_sub_self hkn] at hc
  exact hc

theorem ae_height_affine_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ x ∂μ, ∃ C : ℕ, ∀ n : ℕ, (H (T^[n] x) : ℝ) ≤ C+δ*n := by
  let A : ℕ → Set Y := fun m => {x | m ≤ H x}
  have hAm m : MeasurableSet (A m) :=
    hH (measurableSet_Ici : MeasurableSet (Set.Ici m))
  have hAmn : Antitone A := fun i j hij x hx => hij.trans hx
  have hempty : (⋂ m, A m) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := mem_iInter.mp hx (H x+1)
    exact Nat.not_succ_le_self _ h
  have hz : μ (⋂ m, A m)=0 := by rw [hempty,measure_empty]
  filter_upwards [ae_uniform_small_occupation_of_decreasing μ hT A hAm hAmn hz hδ]
    with x hx
  obtain ⟨m,hm⟩ := hx
  let C := max m (H x)
  have hc (n : ℕ) : visitCount T (A C) n x ≤ visitCount T (A m) n x := by
    exact visitCount_mono T (fun _ hy => (le_max_left m (H x)).trans hy) n x
  refine ⟨C,?_⟩
  intro n
  have hb := height_endpoint_visit_bound T H hstep x C n (le_max_right _ _)
  have hv : (visitCount T (A C) n x : ℝ) ≤ δ*n :=
    (Nat.cast_le.mpr (hc n)).trans (hm n)
  by_cases hCn : C ≤ H (T^[n] x)
  · have hb' : (H (T^[n] x) : ℝ)-(C:ℝ) ≤ visitCount T (A C) n x := by
      exact_mod_cast hb
    linarith
  · have hb' : (H (T^[n] x) : ℝ) ≤ C := by exact_mod_cast le_of_not_ge hCn
    exact hb'.trans (le_add_of_nonneg_right (mul_nonneg hδ.le (Nat.cast_nonneg n)))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TemperedChartRadius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subexponential chart radii along almost every diagonal orbit

Bounded height increments and finite invariant mass give sublinear height
growth by the maximal occupation inequality. Applied to the actual local
injectivity height, this proves the chart control needed in entropy
comparisons without assuming an integrable logarithmic cusp height.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_height_div_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (H (T^[n] x) : ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have hbound (q : ℕ) := ae_height_affine_bound μ hT H hH hstep
    (show 0 < 1/(q+1:ℝ) by positivity)
  filter_upwards [ae_all_iff.mpr hbound] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨q,hq⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨C,hC⟩ := hx q
  have hlim : Tendsto (fun n : ℕ => (C:ℝ)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε)),eventually_ge_atTop 1]
    with n hn hnone
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hnone
  have hf := div_le_div_of_nonneg_right (hC n) hnp.le
  rw [add_div,mul_div_cancel_right₀ _ hnp.ne'] at hf
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnp.le)]
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LayeredObservations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding finite observations chosen by an integer height -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace DukePrimeDegree

lemma layeredObservation_measurable {Y : Type*} [MeasurableSpace Y]
    {N : ℕ → ℕ} {H : Y → ℕ} (hH : Measurable H)
    {P : ∀ m, Y → Fin (N m)} (hP : ∀ m, Measurable (P m)) :
    Measurable (layeredObservation H P) := by
  have hvar : Measurable (fun p : ℕ × Y => (P p.1 p.2).val) :=
    measurable_from_prod_countable_right fun m =>
      (measurable_of_finite (fun u : Fin (N m) => u.val)).comp (hP m)
  exact (measurable_of_countable (fun p : ℕ × ℕ => Nat.pair p.1 p.2)).comp
    (hH.prodMk (hvar.comp (hH.prodMk measurable_id)))

lemma layeredObservation_eq {Y : Type*} {N : ℕ → ℕ} (H : Y → ℕ)
    (P : ∀ m, Y → Fin (N m)) {x y : Y}
    (h : layeredObservation H P y=layeredObservation H P x) :
    H y=H x ∧ P (H x) y=P (H x) x := by
  have hp : H y=H x ∧ (P (H y) y).val=(P (H x) x).val := Nat.pair_eq_pair.mp h
  refine ⟨hp.1,?_⟩
  apply Fin.ext
  have hv := hp.2
  rwa [hp.1] at hv

lemma layeredObservation_finite_levels {Y : Type*} {N : ℕ → ℕ}
    (H : Y → ℕ) (P : ∀ m, Y → Fin (N m)) (m : ℕ) :
    (layeredObservation H P '' {x | H x ≤ m}).Finite := by
  classical
  have hlevel (k : ℕ) : (layeredObservation H P '' {x | H x=k}).Finite := by
    apply ((Set.finite_range (fun p : Fin (N k) => Nat.pair k p.val))).subset
    rintro _ ⟨x,hx,rfl⟩
    change H x=k at hx
    subst k
    exact ⟨P (H x) x,rfl⟩
  apply (Set.Finite.biUnion (Finset.finite_toSet (Finset.range (m+1)))
    (fun k _ => hlevel k)).subset
  rintro _ ⟨x,hx,rfl⟩
  exact mem_iUnion₂.mpr ⟨H x,by simpa using Nat.lt_succ_of_le hx,
    mem_image_of_mem (layeredObservation H P) rfl⟩

lemma layeredObservation_future_eq {Y V : Type*} [TopologicalSpace V]
    {N : ℕ → ℕ} (H : Y → ℕ) (P : ∀ m, Y → Fin (N m))
    (T : Y → Y) (F : V → Y) (v₀ : V)
    (hH : ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ, H (T^[k] (F v))=H (T^[k] (F v₀)))
    (hP : ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
      P (H (T^[k] (F v₀))) (T^[k] (F v))=P (H (T^[k] (F v₀))) (T^[k] (F v₀))) :
    ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
      layeredObservation H P (T^[k] (F v))=layeredObservation H P (T^[k] (F v₀)) := by
  filter_upwards [hH,hP] with v hvH hvP
  intro k
  unfold layeredObservation
  rw [hvH k,hvP k]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CutFamilyCode
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite integer codes for families of real cuts -/

noncomputable section
open MeasureTheory
namespace DukePrimeDegree

lemma finiteCutCode_measurable {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    {f : Fin N → Y → ℝ} (hf : ∀ i, Measurable (f i)) (c : Fin N → ℝ) :
    Measurable (finiteCutCode f c) := by
  apply (measurable_of_finite (Fintype.equivFin (Fin N → Bool))).comp
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_bool
  have he : (fun x => decide (f i x < c i)) ⁻¹' {true} = {x | f i x < c i} := by
    ext x
    simp
  rw [he]
  exact measurableSet_lt (hf i) measurable_const

lemma finiteCutCode_eq_of_iff {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (h : ∀ i, f i y < c i ↔ f i x < c i) : finiteCutCode f c y=finiteCutCode f c x := by
  apply congrArg (Fintype.equivFin (Fin N → Bool))
  funext i
  simp only [h i]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FirstCoverCode
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One covering label instead of the full vector of cut tests

A point is labeled by one cut containing it. There are N+1 labels for N
cuts. Equality of labels still puts covered points in the same small
set, while constancy of all cut tests implies constancy of this label.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

private lemma firstTrue_common {N : ℕ} (v w : Fin N → Bool)
    (hw : ∃ i, w i=true) (h : firstTrue v=firstTrue w) :
    ∃ i, v i=true ∧ w i=true := by
  classical
  have hv : ∃ i, v i=true := by
    by_contra hn
    have hh := congrArg Fin.val h
    simp only [firstTrue,dite_eq_right hn,dite_eq_left hw,Fin.val_zero] at hh
    omega
  have hi : hv.choose=hw.choose := by
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [firstTrue,dite_eq_left hv,dite_eq_left hw] at hh
    omega
  exact ⟨hw.choose,hi ▸ hv.choose_spec,hw.choose_spec⟩

lemma firstCoverCode_measurable {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    {f : Fin N → Y → ℝ} (hf : ∀ i, Measurable (f i)) (c : Fin N → ℝ) :
    Measurable (firstCoverCode f c) := by
  have h := (measurable_of_finite
    (fun u : Fin (Fintype.card (Fin N → Bool)) =>
      firstTrue ((Fintype.equivFin (Fin N → Bool)).symm u))).comp
        (finiteCutCode_measurable hf c)
  change Measurable (fun x => firstTrue (fun i => decide (f i x < c i)))
  simpa only [Function.comp_def,finiteCutCode,Equiv.symm_apply_apply] using h

lemma firstCoverCode_eq_of_cutCode_eq {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (h : finiteCutCode f c y=finiteCutCode f c x) :
    firstCoverCode f c y=firstCoverCode f c x :=
  congrArg firstTrue ((Fintype.equivFin (Fin N → Bool)).injective h)


lemma firstCoverCode_selected {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) (x : Y)
    (hx : ∃ i, f i x < c i) :
    ∃ i : Fin N, (firstCoverCode f c x).val=i.val+1 ∧ f i x < c i := by
  have hw : ∃ i, decide (f i x < c i)=true := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,decide_eq_true hi⟩
  refine ⟨hw.choose,?_,of_decide_eq_true hw.choose_spec⟩
  simp only [firstCoverCode,firstTrue,dite_eq_left hw]

lemma firstCoverCode_common {Y : Type*} {N : ℕ}
    (f : Fin N → Y → ℝ) (c : Fin N → ℝ) {x y : Y}
    (hx : ∃ i, f i x < c i) (h : firstCoverCode f c y=firstCoverCode f c x) :
    ∃ i, f i y < c i ∧ f i x < c i := by
  have hw : ∃ i, decide (f i x < c i)=true := by
    obtain ⟨i,hi⟩ := hx
    exact ⟨i,decide_eq_true hi⟩
  obtain ⟨i,hi,hj⟩ := firstTrue_common (fun i => decide (f i y < c i))
    (fun i => decide (f i x < c i)) hw h
  exact ⟨i,of_decide_eq_true hi,of_decide_eq_true hj⟩

lemma layered_firstCover_eq_of_cutCode_eq {Y : Type*} {N : ℕ → ℕ}
    (H : Y → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ) (c : ∀ m, Fin (N m) → ℝ)
    {x y : Y}
    (h : layeredObservation H (fun m => finiteCutCode (f m) (c m)) y =
      layeredObservation H (fun m => finiteCutCode (f m) (c m)) x) :
    layeredObservation H (fun m => firstCoverCode (f m) (c m)) y =
      layeredObservation H (fun m => firstCoverCode (f m) (c m)) x := by
  obtain ⟨hH,hP⟩ := layeredObservation_eq H _ h
  unfold layeredObservation
  rw [hH]
  dsimp only
  rw [firstCoverCode_eq_of_cutCode_eq _ _ hP]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ConjugationRadius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SmallMatrixLength
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative logarithmic length near the identity

The algebraic inverse identity bounds the inverse norm by two on a
half-unit operator ball. Consequently logarithmic length is bounded by
three times the displacement norm there.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

lemma specialLinear_inverse_norm_le_two {n : ℕ} (hn : 0 < n)
    (g : G n) (hg : ‖g.val-1‖ ≤ 1/2) : ‖(g⁻¹).val‖ ≤ 2 := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he : (g⁻¹).val = 1-(g⁻¹).val*(g.val-1) := by
    rw [Matrix.mul_sub,Matrix.mul_one]
    have hmul : (g⁻¹).val*g.val = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      change (g⁻¹*g).val=1
      simp
    rw [hmul]
    abel
  have hbound : ‖(g⁻¹).val‖ ≤ 1+‖(g⁻¹).val‖*‖g.val-1‖ := by
    calc
      _ = ‖1-(g⁻¹).val*(g.val-1)‖ := congrArg norm he
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖+‖(g⁻¹).val*(g.val-1)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_one]
        exact add_le_add le_rfl (norm_mul_le (g⁻¹).val (g.val-1))
  nlinarith [mul_le_mul_of_nonneg_left hg (norm_nonneg (g⁻¹).val)]

lemma matrixLogLength_le_three_norm {n : ℕ} (hn : 0 < n)
    (g : G n) (hg : ‖g.val-1‖ ≤ 1/2) :
    matrixLogLength g ≤ 3*‖g.val-1‖ := by
  have hi := specialLinear_inverse_norm_le_two hn g hg
  have he : (g⁻¹).val-1 = -((g⁻¹).val*(g.val-1)) := by
    rw [Matrix.mul_sub,Matrix.mul_one]
    have hmul : (g⁻¹).val*g.val = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      change (g⁻¹*g).val=1
      simp
    rw [hmul]
    abel
  have hdiff : ‖(g⁻¹).val-1‖ ≤ 2*‖g.val-1‖ := by
    rw [he,norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have H := matrixLogLength_le_displacements g
  linarith

lemma matrixLogLength_le_three_card_radius {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : (n:ℝ)*r ≤ 1/2)
    {g : G n} (hg : g ∈ matrixBall n r) :
    matrixLogLength g ≤ 3*(n:ℝ)*r := by
  have hnorm := matrix_operator_norm_le_card_mul (g.val-1) hr (fun i j => (hg i j).le)
  exact (matrixLogLength_le_three_norm hn g (hnorm.trans hsmall)).trans (by nlinarith)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LocalQuotientPacking
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform local packing after rescaling a quotient chart

The number of separated points in a fixed multiple of a sufficiently
small chart is bounded independently of the chart radius and base point.
The proof uses the existing finite matrix grid and actual right lifts.
-/

noncomputable section
open Matrix Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

theorem local_quotient_packing_bound {n N : ℕ} (hn : 0 < n)
    (x : X n) (g : Fin N → G n) {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hg : ∀ i, g i ∈ matrixBall n (C*δ))
    (hsep : ∀ i j, i ≠ j → δ ≤
      quotientLogDistance (rightAction x (g i)) (rightAction x (g j))) :
    (N:ℝ) ≤ localQuotientPackingBound n C := by
  classical
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let η : ℝ := 1/(96*(n:ℝ)^2)
  have hη : 0 < η := by dsimp [η] <;> positivity
  have hη1 : η ≤ 1 := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    dsimp [η]
    apply (div_le_iff₀ (by positivity : 0 < 96*(n:ℝ)^2)).mpr
    nlinarith
  have hscale : 8*(n:ℝ)^2*η=1/12 := by
    dsimp [η]
    field_simp [hnp.ne']
    ring
  let q (i : Fin N) (t : Fin (n*n)) : ℝ :=
    ((g i).val (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 -
      (1 : Matrix (Fin n) (Fin n) ℝ) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)/δ
  have hq (i : Fin N) (t : Fin (n*n)) : |q i t| ≤ C := by
    dsimp [q]
    rw [abs_div,abs_of_pos hδ]
    apply (div_le_iff₀ hδ).mpr
    exact (hg i _ _).le
  obtain ⟨s,_,hcard,hcover⟩ := cube_grid_cover (n*n) hC hη hη1
  choose c hc hclose using (fun i => hcover (q i) (hq i))
  let f : Fin N → s := fun i => ⟨c i,hc i⟩
  have hinv (i : Fin N) : ∀ a b, |(g i)⁻¹.val a b| ≤ 2 := by
    have hnorm : ‖(g i).val-1‖ ≤ 1/2 :=
      (matrix_operator_norm_le_card_mul _ (mul_nonneg hC hδ.le)
        (fun a b => (hg i a b).le)).trans (by simpa only [mul_assoc] using hsmall)
    exact fun a b => (matrix_entry_abs_le_operator_norm _ a b).trans
      (specialLinear_inverse_norm_le_two hn (g i) hnorm)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hcij : c i=c j := congrArg Subtype.val hij
    have hdiff (a b : Fin n) : |(g j).val a b-(g i).val a b| ≤ 2*η*δ := by
      let t := finProdFinEquiv (a,b)
      have hi := hclose i t
      have hj := hclose j t
      rw [hcij] at hi
      have hqdiff : |q j t-q i t| ≤ 2*η := by
        calc
          _ = |(q j t-c j t)+(c j t-q i t)| := by congr 1; ring
          _ ≤ |q j t-c j t|+|c j t-q i t| := abs_add_le _ _
          _ ≤ 2*η := by rw [abs_sub_comm (c j t)]; linarith
      have he : (g j).val a b-(g i).val a b = δ*(q j t-q i t) := by
        dsimp [q,t]
        simp only [Equiv.symm_apply_apply]
        field_simp [hδ.ne']
        ring
      rw [he,abs_mul,abs_of_pos hδ]
      nlinarith [mul_le_mul_of_nonneg_left hqdiff hδ.le]
    let r : ℝ := 8*(n:ℝ)*η*δ
    have hr : 0 < r := by dsimp [r] <;> positivity
    have hnr : (n:ℝ)*r=δ/12 := by
      dsimp [r]
      calc
        _ = (8*(n:ℝ)^2*η)*δ := by ring
        _ = _ := by rw [hscale]; ring
    have hrel : (g i)⁻¹*g j ∈ matrixBall n r := by
      intro a b
      have hh := left_div_entry_bound (g i) (g j) (by norm_num : (0:ℝ) ≤ 2)
        (hinv i) hdiff a b
      apply hh.trans_lt
      dsimp [r]
      nlinarith [mul_pos hnp hη, mul_pos (mul_pos hnp hη) hδ]
    have ha : rightAction (rightAction x (g i)) ((g i)⁻¹*g j)=rightAction x (g j) := by
      rw [rightAction_mul]
      congr 1
      group
    have hd := (quotientLogDistance_le_length _ _ _ ha).trans
      (matrixLogLength_le_three_card_radius hn hr.le (by rw [hnr]; linarith) hrel)
    have hsep' := hsep i j hne
    have hh : 3*(n:ℝ)*r=δ/4 := by nlinarith [hnr]
    rw [hh] at hd
    linarith
  have hNs : N ≤ s.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact (show (N:ℝ) ≤ s.card by exact_mod_cast hNs).trans hcard

lemma local_quotient_packing_finset_bound {n : ℕ} (hn : 0 < n)
    {α : Type*} (S : Finset α) (z : α → X n) (x : X n)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hlift : ∀ i ∈ S, ∃ g ∈ matrixBall n (C*δ), rightAction x g=z i)
    (hsep : (S : Set α).Pairwise (fun i j => δ ≤ quotientLogDistance (z i) (z j))) :
    (S.card:ℝ) ≤ localQuotientPackingBound n C := by
  classical
  choose g hg ha using (fun i : S => hlift i.val i.prop)
  let e : Fin S.card ≃ S := S.equivFin.symm
  apply local_quotient_packing_bound hn x (fun i => g (e i)) hC hδ hδ1 hsmall
    (fun i => hg (e i))
  intro i j hij
  rw [ha (e i),ha (e j)]
  apply hsep (e i).prop (e j).prop
  intro he
  exact hij (e.injective (Subtype.ext he))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FirstCoverLocalPacking
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local bounds for the actual first-cover labels

If the covering balls meeting a set have their separated centers in one
small relative chart, only uniformly many of the actual labels occur.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem firstCover_local_label_bound_of_lifts {n N : ℕ} (hn : 0 < n)
    (z : Fin N → X n) (c : Fin N → ℝ) (E : Set (X n)) (x : X n)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hsep : ∀ i j, i ≠ j → δ ≤ quotientLogDistance (z i) (z j))
    (hcover : ∀ y ∈ E, ∃ i, quotientLogDistance (z i) y < c i)
    (hnear : ∀ i, (∃ y ∈ E, quotientLogDistance (z i) y < c i) →
      ∃ g ∈ matrixBall n (C*δ), rightAction x g=z i) :
    ∃ F : Finset (Fin (N+1)),
      (firstCoverCode (fun i => quotientLogDistance (z i)) c) '' E ⊆ F ∧
        (F.card:ℝ) ≤ localQuotientPackingBound n C := by
  classical
  let I : Finset (Fin N) := Finset.univ.filter
    (fun i => ∃ y ∈ E, quotientLogDistance (z i) y < c i)
  let f : Fin N → Fin (N+1) := fun i => ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩
  have hbound : (I.card:ℝ) ≤ localQuotientPackingBound n C := by
    apply local_quotient_packing_finset_bound hn I z x hC hδ hδ1 hsmall
    · intro i hi
      exact hnear i (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact hsep i j hij
  refine ⟨I.image f,?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨i,hi,hiy⟩ := firstCoverCode_selected
      (fun i => quotientLogDistance (z i)) c y (hcover y hy)
    have hiI : i ∈ I := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,y,hy,hiy⟩
    apply Finset.mem_image.mpr
    refine ⟨i,hiI,?_⟩
    exact Fin.ext hi.symm
  · exact (show ((I.image f).card:ℝ) ≤ I.card by
      exact_mod_cast Finset.card_image_le).trans hbound

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ScaledMatrixBalls
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform scaled matrix-ball operations for adjacent observation cells -/

noncomputable section
open Matrix Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrixBall_mul_scaled {n : ℕ} {C D δ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {g h : G n} (hg : g ∈ matrixBall n (C*δ)) (hh : h ∈ matrixBall n (D*δ)) :
    g*h ∈ matrixBall n
      ((((n:ℝ)*C)*((n:ℝ)*D)+(n:ℝ)*C+(n:ℝ)*D+1)*δ) := by
  let A : ℝ := n*C
  let B : ℝ := n*D
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hC
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hD
  have hgN : ‖g.val-1‖ ≤ A*δ := by
    simpa only [A,mul_assoc] using matrix_operator_norm_le_card_mul (g.val-1)
      (mul_nonneg hC hδ.le) (fun i j => (hg i j).le)
  have hhN : ‖h.val-1‖ ≤ B*δ := by
    simpa only [B,mul_assoc] using matrix_operator_norm_le_card_mul (h.val-1)
      (mul_nonneg hD hδ.le) (fun i j => (hh i j).le)
  have he : (g*h).val-1=(g.val-1)*(h.val-1)+(g.val-1)+(h.val-1) := by
    change g.val*h.val-1= _
    noncomm_ring
  have hd : δ^2 ≤ δ := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hd (mul_nonneg hA hB)
  have hb : ‖(g*h).val-1‖ ≤ (A*B+A+B)*δ := by
    calc
      _ ≤ ‖(g.val-1)*(h.val-1)‖+‖g.val-1‖+‖h.val-1‖ := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (A*δ)*(B*δ)+A*δ+B*δ := by
        exact add_le_add (add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul hgN hhN (norm_nonneg _) (mul_nonneg hA hδ.le)))
          hgN) hhN
      _ ≤ _ := by nlinarith
  intro i j
  change |((g*h).val-1) i j| < (A*B+A+B+1)*δ
  exact ((matrix_entry_abs_le_operator_norm _ i j).trans hb).trans_lt (by nlinarith)

lemma matrixBall_right_translate_scaled {n : ℕ} (hn : 0 < n)
    (a : G n) {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    {g : G n} (hg : g ∈ matrixBall n (C*δ)) :
    a⁻¹*g*a ∈ matrixBall n ((2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C)*δ) := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let R : ℝ := (2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C)*δ
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hm : MulAut.conj a⁻¹ g ∈ matrixBall n R := by
    apply conjugation_matrixBall_exp_bound hn a⁻¹ hR
    refine ⟨g,?_,rfl⟩
    rw [matrixLogLength_inv]
    have he : R/(2*(n:ℝ)*Real.exp (2*matrixLogLength a))=C*δ := by
      dsimp [R]
      field_simp [hnp.ne',Real.exp_ne_zero]
    rwa [he]
  simpa only [MulAut.conj_apply,inv_inv] using hm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CoverPredecessorPacking
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding predecessor covering labels after one diagonal step

A single small image cell pulls back to a uniformly small chart. The
separated-cover packing bound then controls its possible source labels.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem firstCover_predecessor_label_bound {n N : ℕ} (hn : 0 < n)
    (z : Fin N → X n) (c : Fin N → ℝ) (E : Set (X n)) (x : X n)
    (a : G n) {C D δ : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*predecessorPackingRadius n a C D*δ ≤ 1/2)
    (hsep : ∀ i j, i ≠ j → δ ≤ quotientLogDistance (z i) (z j))
    (hcover : ∀ y ∈ E, ∃ i, quotientLogDistance (z i) y < c i)
    (himage : ∀ y ∈ E, ∃ p ∈ matrixBall n (C*δ),
      rightAction (rightAction x a) p=rightAction y a)
    (hcell : ∀ i y, y ∈ E → quotientLogDistance (z i) y < c i →
      ∃ h ∈ matrixBall n (D*δ), rightAction y h=z i) :
    ∃ F : Finset (Fin (N+1)),
      (firstCoverCode (fun i => quotientLogDistance (z i)) c) '' E ⊆ F ∧
        (F.card:ℝ) ≤ localQuotientPackingBound n (predecessorPackingRadius n a C D) := by
  let A := 2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hK : 0 ≤ predecessorPackingRadius n a C D := by
    dsimp [predecessorPackingRadius]
    positivity
  apply firstCover_local_label_bound_of_lifts hn z c E x hK hδ hδ1 hsmall hsep hcover
  intro i hi
  obtain ⟨y,hy,hiy⟩ := hi
  obtain ⟨p,hp,hpa⟩ := himage y hy
  obtain ⟨h,hh,hyh⟩ := hcell i y hy hiy
  let q := a*p*a⁻¹
  have hq : q ∈ matrixBall n (A*δ) := by
    simpa only [inv_inv,matrixLogLength_inv,A,q] using
      matrixBall_right_translate_scaled hn a⁻¹ hC hδ hp
  have hxq : rightAction x q=y := by
    calc
      _ = rightAction (rightAction (rightAction x a) p) a⁻¹ := by
        change rightAction x (a*p*a⁻¹)=_
        simp only [rightAction_mul,mul_assoc]
      _ = rightAction (rightAction y a) a⁻¹ := by rw [hpa]
      _ = y := by rw [rightAction_mul,mul_inv_cancel,rightAction_one]
  refine ⟨q*h,?_,?_⟩
  · exact matrixBall_mul_scaled hA hD hδ hδ1 hq hh
  · rw [←rightAction_mul,hxq,hyh]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DistanceCutBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size bounds for the explicit quotient distance cuts -/

noncomputable section
namespace DukePrimeDegree

lemma half_le_log_one_add {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r/2 ≤ Real.log (1+r) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hr)
  apply (le_div_iff₀ (by linarith : 0 < r+2)).mpr
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ExponentialPredecessorScales
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform comparison of neighboring exponential chart radii -/

noncomputable section
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exponential_radius_adjacent {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    {k m : ℕ} (hkm : k ≤ m+1) :
    a*Real.exp (-B*(m:ℝ)) ≤ Real.exp B*(a*Real.exp (-B*(k:ℝ))) := by
  have hkmR : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have he : -B*(m:ℝ) ≤ B+ -B*(k:ℝ) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) ha
  rw [Real.exp_add] at hh
  calc
    _ ≤ a*(Real.exp B*Real.exp (-B*(k:ℝ))) := hh
    _ = _ := by ring

lemma exponential_cover_scale_bounds {a B : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (k : ℕ) :
    let r := a*Real.exp (-B*(k:ℝ))
    let δ := Real.log (1+r)/8
    0 < r ∧ r ≤ a ∧ 0 < δ ∧ δ ≤ a/8 ∧ r ≤ 16*δ := by
  dsimp only
  let r := a*Real.exp (-B*(k:ℝ))
  have hr : 0 < r := mul_pos ha (Real.exp_pos _)
  have hra : r ≤ a := by
    have he : Real.exp (-B*(k:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) k)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans_eq (mul_one a)
  have hr1 : r ≤ 1 := hra.trans ha1
  have hlogp : 0 < Real.log (1+r) := Real.log_pos (by linarith)
  have hlogle : Real.log (1+r) ≤ r := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+r by linarith)
    linarith
  have hlogge := half_le_log_one_add hr.le hr1
  change 0 < r ∧ r ≤ a ∧ 0 < Real.log (1+r)/8 ∧
    Real.log (1+r)/8 ≤ a/8 ∧ r ≤ 16*(Real.log (1+r)/8)
  exact ⟨hr,hra,by positivity,by linarith,by linarith⟩

lemma exponential_cover_image_radius {a B : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    {k m : ℕ} (hkm : k ≤ m+1) :
    a*Real.exp (-B*(m:ℝ)) ≤
      (16*Real.exp B)*(Real.log (1+a*Real.exp (-B*(k:ℝ)))/8) := by
  have hb := (exponential_cover_scale_bounds ha ha1 hB k).2.2.2.2
  calc
    _ ≤ Real.exp B*(a*Real.exp (-B*(k:ℝ))) := exponential_radius_adjacent ha.le hB hkm
    _ ≤ Real.exp B*(16*(Real.log (1+a*Real.exp (-B*(k:ℝ)))/8)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

lemma exponential_cover_smallness {n : ℕ} {a B K : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hsmall : (n:ℝ)*K*a ≤ 4) (k : ℕ) :
    (n:ℝ)*K*(Real.log (1+a*Real.exp (-B*(k:ℝ)))/8) ≤ 1/2 := by
  have hd := (exponential_cover_scale_bounds ha ha1 hB k).2.2.2.1
  have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg n) hK)
  nlinarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LayeredPredecessors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the three possible predecessor height levels -/

noncomputable section
open Set
namespace DukePrimeDegree

theorem uniformFinitePredecessors_of_height_layers {Y : Type*}
    (T : Y → Y) (H Q : Y → ℕ)
    (hstep : ∀ y, H (T y) ≤ H y+1 ∧ H y ≤ H (T y)+1)
    (hrefine : ∀ x y, Q y=Q x → H y=H x)
    (M : ℕ)
    (hlayer : ∀ q k : ℕ, ∃ F : Finset ℕ,
      Q '' {y | H y=k ∧ Q (T y)=q} ⊆ F ∧ F.card ≤ M) :
    UniformFinitePredecessors T Q := by
  classical
  refine ⟨3*M,?_⟩
  intro q
  by_cases he : ∃ x, Q (T x)=q
  · obtain ⟨x,hx⟩ := he
    let m := H (T x)
    choose F hF hcard using (hlayer q)
    let A := F (m-1) ∪ F m ∪ F (m+1)
    refine ⟨A,?_,?_⟩
    · rintro _ ⟨y,hy,rfl⟩
      have hyq : Q (T y)=q := hy
      have hym : H (T y)=m := hrefine (T x) (T y) (hyq.trans hx.symm)
      have hyk : H y=m-1 ∨ H y=m ∨ H y=m+1 := by
        have hs := hstep y
        dsimp [m] at hym ⊢
        omega
      rcases hyk with hyk | hyk | hyk
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact hF (m-1) ⟨y,⟨hyk,hyq⟩,rfl⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact hF m ⟨y,⟨hyk,hyq⟩,rfl⟩
      · apply Finset.mem_union_right
        exact hF (m+1) ⟨y,⟨hyk,hyq⟩,rfl⟩
    · have h₁ := Finset.card_union_le (F (m-1)) (F m)
      have h₂ := Finset.card_union_le (F (m-1) ∪ F m) (F (m+1))
      have hprev := hcard (m-1)
      have hm := hcard m
      have hnext := hcard (m+1)
      change (F (m-1) ∪ F m ∪ F (m+1)).card ≤ 3*M
      omega
  · refine ⟨∅,?_,by simp⟩
    rintro _ ⟨y,hy,_⟩
    exact (he ⟨y,hy⟩).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LayeredCoverPredecessors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite predecessor counts for geometric layered covers -/

noncomputable section
open Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem layered_cover_uniform_predecessors {n : ℕ} (hn : 0 < n)
    (a : G n) (H : X n → ℕ) (N : ℕ → ℕ)
    (z : ∀ k, Fin (N k) → X n) (c : ∀ k, Fin (N k) → ℝ)
    (r δ : ℕ → ℝ) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (hδ : ∀ k, 0 < δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hsmall : ∀ k, (n:ℝ)*predecessorPackingRadius n a C D*δ k ≤ 1/2)
    (hstep : ∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1)
    (hsource : ∀ k, r k ≤ D*δ k)
    (himage : ∀ x, r (H (rightAction x a)) ≤ C*δ (H x))
    (hsep : ∀ k i j, i ≠ j → δ k ≤ quotientLogDistance (z k i) (z k j))
    (hcut : ∀ k i, 0 < c k i)
    (hcover : ∀ k x, H x=k → ∃ i, quotientLogDistance (z k i) x < c k i)
    (hcell : ∀ k i x, quotientLogDistance (z k i) x < c k i →
      ∀ y, quotientLogDistance (z k i) y < c k i →
      ∃ g ∈ matrixBall n (r k), rightAction x g=y) :
    UniformFinitePredecessors (fun x => rightAction x a)
      (layeredObservation H (fun k => firstCoverCode (fun i => quotientLogDistance (z k i)) (c k))) := by
  classical
  let P := fun k => firstCoverCode (fun i => quotientLogDistance (z k i)) (c k)
  let Q := layeredObservation H P
  obtain ⟨M,hM⟩ := exists_nat_gt (localQuotientPackingBound n (predecessorPackingRadius n a C D))
  apply uniformFinitePredecessors_of_height_layers _ H Q hstep
    (fun _ _ he => (layeredObservation_eq H P he).1) M
  intro q k
  let E := {y : X n | H y=k ∧ Q (rightAction y a)=q}
  by_cases he : E.Nonempty
  · obtain ⟨x,hx⟩ := he
    have himg : ∀ y ∈ E, ∃ p ∈ matrixBall n (C*δ k),
        rightAction (rightAction x a) p=rightAction y a := by
      intro y hy
      have heq : P (H (rightAction x a)) (rightAction y a)=
          P (H (rightAction x a)) (rightAction x a) :=
        (layeredObservation_eq H P (hy.2.trans hx.2.symm)).2
      obtain ⟨i,hyi,hxi⟩ := firstCoverCode_common
        (fun i => quotientLogDistance (z (H (rightAction x a)) i))
        (c (H (rightAction x a))) (hcover _ _ rfl) heq
      obtain ⟨g,hg,hgy⟩ := hcell _ i _ hxi _ hyi
      refine ⟨g,matrixBall_mono ?_ hg,hgy⟩
      simpa only [hx.1] using himage x
    have hctr : ∀ i y, y ∈ E → quotientLogDistance (z k i) y < c k i →
        ∃ h ∈ matrixBall n (D*δ k), rightAction y h=z k i := by
      intro i y _ hiy
      obtain ⟨g,hg,hgz⟩ := hcell k i y hiy (z k i) (by
        simpa only [quotientLogDistance_self] using hcut k i)
      exact ⟨g,matrixBall_mono (hsource k) hg,hgz⟩
    obtain ⟨F,hF,hcard⟩ := firstCover_predecessor_label_bound hn (z k) (c k) E x a
      hC hD (hδ k) (hδ1 k) (hsmall k) (hsep k)
      (fun y hy => hcover k y hy.1) himg hctr
    refine ⟨F.image (fun u => Nat.pair k u.val),?_,?_⟩
    · rintro _ ⟨y,hy,rfl⟩
      have hyP : P k y ∈ F := hF ⟨y,hy,rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨P k y,hyP,?_⟩
      change Nat.pair k (P k y).val=Nat.pair (H y) (P (H y) y).val
      rw [hy.1]
    · have hc : F.card ≤ M := by exact_mod_cast (hcard.trans hM.le)
      exact (Finset.card_image_le).trans hc
  · refine ⟨∅,?_,by simp⟩
    rintro _ ⟨y,hy,_⟩
    exact (he ⟨y,hy⟩).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RadialHeightContinuity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local constancy of controlled radial heights

Only the adjacent radial cuts determine the height. Avoiding all cuts up
to the current height therefore makes the entire height itinerary locally
constant along uniformly contracting perturbations.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree

lemma cut_le_agrees_of_abs_sub_le {u v r ε : ℝ}
    (hnear : |u-v| ≤ ε) (haway : ε < |v-r|) :
    (u ≤ r ↔ v ≤ r) := by
  have hn := abs_le.mp hnear
  by_cases hvr : v ≤ r
  · rw [abs_of_nonpos (sub_nonpos.mpr hvr)] at haway
    have hur : u ≤ r := by linarith
    exact iff_of_true hur hvr
  · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hvr))] at haway
    have hur : ¬ u ≤ r := by linarith
    exact iff_of_false hur hvr

lemma height_eq_of_threshold_agreement {Y : Type*}
    (H : Y → ℕ) (f : Y → ℝ) (t : ℕ → ℝ)
    (hlevel : ∀ y m, H y ≤ m ↔ f y ≤ t m) {x y : Y}
    (heq : ∀ m ≤ H x, f y ≤ t m ↔ f x ≤ t m) : H y=H x := by
  apply le_antisymm
  · exact (hlevel y (H x)).mpr ((heq _ le_rfl).mpr ((hlevel x _).mp le_rfl))
  · by_cases hx : H x=0
    · omega
    · have hprev : ¬ f x ≤ t (H x-1) := by
        intro h
        have := (hlevel x _).mpr h
        omega
      have hy : ¬ H y ≤ H x-1 := by
        intro h
        exact hprev ((heq _ (Nat.sub_le _ _)).mp ((hlevel y _).mp h))
      omega

lemma eventually_radial_height_eq {Y : Type*} [TopologicalSpace Y]
    (H : Y → ℕ) (f : Y → ℝ) (t : ℕ → ℝ)
    (hlevel : ∀ y m, H y ≤ m ↔ f y ≤ t m) {x : Y}
    (hf : ContinuousAt f x) (hboundary : ∀ m, f x≠t m) :
    ∀ᶠ y in 𝓝 x, H y=H x := by
  have hfinite (m : Fin (H x+1)) :
      ∀ᶠ y in 𝓝 x, f y ≤ t m.val ↔ f x ≤ t m.val := by
    rcases lt_or_gt_of_ne (hboundary m.val) with hlt | hgt
    · exact (hf.eventually (gt_mem_nhds hlt)).mono fun y hy => iff_of_true hy.le hlt.le
    · exact (hf.eventually (lt_mem_nhds hgt)).mono fun y hy =>
        iff_of_false (not_le.mpr hy) (not_le.mpr hgt)
  filter_upwards [Filter.eventually_all.mpr hfinite] with y hy
  apply height_eq_of_threshold_agreement H f t hlevel
  intro m hm
  exact hy ⟨m,by omega⟩

theorem eventually_radial_height_itinerary_eq
    {Y V : Type*} [TopologicalSpace Y] [TopologicalSpace V]
    {T : Y → Y} (hT : Continuous T) (H : Y → ℕ) (f : Y → ℝ) (t : ℕ → ℝ)
    (hlevel : ∀ y m, H y ≤ m ↔ f y ≤ t m) (hf : Continuous f)
    {F : V → Y} {v₀ : V} (hF : ContinuousAt F v₀)
    (ε : ℕ → ℝ)
    (hboundary : ∀ k m, f (T^[k] (F v₀))≠t m)
    (havoid : ∀ᶠ k : ℕ in atTop, ∀ m ≤ H (T^[k] (F v₀)),
      ε k < |f (T^[k] (F v₀))-t m|)
    (U : Set V) (hU : U ∈ 𝓝 v₀)
    (hcontract : ∀ k : ℕ, ∀ v ∈ U,
      |f (T^[k] (F v))-f (T^[k] (F v₀))| ≤ ε k) :
    ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ, H (T^[k] (F v))=H (T^[k] (F v₀)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp havoid
  have hfinite (k : Fin N) : ∀ᶠ v in 𝓝 v₀,
      H (T^[k.val] (F v))=H (T^[k.val] (F v₀)) := by
    have hcont : ContinuousAt (fun v => T^[k.val] (F v)) v₀ :=
      (hT.iterate k.val).continuousAt.comp hF
    exact hcont.eventually (eventually_radial_height_eq H f t hlevel
      hf.continuousAt (hboundary k.val))
  filter_upwards [Filter.eventually_all.mpr hfinite,hU] with v hv hvU
  intro k
  by_cases hk : k < N
  · exact hv ⟨k,hk⟩
  · apply height_eq_of_threshold_agreement H f t hlevel
    intro m hm
    exact cut_le_agrees_of_abs_sub_le (hcontract k v hvU)
      (hN k (le_of_not_gt hk) m hm)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_VaryingCutItinerary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Locally constant future cuts at a varying height -/

noncomputable section
open Set Filter
open scoped Topology
namespace DukePrimeDegree

theorem eventually_varying_cut_itinerary_eq
    {Y V : Type*} [TopologicalSpace Y] [TopologicalSpace V]
    {T : Y → Y} (hT : Continuous T) (H : Y → ℕ)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Continuous (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    {F : V → Y} {v₀ : V} (hF : ContinuousAt F v₀)
    (ε : ℕ → ℝ)
    (hboundary : ∀ k m i, f m i (T^[k] (F v₀))≠c m i)
    (havoid : ∀ᶠ k : ℕ in atTop, ∀ m ≤ H (T^[k] (F v₀)), ∀ i,
      ε k < |f m i (T^[k] (F v₀))-c m i|)
    (U : Set V) (hU : U ∈ 𝓝 v₀)
    (hcontract : ∀ k m i, ∀ v ∈ U,
      |f m i (T^[k] (F v))-f m i (T^[k] (F v₀))| ≤ ε k) :
    ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ, ∀ i : Fin (N (H (T^[k] (F v₀)))),
      f (H (T^[k] (F v₀))) i (T^[k] (F v)) < c (H (T^[k] (F v₀))) i ↔
        f (H (T^[k] (F v₀))) i (T^[k] (F v₀)) < c (H (T^[k] (F v₀))) i := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp havoid
  have hfinite (k : Fin M) : ∀ᶠ v in 𝓝 v₀,
      ∀ i : Fin (N (H (T^[k.val] (F v₀)))),
      f (H (T^[k.val] (F v₀))) i (T^[k.val] (F v)) < c (H (T^[k.val] (F v₀))) i ↔
        f (H (T^[k.val] (F v₀))) i (T^[k.val] (F v₀)) < c (H (T^[k.val] (F v₀))) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt
        (fun v => f (H (T^[k.val] (F v₀))) i (T^[k.val] (F v))) v₀ :=
      ((hf _ _).comp (hT.iterate k.val)).continuousAt.comp hF
    rcases lt_or_gt_of_ne (hboundary k.val _ i) with hlt | hgt
    · exact (hc.eventually (gt_mem_nhds hlt)).mono fun _ hv => iff_of_true hv hlt
    · exact (hc.eventually (lt_mem_nhds hgt)).mono fun _ hv =>
        iff_of_false (not_lt.mpr hv.le) (not_lt.mpr hgt.le)
  filter_upwards [Filter.eventually_all.mpr hfinite,hU] with v hv hvU
  intro k i
  by_cases hk : k < M
  · exact hv ⟨k,hk⟩ i
  · exact cut_agrees_of_abs_sub_le (hcontract k _ i v hvU)
      (hM k (le_of_not_gt hk) _ le_rfl i)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ExponentialLevelBudget
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable boundary budgets for slowly growing levels -/

noncomputable section
open scoped BigOperators
namespace DukePrimeDegree

lemma sum_exp_nat_le {C : ℝ} (hC : 0 ≤ C) (M : ℕ) :
    (∑ m ∈ Finset.range (M+1), Real.exp (C*(m:ℝ))) ≤
      (M+1:ℝ)*Real.exp (C*(M:ℝ)) := by
  calc
    _ ≤ ∑ _m ∈ Finset.range (M+1), Real.exp (C*(M:ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hC
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    _ = _ := by simp

lemma summable_linear_mul_exp {a : ℝ} (ha : a < 0) :
    Summable (fun k : ℕ => ((k:ℝ)+1)*Real.exp (a*(k:ℝ))) := by
  have hr : ‖Real.exp a‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr ha
  have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    (summable_geometric_of_norm_lt_one hr)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext k
  rw [mul_comm a (k:ℝ),Real.exp_nat_mul]
  simp only [pow_one]
  ring

theorem summable_exponential_level_budget
    (L : ℕ → ℕ) {C δ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hL : ∀ k, (L k:ℝ) ≤ δ*(k:ℝ)) (hdecay : C*δ < Real.log 2) :
    Summable (fun k : ℕ =>
      (∑ m ∈ Finset.range (L k+1), K*Real.exp (C*(m:ℝ)))*(1/2:ℝ)^k) := by
  have hsum := (summable_linear_mul_exp (sub_neg.mpr hdecay)).mul_left
    (K*max δ 1)
  apply Summable.of_nonneg_of_le (fun k =>
    mul_nonneg (Finset.sum_nonneg (fun m _ =>
      mul_nonneg hK (Real.exp_pos _).le)) (by positivity)) _ hsum
  intro k
  have hexp : Real.exp (C*(L k:ℝ)) ≤ Real.exp (C*δ*(k:ℝ)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ C*(δ*(k:ℝ)) := mul_le_mul_of_nonneg_left (hL k) hC
      _ = _ := by ring
  have hcount : (L k+1:ℝ) ≤ max δ 1*((k:ℝ)+1) := by
    have h₁ := mul_le_mul_of_nonneg_right (le_max_left δ 1) (Nat.cast_nonneg (α := ℝ) k)
    have h₂ := le_max_right δ 1
    nlinarith [hL k]
  have hbase : (1/2:ℝ)^k=Real.exp (-Real.log 2*(k:ℝ)) := by
    rw [mul_comm (-Real.log 2) (k:ℝ),Real.exp_nat_mul,
      Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    simp only [one_div]
  calc
    _ ≤ (K*((L k+1:ℝ)*Real.exp (C*(L k:ℝ))))*(1/2:ℝ)^k := by
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sum_exp_nat_le hC (L k)) hK) (by positivity)
    _ ≤ (K*(max δ 1*((k:ℝ)+1)*Real.exp (C*δ*(k:ℝ))))*(1/2:ℝ)^k := by
      gcongr
    _ = _ := by
      rw [hbase]
      have he : Real.exp (C*δ*(k:ℝ))*Real.exp (-Real.log 2*(k:ℝ)) =
          Real.exp ((C*δ-Real.log 2)*(k:ℝ)) := by rw [←Real.exp_add]; congr 1; ring
      calc
        _ = K*max δ 1*((k:ℝ)+1)*
            (Real.exp (C*δ*(k:ℝ))*Real.exp (-Real.log 2*(k:ℝ))) := by ring
        _ = _ := by rw [he]; ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_VaryingCutBoundary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary avoidance across changing finite levels

The union bound and Borel--Cantelli apply to all cuts up to a level that
changes with time. The summability hypothesis is an explicit numerical
budget; no entropy or subordinate-partition conclusion is assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace DukePrimeDegree

theorem ae_eventually_avoid_varying_cut_levels
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Measurable (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (L : ℕ → ℕ) (ε : ℕ → ℝ) (B : ℕ → ℕ → ℝ≥0∞)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) (ε k)) ≤ B m k)
    (hbudget : (∑' k, ∑ m ∈ Finset.range (L k+1), (N m:ℝ≥0∞)*B m k) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ m ≤ L k, ∀ i,
      ε k < |f m i (T^[k] x)-c m i| := by
  classical
  let S (k : ℕ) : Set Y := ⋃ m ∈ Finset.range (L k+1), ⋃ i : Fin (N m),
    (T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)
  have hpre (k m : ℕ) (i : Fin (N m)) :
      μ ((T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)) ≤ B m k := by
    rw [(hT.iterate k).measure_preimage
      (realBoundaryStrip_measurableSet (hf m i) _ _).nullMeasurableSet]
    exact hbound m i k
  have hS (k : ℕ) : μ (S k) ≤ ∑ m ∈ Finset.range (L k+1), (N m:ℝ≥0∞)*B m k := by
    calc
      _ ≤ ∑ m ∈ Finset.range (L k+1), μ (⋃ i : Fin (N m),
          (T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.range (L k+1), ∑ i : Fin (N m),
          μ ((T^[k]) ⁻¹' realBoundaryStrip (f m i) (c m i) (ε k)) :=
        Finset.sum_le_sum fun m _ => measure_iUnion_fintype_le _ _
      _ ≤ ∑ m ∈ Finset.range (L k+1), ∑ _i : Fin (N m), B m k :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun i _ => hpre k m i
      _ = _ := by simp
  have hsum : (∑' k, μ (S k)) ≠ ∞ :=
    ne_top_of_le_ne_top hbudget (ENNReal.tsum_le_tsum hS)
  filter_upwards [ae_eventually_notMem (μ := μ) (s := S) hsum] with x hx
  filter_upwards [hx] with k hk
  intro m hm i
  apply lt_of_not_ge
  intro hbad
  apply hk
  exact mem_iUnion₂.mpr ⟨m,Finset.mem_range.mpr (by omega),
    mem_iUnion.mpr ⟨i,hbad⟩⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ExponentialCutBoundary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary avoidance for exponentially sized families of cuts -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace DukePrimeDegree

theorem ae_eventually_avoid_exponential_cut_levels
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Measurable (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D m*(1/2:ℝ)^k))
    (L : ℕ → ℕ) {C δ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : ∀ m, (N m:ℝ≥0∞)*ENNReal.ofReal (D m) ≤
      ENNReal.ofReal (K*Real.exp (C*(m:ℝ))))
    (hL : ∀ k, (L k:ℝ) ≤ δ*(k:ℝ)) (hdecay : C*δ < Real.log 2) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ m ≤ L k, ∀ i,
      (1/4:ℝ)^k < |f m i (T^[k] x)-c m i| := by
  apply ae_eventually_avoid_varying_cut_levels μ hT N f hf c L
    (fun k => (1/4:ℝ)^k) (fun m k => ENNReal.ofReal (D m*(1/2:ℝ)^k)) hbound
  have hsum := (summable_exponential_level_budget L hC hK hL hdecay).tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hsum
  apply ENNReal.tsum_le_tsum
  intro k
  calc
    _ ≤ ∑ m ∈ Finset.range (L k+1),
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ))*(1/2:ℝ)^k) := by
      apply Finset.sum_le_sum
      intro m _
      rw [ENNReal.ofReal_mul (hD m),←mul_assoc,
        ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      exact mul_le_mul' (hsize m) le_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity),
        ←Finset.sum_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TemperedCutBoundary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary avoidance up to the actual orbit height

The proper height grows sublinearly without an integrability assumption.
It is therefore eventually below a sufficiently slow linear cutoff,
where the exponential boundary budget is summable.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DukePrimeDegree

theorem ae_eventually_avoid_cuts_up_to_height
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Measurable (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D m*(1/2:ℝ)^k))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : ∀ m, (N m:ℝ≥0∞)*ENNReal.ofReal (D m) ≤
      ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ m ≤ H (T^[k] x), ∀ i,
      (1/4:ℝ)^k < |f m i (T^[k] x)-c m i| := by
  let δ := Real.log 2/(2*(C+1))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCp : 0 < C+1 := by linarith
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hdecay : C*δ < Real.log 2 := by
    calc
      _ ≤ (C+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = Real.log 2/2 := by dsimp [δ]; field_simp
      _ < _ := by linarith
  let L (k : ℕ) := ⌊δ*(k:ℝ)⌋₊
  have hL (k : ℕ) : (L k:ℝ) ≤ δ*(k:ℝ) := Nat.floor_le (by positivity)
  have havoid := ae_eventually_avoid_exponential_cut_levels μ hT N f hf c D hD hbound
    L hC hK hsize hL hdecay
  filter_upwards [havoid,ae_height_div_tendsto_zero μ hT H hH hstep] with x hx hsub
  filter_upwards [hx,hsub.eventually (gt_mem_nhds hδ),eventually_ge_atTop 1]
    with k hk hsmall hkp
  have hkp' : 0 < (k:ℝ) := by exact_mod_cast hkp
  have hheight : H (T^[k] x) ≤ L k := by
    apply Nat.le_floor
    exact ((div_lt_iff₀ hkp').mp hsmall).le
  intro m hm i
  exact hk m (hm.trans hheight) i

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CountableCutNeighborhoods
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neighborhoods in countable future atoms from controlled cuts

The actual orbit height selects a finite family of cuts at each time.
Their exponential boundary budget and the radial height budget
make the whole countable future observation locally constant along a
uniformly contracting continuous family.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace DukePrimeDegree

theorem ae_layered_cut_future_neighborhoods
    {Y V : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [TopologicalSpace V] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hTc : Continuous T)
    (H : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    (f₀ : Y → ℝ) (hf₀ : Continuous f₀) (t : ℕ → ℝ)
    (hlevel : ∀ x m, H x ≤ m ↔ f₀ x ≤ t m)
    (hnull₀ : ∀ m, μ {x | f₀ x=t m}=0)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hbound₀ : ∀ m k, μ (realBoundaryStrip f₀ (t m) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D₀*(1/2:ℝ)^k))
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Continuous (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (hnull : ∀ m i, μ {x | f m i x=c m i}=0)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D m*(1/2:ℝ)^k))
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : ∀ m, (N m:ℝ≥0∞)*ENNReal.ofReal (D m) ≤
      ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) :
    ∀ᵐ x ∂μ, ∀ (F : V → Y) (v₀ : V), F v₀=x → ContinuousAt F v₀ →
      ∀ U ∈ 𝓝 v₀,
      (∀ k v, v ∈ U → |f₀ (T^[k] (F v))-f₀ (T^[k] x)| ≤ (1/4:ℝ)^k) →
      (∀ k m i v, v ∈ U → |f m i (T^[k] (F v))-f m i (T^[k] x)| ≤ (1/4:ℝ)^k) →
      ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
        layeredObservation H (fun m => finiteCutCode (f m) (c m)) (T^[k] (F v)) =
          layeredObservation H (fun m => finiteCutCode (f m) (c m)) (T^[k] x) := by
  have hradial := ae_eventually_avoid_cuts_up_to_height μ hT H hH hstep
    (fun _ => 1) (fun _ _ => f₀) (fun _ _ => hf₀.measurable) (fun m _ => t m)
    (fun _ => D₀) (fun _ => hD₀) (fun m _ k => hbound₀ m k)
    (C := 0) (K := D₀) (by norm_num) hD₀ (by intro m; simp)
  have hcuts := ae_eventually_avoid_cuts_up_to_height μ hT H hH hstep
    N f (fun m i => (hf m i).measurable) c D hD hbound hC hK hsize
  have hn₀ : ∀ᵐ x ∂μ, ∀ m k, f₀ (T^[k] x)≠t m :=
    ae_all_iff.mpr fun m => ae_avoid_cut_boundary_at_all_times μ hT (t m) (hnull₀ m)
  have hn : ∀ᵐ x ∂μ, ∀ m i k, f m i (T^[k] x)≠c m i :=
    ae_all_iff.mpr fun m => ae_all_iff.mpr fun i =>
      ae_avoid_cut_boundary_at_all_times μ hT (c m i) (hnull m i)
  filter_upwards [hradial,hcuts,hn₀,hn] with x hx₀ hx hxn₀ hxn
  intro F v₀ hbase hF U hU hc₀ hc
  have hheight := eventually_radial_height_itinerary_eq hTc H f₀ t hlevel hf₀ hF
    (fun k => (1/4:ℝ)^k)
    (by intro k m; simpa only [hbase] using hxn₀ m k)
    (by simpa only [hbase] using hx₀.mono (fun k hk m hm => hk m hm 0)) U hU
    (by intro k v hv; simpa only [hbase] using hc₀ k v hv)
  have hlabels := eventually_varying_cut_itinerary_eq hTc H N f hf c hF
    (fun k => (1/4:ℝ)^k)
    (by intro k m i; simpa only [hbase] using hxn m i k)
    (by simpa only [hbase] using hx) U hU
    (by intro k m i v hv; simpa only [hbase] using hc k m i v hv)
  have hcodes : ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
      finiteCutCode (f (H (T^[k] (F v₀)))) (c (H (T^[k] (F v₀)))) (T^[k] (F v)) =
        finiteCutCode (f (H (T^[k] (F v₀)))) (c (H (T^[k] (F v₀)))) (T^[k] (F v₀)) := by
    filter_upwards [hlabels] with v hv
    intro k
    exact finiteCutCode_eq_of_iff _ _ (hv k)
  simpa only [hbase] using layeredObservation_future_eq H
    (fun m => finiteCutCode (f m) (c m)) T F v₀ hheight hcodes

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BranchingCoverFuture
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A future observation with uniformly finite predecessor sets

The same distance cuts give future neighborhoods and a finite branching
bound. The chart radius is chosen small enough for uniform local packing.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_branching_cover_future_observation_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (B : ℝ) (hB : 0 < B) (H : X (d+1) → ℕ) (hH : Measurable H)
    (t : ℕ → ℝ)
    (ht : ∀ m, t m ≤ 2*B*(m:ℝ)+B)
    (hlevel : ∀ x m, H x ≤ m ↔
      quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ t m)
    (hstep : ∀ x, H (rightAction x (diagonalOneParameter ell hell (-1))) ≤ H x+1 ∧
      H x ≤ H (rightAction x (diagonalOneParameter ell hell (-1)))+1)
    (hnull : ∀ m, μ {x | quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x=t m}=0)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hbound : ∀ m k, μ (realBoundaryStrip
      (quotientLogDistance (Quotient.mk _ (1 : G (d+1)))) (t m) ((1/4:ℝ)^k)) ≤
        ENNReal.ofReal (D₀*(1/2:ℝ)^k))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hpack : ((d+1:ℕ):ℝ)*predecessorPackingRadius (d+1)
      (diagonalOneParameter ell hell (-1)) (16*Real.exp (4*B)) 16*r₀ ≤ 4) :
    ∃ Q : X (d+1) → ℕ, Measurable Q ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ x y, Q y=Q x → H y=H x ∧
        ∃ g ∈ matrixBall (d+1) (r₀*Real.exp (-(4*B)*(H x:ℝ))), rightAction x g=y) ∧
      (∀ᵐ x ∂μ, ∀ᶠ s in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k]
          (rightAction x ((completeRootChain (d+1)).word s))) =
        Q ((fun y => rightAction y (diagonalOneParameter ell hell (-1)))^[k] x)) ∧
      UniformFinitePredecessors
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q ∧
      ∃ (J : ℕ → ℕ) (K C : ℝ), 0 < K ∧ 0 ≤ C ∧
        (∀ m, (J m : ℝ) ≤ K*Real.exp (C*(m:ℝ))) ∧
        ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m) := by
  classical
  let T : X (d+1) → X (d+1) := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    change μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1)))=μ
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  let r := fun m : ℕ => r₀*Real.exp (-(4*B)*(m:ℝ))
  let τ := fun m => Real.log (1+r m)
  have hτ (m : ℕ) : 0 < τ m := by
    have hr : 0 < r m := by dsimp [r] <;> positivity
    exact Real.log_pos (by linarith)
  obtain ⟨N,z,c,K,C,hK,hC,hfamily⟩ := exists_separated_exponential_cut_family
    (Nat.succ_pos d) μ (A := 2*B) (B := 4*B) (R₀ := B)
    (by positivity) (by positivity) hB.le hr₀ hr₀1
  let f : ∀ m, Fin (N m) → X (d+1) → ℝ := fun m i => quotientLogDistance (z m i)
  let P := fun m => firstCoverCode (f m) (c m)
  let Q := layeredObservation H P
  have hP (m : ℕ) : Measurable (P m) :=
    firstCoverCode_measurable (fun i => (continuous_quotientLogDistance (d+1) _).measurable) _
  refine ⟨Q,layeredObservation_measurable hH hP,layeredObservation_finite_levels H P,?_,?_,?_,?_⟩
  · intro x y hxy
    have he := layeredObservation_eq H P hxy
    refine ⟨he.1,?_⟩
    have hx : quotientLogDistance (Quotient.mk _ (1 : G (d+1))) x ≤ 2*B*(H x:ℝ)+B :=
      ((hlevel x (H x)).mp le_rfl).trans (ht (H x))
    obtain ⟨i,hy,hi⟩ := firstCoverCode_common (f (H x)) (c (H x))
      ((hfamily (H x)).2.2.2.1 x hx) he.2
    exact (hfamily (H x)).2.2.2.2 i x hi y hy
  · have hneigh := ae_layered_cut_future_neighborhoods (V := UpperRootTime (d+1)) μ hT
      (continuous_rightAction _) H hH (fun x => (hstep x).1)
      (quotientLogDistance (Quotient.mk _ (1 : G (d+1))))
      (continuous_quotientLogDistance (d+1) _) t hlevel hnull
      hD₀ hbound N f
      (fun m i => continuous_quotientLogDistance (d+1) _) c
      (fun m i => ((hfamily m).2.2.1 i).2.2.1)
      (fun m => 48/τ m) (fun m => div_nonneg (by norm_num) (hτ m).le)
      (fun m i k => ((hfamily m).2.2.1 i).2.2.2 k) hC hK.le (fun m => (hfamily m).1)
    filter_upwards [hneigh] with x hx
    let F : UpperRootTime (d+1) → X (d+1) :=
      fun s => rightAction x ((completeRootChain (d+1)).word s)
    have hbase : F (completeRootChain (d+1)).zeroTime=x := by
      simp only [F,EliminationChain.word_zeroTime,rightAction_one]
    have hF : ContinuousAt F (completeRootChain (d+1)).zeroTime :=
      ((continuous_rightOrbit (d+1) x).comp (upperRootWord_isEmbedding (d+1)).continuous).continuousAt
    let R : ℝ := 1/(6*(d+1:ℝ))
    have hR : 0 < R := by dsimp [R] <;> positivity
    have hsmall : 3*(d+1:ℝ)*R ≤ 1 := by
      dsimp [R]
      have hn : (d+1:ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have he (k : ℕ) : Real.exp (-Real.log 4*(k:ℝ))=(1/4:ℝ)^k := by
      rw [mul_comm (-Real.log 4) (k:ℝ),Real.exp_nat_mul,
        Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)]
      simp only [one_div]
    have hc (w : X (d+1)) (k : ℕ) (s : UpperRootTime (d+1))
        (hs : s ∈ (completeRootChain (d+1)).cube R) :
        |quotientLogDistance w (T^[k] (F s))-quotientLogDistance w (T^[k] x)| ≤ (1/4:ℝ)^k := by
      exact (quotientLogDistance_upperRoot_iterate_bound ell hell (Real.log 4)
        hlog hgap hR hsmall w x k hs).trans_eq (he k)
    have hn := hx F (completeRootChain (d+1)).zeroTime hbase hF _
      (((completeRootChain (d+1)).cube_open R).mem_nhds
        ((completeRootChain (d+1)).zeroTime_mem_cube hR))
      (fun k s hs => hc _ k s hs) (fun k m i s hs => hc _ k s hs)
    filter_upwards [hn] with s hs
    intro k
    exact layered_firstCover_eq_of_cutCode_eq H f c (hs k)

  · have hsc (m : ℕ) := exponential_cover_scale_bounds hr₀ hr₀1
      (show 0 ≤ 4*B by positivity) m
    have hKP : 0 ≤ predecessorPackingRadius (d+1)
        (diagonalOneParameter ell hell (-1)) (16*Real.exp (4*B)) 16 := by
      dsimp [predecessorPackingRadius]
      positivity
    apply layered_cover_uniform_predecessors (Nat.succ_pos d)
      (diagonalOneParameter ell hell (-1)) H N z c r (fun m => τ m/8)
      (by positivity) (by norm_num) (fun m => (hsc m).2.2.1)
      (fun m => (hsc m).2.2.2.1.trans (by linarith))
      (fun m => exponential_cover_smallness hr₀ hr₀1 (by positivity) hKP hpack m)
      hstep (fun m => (hsc m).2.2.2.2) ?_ ?_ ?_ ?_ ?_
    · intro x
      exact exponential_cover_image_radius hr₀ hr₀1 (by positivity) (hstep x).2
    · intro m i j hij
      exact ((hfamily m).2.1 i j hij).le
    · intro m i
      have hh := ((hfamily m).2.2.1 i).1
      exact lt_trans (by have := hτ m; positivity) hh
    · intro m x hx
      apply (hfamily m).2.2.2.1 x
      have hh := ((hlevel x m).mp (by omega)).trans (ht m)
      exact hh
    · exact fun m => (hfamily m).2.2.2.2
  · refine ⟨fun m => N m+1,K+1,C,by linarith,hC,?_,?_⟩
    · intro m
      have hr : 0 < r m := by dsimp [r] <;> positivity
      have hrle : r m ≤ 1 := by
        dsimp [r]
        have he : Real.exp (-(4*B)*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
          nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (α := ℝ) m)])
        exact (mul_le_mul_of_nonneg_left he hr₀.le).trans (by simpa using hr₀1)
      have hlog : τ m ≤ 1 := by
        have hh := Real.log_le_sub_one_of_pos (show 0 < 1+r m by linarith)
        dsimp [τ]
        linarith
      have hfactor : 1 ≤ 48/τ m := (le_div_iff₀ (hτ m)).mpr (by linarith)
      have hb := (hfamily m).1
      change (N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ))) at hb
      have hraw := ENNReal.toReal_mono (by finiteness) hb
      have hd : 0 ≤ (48/τ m:ℝ) := div_nonneg (by norm_num) (hτ m).le
      have hk : 0 ≤ K*Real.exp (C*(m:ℝ)) := mul_nonneg hK.le (Real.exp_pos _).le
      rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hd,ENNReal.toReal_ofReal hk] at hraw
      have hn : (N m:ℝ) ≤ K*Real.exp (C*(m:ℝ)) :=
        (le_mul_of_one_le_right (Nat.cast_nonneg _) hfactor).trans hraw
      have he : 1 ≤ Real.exp (C*(m:ℝ)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hC (Nat.cast_nonneg _))
      push_cast
      nlinarith
    · intro m q hq
      obtain ⟨x,hx,rfl⟩ := hq
      change H x=m at hx
      refine ⟨(P m x).val,(P m x).isLt,?_⟩
      dsimp [Q,layeredObservation]
      rw [hx]

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_branching_cover_future_observation_oai := @OAI.DukePrimeDegree.exists_branching_cover_future_observation_oai
