-- Prove2me | solution 1 for OAI.DukePrimeDegree.EliminationChain.predecessor_root_information
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:08.755591+00:00
-- url     : https://prove2.me/submissions/a3eaf248-f9e0-4027-b000-2d2dc0084de5

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
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke024
import Theorems.Thm_OAI_DukePrimeDegree_EliminationChain_wholeFuture_conditionalInformation_integrable_integral

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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

open MeasureTheory ProbabilityTheory Filter Set
namespace PrimeDegreePackets

variable {Z Y ι : Type*} [MeasurableSpace Z] [MeasurableSpace Y]



lemma measurable_kernel_real (κ : Kernel Z Y) {S : Set Y} (hS : MeasurableSet S) :
    Measurable (fun z => (κ z).real S) := (κ.measurable_coe hS).ennreal_toReal

lemma integrable_kernel_real (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z Y) [IsMarkovKernel κ] {S : Set Y} (hS : MeasurableSet S) :
    Integrable (fun z => (κ z).real S) τ := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (measurable_kernel_real κ hS).aestronglyMeasurable ?_
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma continuous_finiteShannon {α : Type*} [Fintype α] :
    Continuous (finiteShannon (α := α)) := by
  unfold finiteShannon
  exact continuous_finsetSum _ (fun a _ => Real.continuous_negMulLog.comp (continuous_apply a))

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_DisintegrationEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional information in disintegration coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace PrimeDegreePackets

variable {S T α : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [StandardBorelSpace T] [Nonempty T] [Fintype α]

omit [StandardBorelSpace T] [Nonempty T] in
lemma measurable_fiber_observationEntropy (κ : Kernel S T) [IsMarkovKernel κ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    Measurable (fun s => observationEntropy (κ s) (fun t => P (s,t))) := by
  apply continuous_finiteShannon.measurable.comp
  apply measurable_pi_iff.mpr
  intro a
  exact (Kernel.measurable_kernel_prodMk_left (κ := κ) (hP a)).ennreal_toReal

omit [Fintype α] in
lemma condExp_fst_observation_probability
    (μ : Measure (S × T)) [IsFiniteMeasure μ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z = a}) (a : α) :
    μ[({z | P z = a}.indicator (fun _ => (1 : ℝ))) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)] =ᵐ[μ]
      fun z => (μ.condKernel z.1).real {t | P (z.1,t) = a} := by
  let f : S × T → ℝ := {z | P z = a}.indicator (fun _ => 1)
  have hid : (fun z : S × T => (z.1,z.2)) = id := rfl
  have hf : Integrable f (μ.map (fun z : S × T => (z.1,z.2))) := by
    rw [hid, Measure.map_id]
    exact (integrable_const (1 : ℝ)).indicator (hP a)
  have H := condExp_prod_ae_eq_integral_condDistrib'
    (μ := μ) (X := (Prod.fst : S × T → S)) (Y := (Prod.snd : S × T → T))
    measurable_fst measurable_snd.aemeasurable hf
  have hκ : condDistrib (Prod.snd : S × T → T) Prod.fst μ = μ.condKernel := by
    simp only [condDistrib, hid, Measure.map_id]
  rw [hκ] at H
  have hI (s : S) : (∫ t, f (s,t) ∂μ.condKernel s) =
      (μ.condKernel s).real {t | P (s,t) = a} := by
    change (∫ t, {t | P (s,t) = a}.indicator (fun _ => (1 : ℝ)) t ∂μ.condKernel s) = _
    have hs : MeasurableSet {t | P (s,t) = a} := (hP a).preimage measurable_prodMk_left
    rw [integral_indicator_const _ hs]
    simp only [smul_eq_mul, mul_one]
  simpa only [Prod.eta, hI] using H

theorem conditionalSigmaEntropy_fst
    (μ : Measure (S × T)) [IsFiniteMeasure μ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z = a}) :
    conditionalSigmaEntropy μ P
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)) =
      ∫ s, observationEntropy (μ.condKernel s) (fun t => P (s,t)) ∂μ.fst := by
  have H := ae_all_iff.mpr (fun a => condExp_fst_observation_probability μ P hP a)
  unfold conditionalSigmaEntropy
  calc
    _ = ∫ z, observationEntropy (μ.condKernel z.1) (fun t => P (z.1,t)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [H] with z hz
      unfold observationEntropy
      congr 1
      exact funext hz
    _ = _ := by
      exact (integral_map measurable_fst.aemeasurable
        (measurable_fiber_observationEntropy μ.condKernel P hP).aestronglyMeasurable).symm

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ObservationInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

lemma measurable_kernel_observationInformation {S T α : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [Fintype α]
    (κ : Kernel S T) [IsMarkovKernel κ] (P : S × T → α)
    (hP : ∀ a, MeasurableSet {z | P z=a}) :
    Measurable (fun z : S × T => observationInformation (κ z.1) (fun t => P (z.1,t)) z.2) := by
  classical
  have he (z : S × T) :
      observationInformation (κ z.1) (fun t => P (z.1,t)) z.2 =
        ∑ a, {z | P z=a}.indicator
          (fun z => -Real.log ((κ z.1).real {t | P (z.1,t)=a})) z := by
    rw [Finset.sum_eq_single (P z)]
    · simp [observationInformation]
    · intro a _ ha
      exact indicator_of_notMem (show z ∉ {z | P z=a} from Ne.symm ha) _
    · simp
  simp_rw [he]
  apply Finset.measurable_sum
  intro a _
  have hm := (Kernel.measurable_kernel_prodMk_left (κ := κ) (hP a)).ennreal_toReal
  exact (hm.log.neg.comp measurable_fst).indicator (hP a)

theorem integrable_kernel_observationInformation {S T α : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [Fintype α]
    (σ : Measure S) [IsFiniteMeasure σ] (κ : Kernel S T) [IsMarkovKernel κ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z=a}) :
    Integrable (fun z : S × T => observationInformation (κ z.1) (fun t => P (z.1,t)) z.2)
      (σ ⊗ₘ κ) := by
  apply (Measure.integrable_compProd_iff
    (measurable_kernel_observationInformation κ P hP).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun s => observationInformation_integrable (κ s) _
      (fun a => (hP a).preimage measurable_prodMk_left)
  · have he (s : S) :
        (∫ t, ‖observationInformation (κ s) (fun t => P (s,t)) t‖ ∂κ s) =
          observationEntropy (κ s) (fun t => P (s,t)) := by
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (observationInformation_nonneg (κ s) _ _)]
      exact integral_observationInformation (κ s) _
        (fun a => (hP a).preimage measurable_prodMk_left)
    simp_rw [he]
    apply (integrable_const (Fintype.card α : ℝ)).mono'
      (measurable_fiber_observationEntropy κ P hP).aestronglyMeasurable
    exact ae_of_all _ fun s => finiteShannon_norm_le_card_of_unit_bounds _
      (fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩)

theorem conditionalEntropy_fst_information {S T α : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T] [Fintype α]
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z=a}) :
    conditionalSigmaEntropy ρ P
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)) =
      ∫ z, observationInformation (ρ.condKernel z.1) (fun t => P (z.1,t)) z.2 ∂ρ := by
  rw [conditionalSigmaEntropy_fst ρ P hP]
  have H := Measure.integral_compProd
    (integrable_kernel_observationInformation ρ.fst ρ.condKernel P hP)
  rw [Measure.disintegrate] at H
  refine (integral_congr_ae (ae_of_all _ fun s => ?_)).trans H.symm
  exact (integral_observationInformation (ρ.condKernel s) _
    (fun a => (hP a).preimage measurable_prodMk_left)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional entropy as the mean pointwise information

The finite observed variable has a regular conditional distribution even
when the conditioning sigma algebra is arbitrary. Lifting its underlying
space keeps the ambient and conditioning measurable structures distinct.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalInformation_integrable_integral {Y : Type*} (m : MeasurableSpace Y)
    [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {N : ℕ} [NeZero N]
    (P : Y → Fin N) (hP : Measurable P) (hm : m ≤ mY) :
    Integrable (conditionalInformation μ P m) μ ∧
      (∫ y, conditionalInformation μ P m y ∂μ) = conditionalSigmaEntropy μ P m := by
  let : MeasurableSpace (ULift.{0} Y) := m.comap ULift.down
  let X : Y → ULift.{0} Y := ULift.up
  have hmX : MeasurableSpace.comap X (inferInstance : MeasurableSpace (ULift.{0} Y)) = m := by
    change (m.comap ULift.down).comap ULift.up = m
    rw [MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_id
  have hX : Measurable X := by
    apply Measurable.of_comap_le
    simpa only [hmX] using hm
  let σ := μ.map (fun y => (X y,P y))
  let κ := σ.condKernel
  have hκ : condDistrib P X μ = κ := by rw [condDistrib]
  have heq (a : Fin N) :
      μ[({z | P z=a}.indicator (fun _ => (1:ℝ))) | m] =ᵐ[μ]
        fun y => (κ (X y)).real {a} := by
    have H := condExp_ae_eq_integral_condDistrib (μ := μ) (X := X) (Y := P)
      hX hP.aemeasurable
      ((stronglyMeasurable_const.indicator (measurableSet_singleton a)) :
        StronglyMeasurable (({a} : Set (Fin N)).indicator (fun _ : Fin N => (1:ℝ))))
      ((integrable_const (1:ℝ)).indicator (hP (measurableSet_singleton a)))
    rw [hκ,hmX] at H
    have hleft : (fun y => ({a} : Set (Fin N)).indicator (fun _ => (1:ℝ)) (P y)) =
        {z | P z=a}.indicator (fun _ => (1:ℝ)) := by
      funext y
      simp only [Set.indicator_apply,Set.mem_singleton_iff,Set.mem_ofPred_eq]
    simpa only [hleft,integral_indicator_const (1:ℝ) (measurableSet_singleton a),
      smul_eq_mul,mul_one] using H
  let I : ULift.{0} Y × Fin N → ℝ :=
    fun z => observationInformation (κ z.1) (id : Fin N → Fin N) z.2
  have hI : Measurable I := measurable_kernel_observationInformation κ Prod.snd
    (fun a => measurable_snd (measurableSet_singleton a))
  have hIp : conditionalInformation μ P m =ᵐ[μ] fun y => I (X y,P y) := by
    filter_upwards [ae_all_iff.mpr heq] with y hy
    unfold conditionalInformation I observationInformation
    rw [hy (P y)]
    rfl
  have hIint : Integrable I σ := by
    have H := integrable_kernel_observationInformation σ.fst κ Prod.snd
      (fun a => measurable_snd (measurableSet_singleton a))
    change Integrable I (σ.fst ⊗ₘ σ.condKernel) at H
    rwa [Measure.disintegrate] at H
  have hIf : Integrable (fun y => I (X y,P y)) μ :=
    hIint.comp_measurable (hX.prodMk hP)
  refine ⟨hIf.congr hIp.symm,?_⟩
  rw [integral_congr_ae hIp]
  have HI := conditionalEntropy_fst_information σ Prod.snd
    (fun a => measurable_snd (measurableSet_singleton a))
  rw [conditionalSigmaEntropy_fst σ Prod.snd
    (fun a => measurable_snd (measurableSet_singleton a))] at HI
  have HE : conditionalSigmaEntropy μ P m =
      ∫ y, observationEntropy (κ (X y)) (id : Fin N → Fin N) ∂μ := by
    unfold conditionalSigmaEntropy observationEntropy
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr heq] with y hy
    congr 1
    funext a
    simpa only [id_eq,Set.ofPred_eq_eq_singleton] using hy a
  rw [HE]
  calc
    _ = ∫ z, I z ∂σ :=
      (integral_map (hX.prodMk hP).aemeasurable hI.aestronglyMeasurable).symm
    _ = ∫ s, observationEntropy (κ s) (id : Fin N → Fin N) ∂σ.fst := HI.symm
    _ = ∫ z, observationEntropy (κ z.1) (id : Fin N → Fin N) ∂σ :=
      integral_map measurable_fst.aemeasurable
        (measurable_fiber_observationEntropy κ Prod.snd
          (fun a => measurable_snd (measurableSet_singleton a))).aestronglyMeasurable
    _ = _ := integral_map (hX.prodMk hP).aemeasurable
      ((measurable_fiber_observationEntropy κ Prod.snd
        (fun a => measurable_snd (measurableSet_singleton a))).comp measurable_fst).aestronglyMeasurable

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FiniteFactorInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite conditional entropy under a countable recoding -/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalInformation_fintype_integrable_integral
    {Y α : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (hP : Measurable P) (hm : m ≤ mY) :
    Integrable (conditionalInformation μ P m) μ ∧
      (∫ x, conditionalInformation μ P m x ∂μ)=conditionalSigmaEntropy μ P m := by
  let e := Fintype.equivFin α
  let : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  have he : Measurable e := measurable_of_countable e
  have H := conditionalInformation_integrable_integral m μ (e ∘ P) (he.comp hP) hm
  have hi : conditionalInformation μ (e ∘ P) m=conditionalInformation μ P m := by
    funext x
    unfold conditionalInformation
    have hs : {z | (e ∘ P) z=(e ∘ P) x}={z | P z=P x} := by
      ext z
      exact e.injective.eq_iff
    rw [hs]
  have hs : conditionalSigmaEntropy μ (e ∘ P) m=conditionalSigmaEntropy μ P m := by
    unfold conditionalSigmaEntropy
    apply integral_congr_ae
    apply ae_of_all
    intro x
    unfold finiteShannon
    symm
    apply Fintype.sum_equiv e
    intro a
    have ha : {z | (e ∘ P) z=e a}={z | P z=a} := by
      ext z
      exact e.injective.eq_iff
    dsimp only
    rw [ha]
  rw [hi,hs] at H
  exact H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingFutureShift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact shift of future atoms along remaining-root leaves -/

noncomputable section
open Set
open MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma measurableSet_remainingFutureAtom (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) (x : X n) :
    MeasurableSet (c.remainingFutureAtom ell hell Q m x) := by
  let T : X n → X n := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  change MeasurableSet {u | ∀ k : ℕ, Q (T^[k+m] (rightAction x (c.word u))) = _}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (hQ.comp ((hT.iterate (k+m)).comp hF)) (measurableSet_singleton _)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_StationaryRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gluing stationary restrictions over a countable cover

For a Markov kernel, stationary restrictions of one finite measure are
closed under intersections and unions. Thus local stationarity on a
countable almost-everywhere cover implies global stationarity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

theorem bind_kernel_real (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) (A : Set Y) (hA : MeasurableSet A) :
    (μ.bind κ).real A = ∫ y, (κ y).real A ∂μ := by
  rw [Measure.real, Measure.bind_apply hA κ.measurable.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Filter.Eventually.of_forall fun y => measure_lt_top (κ y) A)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SelfConditionalKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional distributions from a stationary fiber kernel

A stationary kernel which is constant almost everywhere on each of its
own probability fibers is the conditional distribution for the sigma
algebra generated by that kernel. This is the precise extra condition
needed beyond stationarity in the whole-future application.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*} [mY : MeasurableSpace Y]

theorem setIntegral_selfConstant_kernel
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ = μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y = κ x)
    {S : Set Y} (hS : MeasurableSet[MeasurableSpace.comap κ inferInstance] S)
    {A : Set Y} (hA : MeasurableSet A) :
    (∫ x in S, (κ x).real A ∂μ) = μ.real (A ∩ S) := by
  have hSm : MeasurableSet S := κ.measurable.comap_le S hS
  obtain ⟨B,hB,rfl⟩ := hS
  have he : ∀ᵐ x ∂μ,
      (κ x).real (A ∩ (κ ⁻¹' B)) =
        (κ ⁻¹' B).indicator (fun x => (κ x).real A) x := by
    filter_upwards [hself] with x hx
    by_cases hb : κ x ∈ B
    · rw [Set.indicator_of_mem (show x ∈ κ ⁻¹' B from hb)]
      apply congrArg ENNReal.toReal
      apply measure_congr
      filter_upwards [hx] with y hy
      show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
      simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_true]
    · rw [Set.indicator_of_notMem (show x ∉ κ ⁻¹' B from hb)]
      have hz : (κ x) (A ∩ (κ ⁻¹' B)) = 0 := by
        rw [←measure_empty (μ := κ x)]
        apply measure_congr
        filter_upwards [hx] with y hy
        show (y ∈ (A ∩ κ ⁻¹' B : Set Y)) = (y ∈ (∅ : Set Y))
        simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_false,mem_empty_iff_false]
      rw [Measure.real,hz,ENNReal.toReal_zero]
  calc
    _ = ∫ x, (κ ⁻¹' B).indicator (fun x => (κ x).real A) x ∂μ :=
      (integral_indicator hSm).symm
    _ = ∫ x, (κ x).real (A ∩ (κ ⁻¹' B)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      exact hx.symm
    _ = (μ.bind κ).real (A ∩ (κ ⁻¹' B)) :=
      (bind_kernel_real κ μ _ (hA.inter hSm)).symm
    _ = _ := by rw [hstat]

/-- The kernel evaluations are actual conditional probabilities. -/
theorem selfConstant_kernel_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ = μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y = κ x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap κ inferInstance] := by
  have hm : MeasurableSpace.comap (fun x => κ x)
      (inferInstance : MeasurableSpace (Measure Y)) ≤ mY := κ.measurable.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hA)
  · exact fun _ _ _ => (integrable_kernel_real μ κ hA).integrableOn
  · intro S hS _
    rw [setIntegral_selfConstant_kernel μ κ hstat hself hS hA,
      integral_indicator_const (1 : ℝ) hA]
    simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply hA]
  · have h : @Measurable Y ℝ (MeasurableSpace.comap κ inferInstance)
        inferInstance (fun x => (κ x).real A) :=
      (Measure.measurable_coe hA).ennreal_toReal.comp (comap_measurable κ)
    exact h.stronglyMeasurable.aestronglyMeasurable

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_StationaryFiberConditioning
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning a stationary kernel on its actual fiber labels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y S : Type*} [mY : MeasurableSpace Y] [MeasurableSpace S]

theorem fiberConstant_kernel_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hκF : @Measurable Y (Measure Y) (MeasurableSpace.comap F inferInstance)
      inferInstance κ)
    (hstat : μ.bind κ=μ)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap F inferInstance] := by
  have hm := hF.comap_le
  apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) hm
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hA)
  · exact fun _ _ _ => (integrable_kernel_real μ κ hA).integrableOn
  · intro U hU _
    have hUm : MeasurableSet U := hm U hU
    obtain ⟨B,hB,rfl⟩ := hU
    have he : ∀ᵐ x ∂μ, (κ x).real (A ∩ (F ⁻¹' B)) =
        (F ⁻¹' B).indicator (fun x => (κ x).real A) x := by
      filter_upwards [hconst] with x hx
      by_cases hb : F x ∈ B
      · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' B from hb)]
        apply congrArg ENNReal.toReal
        apply measure_congr
        filter_upwards [hx] with y hy
        show (_ ∈ (_ : Set _)) = (_ ∈ (_ : Set _))
        simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_true]
      · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' B from hb)]
        have hz : (κ x) (A ∩ (F ⁻¹' B))=0 := by
          rw [←measure_empty (μ := κ x)]
          apply measure_congr
          filter_upwards [hx] with y hy
          show (y ∈ (A ∩ F ⁻¹' B : Set Y)) = (y ∈ (∅ : Set Y))
          simp only [Set.mem_setOf_eq,mem_inter_iff,mem_preimage,hy,hb,and_false,mem_empty_iff_false]
        rw [Measure.real,hz,ENNReal.toReal_zero]
    calc
      (∫ x in F ⁻¹' B, (κ x).real A ∂μ) =
          ∫ x, (F ⁻¹' B).indicator (fun x => (κ x).real A) x ∂μ :=
        (integral_indicator hUm).symm
      _ = ∫ x, (κ x).real (A ∩ (F ⁻¹' B)) ∂μ :=
        integral_congr_ae (by
          filter_upwards [he] with x hx
          exact hx.symm)
      _ = (μ.bind κ).real (A ∩ (F ⁻¹' B)) :=
        (bind_kernel_real κ μ _ (hA.inter hUm)).symm
      _ = ∫ x in F ⁻¹' B, A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [hstat,integral_indicator_const (1 : ℝ) hA]
        simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply hA]
  · exact ((Measure.measurable_coe hA).ennreal_toReal.comp hκF).stronglyMeasurable.aestronglyMeasurable

theorem selfConstant_kernel_with_label_ae_eq_condExp
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    {A : Set Y} (hA : MeasurableSet A) :
    (fun x => (κ x).real A) =ᵐ[μ]
      μ[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] := by
  apply fiberConstant_kernel_ae_eq_condExp μ κ (fun x => (κ x,F x))
    (κ.measurable.prodMk hF) (measurable_fst.comp (comap_measurable _)) hstat
  · filter_upwards [hself,hconst] with x hs hc
    filter_upwards [hs,hc] with y hy hc
    exact Prod.ext hy hc
  · exact hA

theorem selfConstant_kernel_with_label_information
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F)
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (Q : Y → ℕ) (hQ : Measurable Q) :
    conditionalInformation μ Q
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =ᵐ[μ]
      conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) := by
  have h (a : ℕ) :=
    (selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF hstat hself hconst
      (hQ (measurableSet_singleton a))).symm.trans
    (selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hQ (measurableSet_singleton a)))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact congrArg (-Real.log ·) (hx (Q x))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_KernelFutureInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual root information is bounded by full metric entropy

The entire future is an almost sure fiber label of the constructed
kernel. Adding that label to the conditioning sigma algebra leaves its
conditional law unchanged, and makes the future inclusion literal.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

theorem ambientFutureMeasure_ae_same_names
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (m : ℕ) (x : X n) :
    ∀ᵐ y ∂c.ambientFutureMeasure hP hf μ ell hell Q m x, ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] x) := by
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  unfold ambientFutureMeasure
  apply (ae_map_iff hF.aemeasurable ?_).mpr
  · exact ae_restrict_mem (c.measurableSet_remainingFutureAtom hf ell hell Q hQ m x)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact (hQ.comp (((continuous_rightAction _).measurable).iterate (k+m)))
      (measurableSet_singleton _)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPredecessorInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite predecessor information on actual root future fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
/-- Recoding on a stationary kernel fiber does not require measurable
 equality on its measure-valued label. -/
theorem kernel_label_information_eq_of_fiber_equiv
    {Y S α β : Type*} [MeasurableSpace Y] [MeasurableSpace S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (μ : Measure Y) [IsFiniteMeasure μ] (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F) (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (hequiv : ∀ x y, F x=F y → (P x=P y ↔ B x=B y)) :
    conditionalInformation μ P
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =ᵐ[μ]
      conditionalInformation μ B
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) := by
  have hp (a : α) : (fun x => (κ x).real {y | P y=a}) =ᵐ[μ]
      μ[({y | P y=a}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] :=
    selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF
      hstat hself hconst (hP (measurableSet_singleton a))
  have hb (b : β) : (fun x => (κ x).real {y | B y=b}) =ᵐ[μ]
      μ[({y | B y=b}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] :=
    selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF
      hstat hself hconst (hB (measurableSet_singleton b))
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hb,hconst] with x hxP hxB hxF
  unfold conditionalInformation
  rw [←hxP (P x),←hxB (B x)]
  have hm : κ x {y | P y=P x}=κ x {y | B y=B x} := by
    apply measure_congr
    filter_upwards [hxF] with y hy
    exact propext (hequiv y x hy)
  rw [show (κ x).real {y | P y=P x}=(κ x).real {y | B y=B x} from
    congrArg ENNReal.toReal hm]

namespace EliminationChain

/-- The same finite predecessor symbol used for the ambient entropy
bound has exactly the root-information integral on the finer root fibers. -/
theorem predecessor_root_information_oai
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
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
    (hdecode : ∀ x,
      decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := entireFutureObservation T Q
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := entireFutureObservation T Q
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := entireFutureObservation_measurable hT hQ
  have hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x := by
    filter_upwards [hversion] with x hx
    rw [hx]
    filter_upwards [c.ambientFutureMeasure_ae_same_names hP hf μ ell hell Q hQ 1 x]
      with y hy
    exact funext hy
  have he := kernel_label_information_eq_of_fiber_equiv μ κ F hF hstat hself hconst
    Q hQ B hB (by
      intro x y hxy
      have ht : Q (T x)=Q (T y) := by
        simpa only [F,entireFutureObservation,Nat.zero_add,Function.iterate_one] using
          congrFun hxy 0
      exact ⟨fun h => href x y h ht,fun hb => by rw [←hdecode x,←hdecode y,ht,hb]⟩)
  have hs := selfConstant_kernel_with_label_information μ κ F hF hstat hself hconst Q hQ
  have HI := c.wholeFuture_conditionalInformation_integrable_integral d hP hf μ hA
    ell hell Q hQ κ hstat hself hversion hmass
  have HB := conditionalInformation_fintype_integrable_integral
    (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) μ B hB
    (κ.measurable.prodMk hF).comap_le
  calc
    _ = ∫ x, conditionalInformation μ B
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) x ∂μ := HB.2.symm
    _ = ∫ x, conditionalInformation μ Q
        (MeasurableSpace.comap κ inferInstance) x ∂μ :=
      integral_congr_ae (he.symm.trans hs)
    _ = _ := HI.2

end EliminationChain
end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.EliminationChain.predecessor_root_information_oai := @OAI.DukePrimeDegree.EliminationChain.predecessor_root_information_oai
