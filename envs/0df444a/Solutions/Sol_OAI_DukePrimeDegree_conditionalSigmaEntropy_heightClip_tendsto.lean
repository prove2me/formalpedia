-- Prove2me | solution 1 for OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:48.00291+00:00
-- url     : https://prove2.me/submissions/1bde00d1-1050-478e-b6de-8a4ed99f5c15

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_EntropyMixtures
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalSigmaOrder
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableObservationInformation
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalInformationClipping
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite present observations with a fixed conditioning sigma algebra

An integrable countable information function is the limit of the
conditional entropies of finite clips. The conditioning is kept fixed;
in the application it is the entire future together with the transverse
coordinate, rather than the future of a clipped observation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*}

lemma conditionalInformation_heightClip_eventually
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) (Q : Y → ℕ) (y : Y) :
    ∀ᶠ N : ℕ in atTop,
      conditionalInformation μ (heightClip Q N) m y = conditionalInformation μ Q m y := by
  filter_upwards [eventually_gt_atTop (Q y)] with N hN
  unfold conditionalInformation
  rw [heightClip_atom_eq_of_lt Q y hN]

lemma ae_conditionalInformation_heightClip_bounds
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (Q : Y → ℕ) (hQ : Measurable Q)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y) (N : ℕ) :
    ∀ᵐ y ∂μ, 0 ≤ conditionalInformation μ (heightClip Q N) m y ∧
      conditionalInformation μ (heightClip Q N) m y ≤ conditionalInformation μ Q m y := by
  classical
  let clip (a : ℕ) : Fin (N+1) := ⟨min a N, Nat.lt_succ_of_le (min_le_right a N)⟩
  have hmono (a : ℕ) :
      μ[({z | Q z = a}.indicator (fun _ => (1 : ℝ))) | m] ≤ᵐ[μ]
        μ[({z | heightClip Q N z = clip a}.indicator (fun _ => (1 : ℝ))) | m] := by
    apply condExp_mono
      ((integrable_const (1 : ℝ)).indicator (hQ (measurableSet_singleton a)))
      ((integrable_const (1 : ℝ)).indicator
        ((heightClip_measurable hQ N) (measurableSet_singleton (clip a))))
    apply ae_of_all
    intro z
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hz : Q z = a
    · have hc : heightClip Q N z = clip a := by simp [hz, heightClip, clip]
      rw [ite_eq_left hz, ite_eq_left hc]
    · rw [ite_eq_right hz]
      split_ifs <;> norm_num
  have hb (a : Fin (N+1)) :=
    conditionalProbability_unit_bounds μ {z | heightClip Q N z = a} m
  filter_upwards [ae_all_iff.mpr hmono, ae_all_iff.mpr hb, hpos] with y hy hby hpy
  change 0 ≤ -Real.log _ ∧ -Real.log _ ≤ -Real.log _
  refine ⟨neg_nonneg.mpr (Real.log_nonpos (hby _).1 (hby _).2), ?_⟩
  apply neg_le_neg
  apply Real.log_le_log hpy
  exact hy (Q y)

/-- Finite present-label clips recover the mean countable information,
with no finite-Shannon-entropy assumption on the full countable label. -/
theorem conditionalSigmaEntropy_heightClip_tendsto_oai
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (Q : Y → ℕ) (hQ : Measurable Q) (hm : m ≤ mY)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y)
    (hint : Integrable (conditionalInformation μ Q m) μ) :
    Tendsto (fun N => conditionalSigmaEntropy μ (heightClip Q N) m) atTop
      (𝓝 (∫ y, conditionalInformation μ Q m y ∂μ)) := by
  have H := tendsto_integral_of_dominated_convergence
    (conditionalInformation μ Q m)
    (fun N => (conditionalInformation_integrable_integral m μ (heightClip Q N)
      (heightClip_measurable hQ N) hm).1.aestronglyMeasurable)
    hint
    (fun N => (ae_conditionalInformation_heightClip_bounds m μ Q hQ hpos N).mono
      (fun y hy => by simpa only [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2))
    (ae_of_all _ (fun y => by
      apply tendsto_const_nhds.congr'
      filter_upwards [conditionalInformation_heightClip_eventually m μ Q y] with N hN
      exact hN.symm))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  exact (conditionalInformation_integrable_integral m μ (heightClip Q N)
    (heightClip_measurable hQ N) hm).2.symm

end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto_oai.{u_1} := @OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto_oai.{u_1}
