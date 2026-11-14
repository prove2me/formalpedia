-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:38:44.255317+00:00
-- url     : https://prove2.me/submissions/4eba1a2d-8135-4197-a5b0-d24788b8342a

import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ErgodicAverageMean
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the constant ergodic average

The constant obtained from the L2 mean ergodic theorem is the integral
of the original observable. Integration is represented by pairing with
the constant-one vector, so passage to the limit is continuous in L2.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma constantL2_ae (μ : Measure X) [IsFiniteMeasure μ] (c : ℝ) :
    (constantL2 μ c : X → ℝ) =ᵐ[μ] fun _ => c :=
  (memLp_const c).coeFn_toLp

lemma meanL2_apply (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    meanL2 μ f = ∫ x, f x ∂μ := by
  change inner ℝ (constantL2 μ 1) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constantL2_ae μ 1] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_one]

lemma meanL2_constant (μ : Measure X) [IsProbabilityMeasure μ] (c : ℝ) :
    meanL2 μ (constantL2 μ c) = c := by
  rw [meanL2_apply]
  exact integral_eq_const (constantL2_ae μ c)

lemma meanL2_koopman (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    meanL2 μ (Lp.compMeasurePreserving T hT f) = meanL2 μ f := by
  rw [meanL2_apply, meanL2_apply]
  calc
    _ = ∫ x, f (T x) ∂μ := integral_congr_ae (Lp.coeFn_compMeasurePreserving f hT)
    _ = ∫ x, f x ∂μ := by
      have hfmap : AEStronglyMeasurable (fun x => f x) (μ.map T) := by
        rw [hT.map_eq]
        exact Lp.aestronglyMeasurable f
      have he := integral_map (μ := μ) (φ := T) (f := fun x => f x)
        hT.measurable.aemeasurable hfmap
      rw [hT.map_eq] at he
      exact he.symm

lemma meanL2_iterate (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) (n : ℕ) :
    meanL2 μ ((Lp.compMeasurePreserving T hT)^[n] f) = meanL2 μ f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', meanL2_koopman, ih]

lemma meanL2_birkhoffAverage (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ)
    (n : ℕ) (hn : n ≠ 0) :
    meanL2 μ (birkhoffAverage ℝ (Lp.compMeasurePreserving T hT) id n f) = meanL2 μ f := by
  simp only [birkhoffAverage, birkhoffSum, map_smul, map_sum, meanL2_iterate,
    id_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_L2ToL1Averages
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# L1 control of actual ergodic orbit averages

Probability normalization gives the L2-to-L1 bound with constant one.
Combining it with the identified mean and the uniform-density transfer
allows the sampling law of an orbit average to vary with its length.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma integral_norm_le_L2_norm (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num : (1 : ℝ≥0∞) ≤ 2))

lemma L1_tendsto_of_L2_tendsto_constant
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℕ → Lp ℝ 2 μ) (c : ℝ)
    (hF : Tendsto F atTop (𝓝 (constantL2 μ c))) :
    Tendsto (fun n => ∫ x, |F n x - c| ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : (∫ x, |F n x - c| ∂μ) ≤ ‖F n - constantL2 μ c‖ := by
    have he : (∫ x, |F n x - c| ∂μ) = ∫ x, ‖(F n - constantL2 μ c) x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (F n) (constantL2 μ c), constantL2_ae μ c] with x hx hc
      simp only [hx, Pi.sub_apply, hc, Real.norm_eq_abs]
    rw [he]
    exact integral_norm_le_L2_norm μ _
  have hnorm : Tendsto (fun n => ‖F n - constantL2 μ c‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hF.sub_const (constantL2 μ c)).norm
  exact squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _)) hbound hnorm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitAverageFunctions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise representatives of the orbit averages

The Hilbert-space Cesaro average agrees almost everywhere with the
literal finite sum along the orbit. A bounded density transfers that
agreement to a varying sampling law, so the dominated-average theorem
applies to actual orbit samples.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma orbit_average_congr_ae (μ : Measure X) (T : X → X)
    (hT : MeasurePreserving T μ μ) {f g : X → ℝ}
    (hfg : f =ᵐ[μ] g) (N : ℕ) :
    birkhoffAverage ℝ T f N =ᵐ[μ] birkhoffAverage ℝ T g N := by
  have hsum := eventuallyEq_sum (s := Finset.range N)
    (fun k _ => (hT.iterate k).quasiMeasurePreserving.ae_eq_comp hfg)
  filter_upwards [hsum] with x hx
  simpa only [birkhoffAverage, birkhoffSum, Function.comp_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    congrArg (fun z : ℝ => (N : ℝ)⁻¹ * z) hx

lemma Lp_orbit_average_ae (μ : Measure X) (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) (N : ℕ) :
    ((birkhoffAverage ℝ (Lp.compMeasurePreserving T hT) id N f : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] birkhoffAverage ℝ T f N := by
  have hit (k : ℕ) :
      ((Lp.compMeasurePreserving T hT)^[k] f : X → ℝ)
        =ᵐ[μ] fun x => f (T^[k] x) := by
    rw [Lp.compMeasurePreserving_iterate]
    exact Lp.coeFn_compMeasurePreserving f (hT.iterate k)
  have hsum :
      ((∑ k ∈ Finset.range N, (Lp.compMeasurePreserving T hT)^[k] f : Lp ℝ 2 μ) : X → ℝ)
        =ᵐ[μ] fun x => ∑ k ∈ Finset.range N, f (T^[k] x) :=
    by
      have hh := eventuallyEq_sum (s := Finset.range N) (fun k _ => hit k)
      filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range N)
        (fun k => (Lp.compMeasurePreserving T hT)^[k] f), hh] with x hx hx'
      exact hx.trans (by simpa only [Finset.sum_apply] using hx')
  have hscale := Lp.coeFn_smul ((N : ℝ)⁻¹)
    (∑ k ∈ Finset.range N, (Lp.compMeasurePreserving T hT)^[k] f)
  filter_upwards [hscale, hsum] with x hx hs
  simpa only [birkhoffAverage, birkhoffSum, id_eq, Pi.smul_apply,
    smul_eq_mul, hs] using hx

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitCoboundary
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded coboundary approximations to an orbit observable

The difference between a bounded observable and any one of its finite
orbit averages is an explicit bounded coboundary. This is the uniform
part of the maximal-inequality proof of a common generic set.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*}

lemma sub_orbit_average_eq_coboundary
    (T : X → X) (f : X → ℝ) (M : ℕ) (hM : M ≠ 0) (x : X) :
    f x - birkhoffAverage ℝ T f M x =
      orbitAveragePotential T f M x - orbitAveragePotential T f M (T x) := by
  have hdiff (j : ℕ) : birkhoffSum T f j x - birkhoffSum T f j (T x) =
      f x - f (T^[j] x) := by
    have h₁ := birkhoffSum_succ T f j x
    have h₂ := birkhoffSum_succ' T f j x
    linarith
  have hc : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  unfold orbitAveragePotential
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [hdiff]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, birkhoffAverage, birkhoffSum, smul_eq_mul]
  field_simp

lemma birkhoffSum_abs_le
    (T : X → X) (f : X → ℝ) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (N : ℕ) (x : X) :
    |birkhoffSum T f N x| ≤ (N : ℝ) * C := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, |f (T^[k] x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, C := Finset.sum_le_sum (fun k _ => hC (T^[k] x))
    _ = _ := by simp

lemma orbitAveragePotential_abs_le
    (T : X → X) (f : X → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, |f x| ≤ C) (M : ℕ) (x : X) :
    |orbitAveragePotential T f M x| ≤ (M : ℝ) * C := by
  by_cases hM : M = 0
  · simp [orbitAveragePotential, hM]
  have hm : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
  unfold orbitAveragePotential
  rw [abs_mul, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (M : ℝ)⁻¹ * ∑ j ∈ Finset.range M, |birkhoffSum T f j x| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hm.le)
    _ ≤ (M : ℝ)⁻¹ * ∑ _j ∈ Finset.range M, (M : ℝ) * C := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm.le)
      apply Finset.sum_le_sum
      intro j hj
      exact (birkhoffSum_abs_le T f C hC j x).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hj).le) hC0)
    _ = (M : ℝ) * C := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

/-- A bounded coboundary has a uniformly small Cesaro average. -/
lemma orbit_average_coboundary_bound
    (T : X → X) (g : X → ℝ) (B : ℝ) (hg : ∀ x, |g x| ≤ B)
    (N : ℕ) (x : X) :
    |birkhoffAverage ℝ T (fun y => g y - g (T y)) N x| ≤
      (N : ℝ)⁻¹ * (2 * B) := by
  have htel : birkhoffSum T (fun y => g y - g (T y)) N x = g x - g (T^[N] x) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [birkhoffSum_succ, ih, Function.iterate_succ_apply']
        ring
  rw [birkhoffAverage, smul_eq_mul, htel, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have htri : |g x - g (T^[N] x)| ≤ |g x| + |g (T^[N] x)| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (g x) (g (T^[N] x))
  exact mul_le_mul_of_nonneg_left
    (htri.trans (by linarith [hg x, hg (T^[N] x)]))
    (inv_nonneg.mpr (Nat.cast_nonneg N))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact observables under small group translations

A compactly supported continuous observable changes uniformly little
under a group element tending to the identity. This remains true along
arbitrary moving base points, including points leaving compact sets.
It supplies the topological contraction step in the Hopf argument on a
noncompact homogeneous space.
-/

open Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [MulAction G X]
  [ContinuousSMul G X]

/-- Small translations act uniformly continuously on a compactly
supported continuous real observable. -/
theorem compact_observable_smul_tendstoUniformly
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun a : G => fun x : X => f (a • x)) f (𝓝 1) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  let C : Set X := tsupport f ∪
    (fun z : G × X => z.1⁻¹ • z.2) '' (V ×ˢ tsupport f)
  have hCc : IsCompact C := hc.union
    ((hVc.prod hc).image (continuous_fst.inv.smul continuous_snd))
  have hcont : Continuous (fun z : G × X => f (z.1 • z.2)) := by
    fun_prop
  obtain ⟨W, hW, hsmallW⟩ := hCc.mem_uniformity_of_prod
    (f := fun a : G => fun x : X => f (a • x))
    (s := Set.univ) hcont.continuousOn (show (1 : G) ∈ Set.univ from Set.mem_univ _)
    (Metric.dist_mem_uniformity hε)
  have hsmall : ∀ᶠ a : G in 𝓝 1,
      ∀ x : C, dist (f (a • (x : X))) (f x) < ε := by
    have hW' : W ∈ 𝓝 (1 : G) := by simpa only [nhdsWithin_univ] using hW
    filter_upwards [hW'] with a ha x
    simpa only [one_smul, Set.mem_ofPred_eq] using hsmallW a ha x x.property
  filter_upwards [hV, hsmall] with a ha hs x
  by_cases hx : x ∈ C
  · simpa only [dist_comm] using hs ⟨x, hx⟩
  · have hx0 : f x = 0 := by
      by_contra hne
      exact hx (Or.inl (subset_tsupport f hne))
    have hax0 : f (a • x) = 0 := by
      by_contra hne
      apply hx
      exact Or.inr ⟨(a, a • x), ⟨ha, subset_tsupport f hne⟩, inv_smul_smul a x⟩
    simpa only [hx0, hax0, dist_self] using hε

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootSubgroups
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

 
lemma transvection_chain_commutator {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hjk b *
      Matrix.SpecialLinearGroup.transvection hij (-a) *
      Matrix.SpecialLinearGroup.transvection hjk (-b) =
      Matrix.SpecialLinearGroup.transvection hik (a*b) := by
  ext r c
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.transvection_coe,
    mul_add,add_mul,Matrix.one_mul,Matrix.mul_one]
  by_cases hri : r = i <;> by_cases hrj : r = j <;> by_cases hrk : r = k <;>
    by_cases hci : c = i <;> by_cases hcj : c = j <;> by_cases hck : c = k
  all_goals simp_all [Matrix.single_apply,Matrix.one_apply,eq_comm]


end PrimeDegreePackets


open scoped Topology Classical Matrix
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DiscreteMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform discrete orbit averages

The finite Hopf inequality bounds the union over all averaging lengths.
The resulting measurable good set controls every positive integer time,
as needed before passing to the continuous diagonal flow.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

theorem positiveRunningSum_measure_bound
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    μ (⋃ n : ℕ, {x | 0 < positiveRunningSum T (fun y => g y - c) n x}) ≤
      ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
  let f : Y → ℝ := fun x => g x - c
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hf : Integrable f μ := hg.sub (integrable_const c)
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hEmeas (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  have hEmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hbound (n : ℕ) : μ (E n) ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) := by
    have hhopf := finite_hopf_maximal hT hf hfmeas n
    change 0 ≤ ∫ x in E n, g x - c ∂μ at hhopf
    rw [integral_sub hg.restrict (integrable_const c), setIntegral_const, smul_eq_mul] at hhopf
    have hsub : ∫ x in E n, g x ∂μ ≤ ∫ x, g x ∂μ :=
      setIntegral_le_integral hg (Eventually.of_forall hgnonneg)
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
      (div_nonneg (integral_nonneg hgnonneg) hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    change μ.real (E n) * c ≤ _
    linarith
  rw [hEmono.measure_iUnion]
  exact iSup_le hbound

/-- The complement of one measurable exceptional set controls all finite
averages, with the sharp Hopf bound on its measure. -/
theorem exists_discrete_average_good_set
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {g : Y → ℝ} (hg : Integrable g μ) (hgmeas : Measurable g)
    (hgnonneg : ∀ x, 0 ≤ g x) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set Y, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal ((∫ x, g x ∂μ) / c) ∧
      ∀ x ∈ G, ∀ n : ℕ, birkhoffSum T g n x ≤ c * n := by
  let f : Y → ℝ := fun x => g x - c
  let B := ⋃ n : ℕ, {x | 0 < positiveRunningSum T f n x}
  have hfmeas : Measurable f := hgmeas.sub measurable_const
  have hB : MeasurableSet B := MeasurableSet.iUnion fun n =>
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfmeas n)
  refine ⟨Bᶜ, hB.compl, ?_, ?_⟩
  · simpa only [compl_compl] using positiveRunningSum_measure_bound μ hT hg hgmeas hgnonneg c hc
  · intro x hx n
    have hnot : ¬ 0 < positiveRunningSum T f n x := by
      intro h
      exact hx (mem_iUnion.mpr ⟨n, h⟩)
    have hs := (birkhoffSum_le_positiveRunningSum T f n x).trans (le_of_not_gt hnot)
    have heq : birkhoffSum T f n x = birkhoffSum T g n x - (n : ℝ) * c := by
      change (∑ k ∈ Finset.range n, (g (T^[k] x) - c)) = _
      rw [Finset.sum_sub_distrib]
      simp [birkhoffSum]
    rw [heq] at hs
    linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BoundedGenericSet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform generic sets for bounded observables

The maximal estimate is applied to the small L1 residual of a single
finite orbit average. The complementary part is an explicit bounded
coboundary. Consequently one fixed set controls every sufficiently
large averaging length, including lengths chosen from a nearby pair.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

lemma measurable_orbit_average (T : X → X) (hT : Measurable T)
    (f : X → ℝ) (hf : Measurable f) (N : ℕ) :
    Measurable (birkhoffAverage ℝ T f N) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun k _ => hf.comp (hT.iterate k))

lemma integrable_orbit_average (μ : Measure X) (T : X → X)
    (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Integrable f μ) (N : ℕ) :
    Integrable (birkhoffAverage ℝ T f N) μ := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun k _ => (hT.iterate k).integrable_comp_of_integrable hf)

omit [MeasurableSpace X] in
lemma abs_orbit_average_le_of_abs_sum_le (T : X → X) (r : X → ℝ)
    (η : ℝ) (N : ℕ) (hN : N ≠ 0) (x : X)
    (hsum : birkhoffSum T (fun y => |r y|) N x ≤ η * N) :
    |birkhoffAverage ℝ T r N x| ≤ η := by
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [birkhoffAverage, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (N : ℝ)⁻¹ * birkhoffSum T (fun y => |r y|) N x :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * (η * N) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = η := by field_simp

/-- Quantitative good set from one finite-average residual. -/
theorem exists_uniform_average_set_from_residual
    (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (c η : ℝ) (hη : 0 < η) (M : ℕ) (hM : M ≠ 0) :
    ∃ G : Set X, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal
        ((∫ x, |birkhoffAverage ℝ T f M x - c| ∂μ) / η) ∧
      ∀ x ∈ G, ∀ N : ℕ, N ≠ 0 →
        |birkhoffAverage ℝ T f N x - c| ≤ (N : ℝ)⁻¹ * (2 * (M * C)) + η := by
  let r : X → ℝ := fun x => birkhoffAverage ℝ T f M x - c
  have hrm : Measurable r := (measurable_orbit_average T hT.measurable f hfm M).sub measurable_const
  have hri : Integrable r μ := (integrable_orbit_average μ T hT f hfi M).sub (integrable_const c)
  obtain ⟨G, hG, hGμ, hGsum⟩ := exists_discrete_average_good_set μ hT hri.norm
    (by simpa only [Real.norm_eq_abs] using hrm.norm) (fun x => abs_nonneg (r x)) η hη
  refine ⟨G, hG, hGμ, ?_⟩
  intro x hx N hN
  have hrbound : |birkhoffAverage ℝ T r N x| ≤ η :=
    abs_orbit_average_le_of_abs_sum_le T r η N hN x (hGsum x hx N)
  have hcob := orbit_average_coboundary_bound T (orbitAveragePotential T f M)
    (M * C) (orbitAveragePotential_abs_le T f C hC0 hC M) N x
  have hfun : (fun y => orbitAveragePotential T f M y -
      orbitAveragePotential T f M (T y)) = fun y => f y - birkhoffAverage ℝ T f M y := by
    funext y
    exact (sub_orbit_average_eq_coboundary T f M hM y).symm
  rw [hfun] at hcob
  have hc : birkhoffAverage ℝ T (fun _ => c) N x = c := by
    exact congrFun (birkhoffAverage_of_comp_eq (R := ℝ) (f := T) (g := fun _ => c) rfl (Nat.cast_ne_zero.mpr hN)) x
  have hdecomp : birkhoffAverage ℝ T f N x - c =
      birkhoffAverage ℝ T (fun y => f y - birkhoffAverage ℝ T f M y) N x +
        birkhoffAverage ℝ T r N x := by
    change _ = birkhoffAverage ℝ T (f - birkhoffAverage ℝ T f M) N x +
      birkhoffAverage ℝ T (birkhoffAverage ℝ T f M - fun _ => c) N x
    rw [birkhoffAverage_sub, birkhoffAverage_sub]
    simp only [Pi.sub_apply, hc]
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add hcob hrbound)

/-- L1 convergence of bounded orbit averages yields a single measurable
set of arbitrarily large measure with uniform eventual convergence.
The convergence premise is stated separately so it can be supplied by
an ergodic real flow after smoothing over one unit of time. -/
theorem exists_uniform_generic_set_of_L1_convergence
    (μ : Measure X) [IsFiniteMeasure μ]
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (c : ℝ)
    (hmean : Tendsto (fun M => ∫ x, |birkhoffAverage ℝ T f M x - c| ∂μ) atTop (𝓝 0))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set X, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀, |birkhoffAverage ℝ T f N x - c| ≤ ε := by
  have hsmall := hmean.eventually (gt_mem_nhds (show (0 : ℝ) < δ * (ε / 2) by positivity))
  obtain ⟨M, hM, hres⟩ := (eventually_gt_atTop (0 : ℕ)).and hsmall |>.exists
  obtain ⟨G, hG, hGμ, hGbound⟩ := exists_uniform_average_set_from_residual μ T hT
    f hfm hfi C hC0 hC c (ε / 2) (by positivity) M (Nat.ne_of_gt hM)
  refine ⟨G, hG, hGμ.trans ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (by positivity : 0 < ε / 2)).mpr hres.le
  · have hlim : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * (M * C))) atTop (𝓝 0) := by
      simpa only [div_eq_inv_mul] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (2 * (M * C)) / (N : ℝ)) atTop (𝓝 0))
    have htail := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_gt_atTop (0 : ℕ)).and htail)
    refine ⟨N₀, ?_⟩
    intro x hx N hN
    have hs := hGbound x hx N (Nat.ne_of_gt (hN₀ N hN).1)
    linarith [(hN₀ N hN).2]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FiniteKoopmanAverages
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite averages of Koopman operators

An average of finitely many Hilbert-space isometries has exactly their
common fixed vectors. This permits averaging an entire generating
family of an ergodic action without asserting that one chosen group
element is ergodic.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

section GroupAction

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  (μ : Measure X) [ErgodicSMul G X μ]

/-- Group ergodicity supplies constant invariant observables directly;
no selected element is assumed ergodic. -/
theorem ae_eq_const_of_group_invariant (f : X → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hinv : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro U hU
  apply eventuallyConst_set.mp
  apply aeconst_of_forall_preimage_smul_ae_eq G (hf.aemeasurable.nullMeasurable hU)
  intro g
  refine ((hinv g).mono fun x hx => ?_).set_eq
  simp only [Set.mem_preimage, hx]

end GroupAction
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowWindowAverages
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unit smoothing and continuous orbit windows

Discrete averages of a unit-smoothed observable are exactly continuous
flow averages at integer lengths. Shifting the initial point changes
only two boundary intervals; their contribution is uniformly bounded.
Neither statement assumes that a time-one map is ergodic.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*}

lemma flow_nat_iterate_dup1 (U : ℝ → X → X)
    (hzero : ∀ x, U 0 x = x)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x)) (N : ℕ) (x : X) :
    (U 1)^[N] x = U (N : ℝ) x := by
  induction N with
  | zero => simpa using (hzero x).symm
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, Nat.cast_succ]
      rw [add_comm, hadd]

lemma unitFlowSmooth_nat (U : ℝ → X → X) (f : X → ℝ)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x)) (N : ℕ) (x : X) :
    unitFlowSmooth U f (U (N : ℝ) x) =
      ∫ t in (N : ℝ)..(N : ℝ) + 1, f (U t x) := by
  unfold unitFlowSmooth
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_right (fun t => f (U t x)) (N : ℝ)]
  simp only [zero_add, add_comm (1 : ℝ)]

/-- Integer discrete averages of the smoothed observable are literal
continuous-time averages of the original observable. -/
theorem birkhoffAverage_unitFlowSmooth
    (U : ℝ → X → X) (f : X → ℝ)
    (hzero : ∀ x, U 0 x = x)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x))
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (N : ℕ) (x : X) :
    birkhoffAverage ℝ (U 1) (unitFlowSmooth U f) N x =
      (N : ℝ)⁻¹ * ∫ t in (0 : ℝ)..(N : ℝ), f (U t x) := by
  unfold birkhoffAverage birkhoffSum
  simp only [smul_eq_mul]
  congr 1
  simp_rw [flow_nat_iterate_dup1 U hzero hadd, unitFlowSmooth_nat U f hadd]
  simpa only [Nat.cast_zero, Nat.cast_succ] using
    (intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := N) (f := fun t => f (U t x)) (fun k _ => by
        simpa only [Nat.cast_add, Nat.cast_one] using hint x k (k + 1)))

/-- A translated window differs by two boundary intervals of the
translation length, regardless of the total window length. -/
theorem integral_window_shift_bound (F : ℝ → ℝ)
    (hint : ∀ a b, IntervalIntegrable F volume a b)
    (C : ℝ) (hC : ∀ t, |F t| ≤ C) (s L : ℝ) :
    |(∫ t in s..s + L, F t) - ∫ t in (0 : ℝ)..L, F t| ≤ 2 * C * |s| := by
  rw [intervalIntegral.integral_interval_sub_interval_comm'
    (hint s (s + L)) (hint 0 L) (hint s 0)]
  have hright : |∫ t in L..s + L, F t| ≤ C * |s| := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_right] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
        (a := L) (b := s + L) (C := C) (fun t _ => by simpa using hC t))
  have hleft : |∫ t in (0 : ℝ)..s, F t| ≤ C * |s| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
        (a := 0) (b := s) (C := C) (fun t _ => by simpa using hC t))
  calc
    _ ≤ |∫ t in L..s + L, F t| + |∫ t in (0 : ℝ)..s, F t| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (∫ t in L..s + L, F t) (∫ t in (0 : ℝ)..s, F t)
    _ ≤ C * |s| + C * |s| := add_le_add hright hleft
    _ = _ := by ring

/-- Invariance of the eventual average is under every real flow time,
not just under its integer subgroup. -/
theorem birkhoffAverage_unitFlowSmooth_shift_bound
    (U : ℝ → X → X) (f : X → ℝ)
    (hzero : ∀ x, U 0 x = x)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x))
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (N : ℕ) (s : ℝ) (x : X) :
    |birkhoffAverage ℝ (U 1) (unitFlowSmooth U f) N (U s x) -
        birkhoffAverage ℝ (U 1) (unitFlowSmooth U f) N x| ≤
      (N : ℝ)⁻¹ * (2 * C * |s|) := by
  rw [birkhoffAverage_unitFlowSmooth U f hzero hadd hint,
    birkhoffAverage_unitFlowSmooth U f hzero hadd hint, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_right (fun t => f (U t x)) s]
  simp only [zero_add]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [add_comm (N : ℝ)] using
    integral_window_shift_bound (fun t => f (U t x)) (hint x) C (fun t => hC (U t x)) s N

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FlowSmoothedL2
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean convergence for a real flow without time-one ergodicity

Unit smoothing removes the possible nonconstant time-one invariant
vectors. The boundary estimate makes the Hilbert-space limit invariant
under every real time, and ergodicity of the entire flow then makes it
constant. This is the averaging statement needed on actual ergodic
components of a root flow.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MulAction (Multiplicative ℝ) X]

lemma realActionTime_zero (x : X) : realActionTime 0 x = x := by
  simp [realActionTime]

lemma realActionTime_add (s t : ℝ) (x : X) :
    realActionTime (s + t) x = realActionTime s (realActionTime t x) := by
  simp only [realActionTime, ofAdd_add, mul_smul]

variable [MeasurableSpace X] [MeasurableConstSMul (Multiplicative ℝ) X]

/-- Flow ergodicity, with no ergodicity assumption on its time-one map. -/
theorem L2_unit_smoothed_real_action_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) X μ]
    (f : X → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C)
    (hint : ∀ x a b, IntervalIntegrable
      (fun t => f (realActionTime t x)) volume a b)
    (hg : MemLp (unitFlowSmooth realActionTime f) 2 μ) :
    Tendsto (fun N => birkhoffAverage ℝ
      (Lp.compMeasurePreserving (realActionTime 1)
        (measurePreserving_smul (Multiplicative.ofAdd 1) μ)) id N
      (hg.toLp (unitFlowSmooth realActionTime f))) atTop
      (𝓝 (constantL2 μ (∫ x, unitFlowSmooth realActionTime f x ∂μ))) := by
  let T : X → X := realActionTime 1
  have hT : MeasurePreserving T μ μ := measurePreserving_smul (Multiplicative.ofAdd 1) μ
  let g : X → ℝ := unitFlowSmooth realActionTime f
  let F : Lp ℝ 2 μ := hg.toLp g
  let V : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  have hVe : (V : Lp ℝ 2 μ → Lp ℝ 2 μ) = Lp.compMeasurePreserving T hT := by
    funext v
    rfl
  let A (N : ℕ) : Lp ℝ 2 μ := birkhoffAverage ℝ V id N F
  have hV : ‖V‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖Lp.compMeasurePreserving T hT v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using (Lp.norm_compMeasurePreserving v hT).le
  let S := V.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let q : Lp ℝ 2 μ := S.orthogonalProjectionOnto F
  have hA : Tendsto A atTop (𝓝 q) := V.tendsto_birkhoffAverage_orthogonalProjection hV F
  have hrep (N : ℕ) : (A N : X → ℝ) =ᵐ[μ] birkhoffAverage ℝ T g N :=
    (Lp_orbit_average_ae μ T hT F N).trans
      (orbit_average_congr_ae μ T hT hg.coeFn_toLp N)
  have hfixed (s : ℝ) :
      Lp.compMeasurePreserving (realActionTime s)
        (measurePreserving_smul (Multiplicative.ofAdd s) μ) q = q := by
    have hs := measurePreserving_smul (Multiplicative.ofAdd s) μ
    let W : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
      (Lp.compMeasurePreservingₗᵢ ℝ (realActionTime s) hs).toContinuousLinearMap
    have hb (N : ℕ) : ‖W (A N) - A N‖ ≤ (N : ℝ)⁻¹ * (2 * C * |s|) := by
      have hWA : (W (A N) : X → ℝ) =ᵐ[μ] fun x => A N (realActionTime s x) := by
        change (Lp.compMeasurePreserving (realActionTime s) hs (A N) : X → ℝ) =ᵐ[μ] _
        exact Lp.coeFn_compMeasurePreserving (A N) hs
      have hp : ∀ᵐ x ∂μ, ‖(W (A N) - A N) x‖ ≤ (N : ℝ)⁻¹ * (2 * C * |s|) := by
        filter_upwards [Lp.coeFn_sub (W (A N)) (A N),
          hWA,
          hs.quasiMeasurePreserving.ae_eq_comp (hrep N), hrep N] with x hsub hcomp hshift hplain
        change A N (realActionTime s x) = birkhoffAverage ℝ T g N (realActionTime s x) at hshift
        rw [hsub, Pi.sub_apply, hcomp, hshift, hplain, Real.norm_eq_abs]
        exact birkhoffAverage_unitFlowSmooth_shift_bound realActionTime f
          realActionTime_zero realActionTime_add hint C hC N s x
      simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity) hp
    have hbzero : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * C * |s|)) atTop (𝓝 0) := by
      simpa only [div_eq_inv_mul] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (2 * C * |s|) / (N : ℝ)) atTop (𝓝 0))
    have hzero : Tendsto (fun N => W (A N) - A N) atTop (𝓝 0) :=
      squeeze_zero_norm hb hbzero
    have hq := (W.continuous.tendsto q |>.comp hA).sub hA
    exact sub_eq_zero.mp (tendsto_nhds_unique hq hzero)
  have hqae : ∀ a : Multiplicative ℝ, (fun x => q (a • x)) =ᵐ[μ] (q : X → ℝ) := by
    intro a
    have he := (Lp.coeFn_compMeasurePreserving q
      (measurePreserving_smul a μ)).symm
    have hf := hfixed a.toAdd
    change Lp.compMeasurePreserving (fun x => a • x)
      (measurePreserving_smul a μ) q = q at hf
    rwa [hf] at he
  obtain ⟨c, hc⟩ := ae_eq_const_of_group_invariant μ q (Lp.aestronglyMeasurable q) hqae
  have hqconst : q = constantL2 μ c := Lp.ext (hc.trans (constantL2_ae μ c).symm)
  rw [hqconst] at hA
  have hmean := (meanL2 μ).continuous.tendsto (constantL2 μ c) |>.comp hA
  have hconst : Tendsto (fun N => meanL2 μ (A N)) atTop (𝓝 (meanL2 μ F)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (meanL2_birkhoffAverage μ T hT F N (Nat.ne_of_gt hN)).symm
  have hcmean := tendsto_nhds_unique hmean hconst
  rw [meanL2_constant, meanL2_apply] at hcmean
  have hFg : (∫ x, F x ∂μ) = ∫ x, g x ∂μ := integral_congr_ae hg.coeFn_toLp
  rw [hFg] at hcmean
  simpa only [A, hVe, F, g, T, hcmean] using hA

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_UnitFlowSmoothing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded observable smoothing for an ergodic real flow

Unit smoothing is measurable, bounded, and preserves the integral.
Its discrete averages have an actual L1 limit under flow ergodicity.
Together with the maximal estimate this gives fixed large-measure sets
that control every sufficiently long integer flow window.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction (Multiplicative ℝ) X] [ContinuousSMul (Multiplicative ℝ) X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_flow_observable (f : X →ᵇ ℝ) :
    Continuous (fun p : ℝ × X => f (realActionTime p.1 p.2)) := by
  unfold realActionTime
  fun_prop

lemma measurable_unitFlowSmooth (f : X →ᵇ ℝ) :
    Measurable (unitFlowSmooth realActionTime f) := by
  have hj : StronglyMeasurable (fun p : X × ℝ => f (realActionTime p.2 p.1)) :=
    ((continuous_flow_observable f).comp continuous_swap).stronglyMeasurable
  have hm := hj.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  unfold unitFlowSmooth
  simpa only [intervalIntegral.integral_of_le zero_le_one] using hm.measurable

omit [MeasurableSpace X] [BorelSpace X] [ContinuousSMul (Multiplicative ℝ) X] in
lemma unitFlowSmooth_abs_le (f : X →ᵇ ℝ) (x : X) :
    |unitFlowSmooth realActionTime f x| ≤ ‖f‖ := by
  simpa only [unitFlowSmooth, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => f (realActionTime t x))
      (a := 0) (b := 1) (C := ‖f‖)
      (fun t _ => f.norm_coe_le_norm (realActionTime t x)))

lemma memLp_unitFlowSmooth (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ ℝ) :
    MemLp (unitFlowSmooth realActionTime f) 2 μ :=
  MemLp.of_bound (measurable_unitFlowSmooth f).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using unitFlowSmooth_abs_le f x)

lemma unitFlowSmooth_integral_eq (μ : Measure X) [IsFiniteMeasure μ]
    [SMulInvariantMeasure (Multiplicative ℝ) X μ] (f : X →ᵇ ℝ) :
    (∫ x, unitFlowSmooth realActionTime f x ∂μ) = ∫ x, f x ∂μ := by
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
    rw [uIoc_of_le zero_le_one]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hi : Integrable (fun p : ℝ × X => f (realActionTime p.1 p.2))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) :=
    memLp_one_iff_integrable.mp (MemLp.of_bound
      (continuous_flow_observable f).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun p => f.norm_coe_le_norm (realActionTime p.1 p.2)))
  have he (t : ℝ) : (∫ x, f (realActionTime t x) ∂μ) = ∫ x, f x ∂μ := by
    have hp : MeasurePreserving (realActionTime t) μ μ :=
      measurePreserving_smul (Multiplicative.ofAdd t) μ
    have hmap := integral_map hp.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x => f x) (μ.map (realActionTime t)) from
        by rw [hp.map_eq]; exact f.continuous.aestronglyMeasurable)
    rw [hp.map_eq] at hmap
    exact hmap.symm
  unfold unitFlowSmooth
  rw [← intervalIntegral_integral_swap hi]
  simp_rw [he]
  simp

/-- The genuine continuous-flow windows converge in L1 at integer
lengths. Full-flow ergodicity is the only ergodicity hypothesis. -/
theorem L1_integer_flow_windows_tendsto_integral
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) X μ]
    (f : X →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ x,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) -
        ∫ y, f y ∂μ| ∂μ) atTop (𝓝 0) := by
  let g : X → ℝ := unitFlowSmooth realActionTime f
  have hg := memLp_unitFlowSmooth μ f
  have ht : ∀ x a b, IntervalIntegrable (fun t => f (realActionTime t x)) volume a b :=
    fun x a b => ((continuous_flow_observable f).comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hL2 := L2_unit_smoothed_real_action_tendsto_integral μ f ‖f‖ (norm_nonneg f)
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) ht hg
  have hL1 := L1_tendsto_of_L2_tendsto_constant μ _ _ hL2
  change Tendsto (fun N : ℕ => ∫ x,
    |(birkhoffAverage ℝ (Lp.compMeasurePreserving (realActionTime 1)
      (measurePreserving_smul (Multiplicative.ofAdd 1) μ)) id N (hg.toLp g)) x -
      ∫ y, g y ∂μ| ∂μ) atTop (𝓝 0) at hL1
  have he (N : ℕ) :
      (∫ x, |(birkhoffAverage ℝ
        (Lp.compMeasurePreserving (realActionTime 1)
          (measurePreserving_smul (Multiplicative.ofAdd 1) μ)) id N (hg.toLp g)) x -
          ∫ y, g y ∂μ| ∂μ) =
      ∫ x, |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) -
          ∫ y, f y ∂μ| ∂μ := by
    apply integral_congr_ae
    have hrep := (Lp_orbit_average_ae μ (realActionTime 1)
      (measurePreserving_smul (Multiplicative.ofAdd 1) μ) (hg.toLp g) N).trans
      (orbit_average_congr_ae μ (realActionTime 1)
        (measurePreserving_smul (Multiplicative.ofAdd 1) μ) hg.coeFn_toLp N)
    filter_upwards [hrep] with x hx
    rw [hx, birkhoffAverage_unitFlowSmooth realActionTime f realActionTime_zero
      realActionTime_add ht, unitFlowSmooth_integral_eq μ f]
  simpa only [he] using hL1

/-- A fixed large-measure set works for all sufficiently large integer
flow windows, including a window length selected from a pair of points. -/
theorem exists_uniform_integer_flow_generic_set
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) X μ]
    (f : X →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set X, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀,
        |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (realActionTime t x)) -
          ∫ y, f y ∂μ| ≤ ε := by
  let g : X → ℝ := unitFlowSmooth realActionTime f
  have ht : ∀ x a b, IntervalIntegrable (fun t => f (realActionTime t x)) volume a b :=
    fun x a b => ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hmean : Tendsto (fun N : ℕ => ∫ x,
      |birkhoffAverage ℝ (realActionTime 1) g N x - ∫ y, f y ∂μ| ∂μ)
      atTop (𝓝 0) := by
    simpa only [g, birkhoffAverage_unitFlowSmooth realActionTime f
      realActionTime_zero realActionTime_add ht] using L1_integer_flow_windows_tendsto_integral μ f
  obtain ⟨G, hG, hGμ, N₀, hN₀⟩ := exists_uniform_generic_set_of_L1_convergence μ
    (realActionTime 1) (measurePreserving_smul (Multiplicative.ofAdd 1) μ)
    g (measurable_unitFlowSmooth f)
    (memLp_one_iff_integrable.mp ((memLp_unitFlowSmooth μ f).mono_exponent (by norm_num)))
    ‖f‖ (norm_nonneg f) (unitFlowSmooth_abs_le f) (∫ y, f y ∂μ) hmean ε δ hε hδ
  refine ⟨G, hG, hGμ, N₀, ?_⟩
  intro x hx N hN
  simpa only [g, birkhoffAverage_unitFlowSmooth realActionTime f
    realActionTime_zero realActionTime_add ht] using hN₀ x hx N hN

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RealFlowWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real stopping times for bounded flow averages

An arbitrary real window differs from its integer part by a boundary
interval of length at most one.  The estimate is uniform in the initial
point, so the same good set works for stopping times selected from a pair.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

lemma normalized_integral_nearby_length_bound
    (F : ℝ → ℝ) (hint : ∀ a b, IntervalIntegrable F volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, |F t| ≤ C)
    (L T : ℝ) (hL : 0 < L) (hLT : L ≤ T) (hTL : T ≤ L + 1) :
    |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) -
        L⁻¹ * (∫ t in (0 : ℝ)..L, F t)| ≤ 2 * C / L := by
  have hT : 0 < T := hL.trans_le hLT
  have hJ : |∫ t in L..T, F t| ≤ C := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
      (a := L) (b := T) (C := C) (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
    simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hLT)] at hb
    exact hb.trans (by nlinarith)
  have hI : |∫ t in (0 : ℝ)..L, F t| ≤ C * L := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hL] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
        (a := 0) (b := L) (C := C)
        (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t))
  have hinv : T⁻¹ ≤ L⁻¹ := (inv_le_inv₀ hT hL).mpr hLT
  have hcoef : |T⁻¹ - L⁻¹| * (C * L) ≤ C / L := by
    rw [abs_of_nonpos (sub_nonpos.mpr hinv)]
    have heq : -(T⁻¹ - L⁻¹) * (C * L) = C * (T - L) / T := by
      field_simp [ne_of_gt hT, ne_of_gt hL]
      ring
    rw [heq]
    calc
      C * (T - L) / T ≤ C / T := by
        exact div_le_div_of_nonneg_right (by nlinarith) hT.le
      _ ≤ C / L := div_le_div_of_nonneg_left hC hL hLT
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 L) (hint L T)]
  have heq : T⁻¹ * ((∫ t in (0 : ℝ)..L, F t) + ∫ t in L..T, F t) -
      L⁻¹ * (∫ t in (0 : ℝ)..L, F t) =
      T⁻¹ * (∫ t in L..T, F t) +
        (T⁻¹ - L⁻¹) * (∫ t in (0 : ℝ)..L, F t) := by ring
  rw [heq]
  calc
    _ ≤ |T⁻¹ * (∫ t in L..T, F t)| +
        |(T⁻¹ - L⁻¹) * (∫ t in (0 : ℝ)..L, F t)| := abs_add_le _ _
    _ = T⁻¹ * |∫ t in L..T, F t| +
        |T⁻¹ - L⁻¹| * |∫ t in (0 : ℝ)..L, F t| := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hT)]
    _ ≤ T⁻¹ * C + |T⁻¹ - L⁻¹| * (C * L) :=
      add_le_add (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hT.le))
        (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ ≤ C / L + C / L := by
      exact add_le_add (by simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_right hinv hC) hcoef
    _ = 2 * C / L := by ring

/-- Any real-time average has uniformly small distance from its integer
part once that integer part is positive. -/
lemma normalized_integral_floor_bound
    (F : ℝ → ℝ) (hint : ∀ a b, IntervalIntegrable F volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, |F t| ≤ C)
    (T : ℝ) (hT : 1 ≤ T) :
    |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) -
        (⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), F t)| ≤
      2 * C / (⌊T⌋₊ : ℝ) := by
  have hnonneg : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans hT
  have hfloor : 1 ≤ ⌊T⌋₊ := (Nat.le_floor_iff hnonneg).mpr (by simpa using hT)
  exact normalized_integral_nearby_length_bound F hint C hC hbound (⌊T⌋₊ : ℝ) T
    (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hfloor))
    (Nat.floor_le hnonneg) (Nat.lt_floor_add_one T).le

/-- Integer good-set control extends to all sufficiently large real
window lengths, retaining the same measurable set. -/
theorem real_window_control_of_integer_mean_control
    {Y : Type*} (U : ℝ → Y → Y) (f : Y → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (G : Set Y) (q : Y → ℝ) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ)
    (hgood : ∀ x ∈ G, ∀ N ≥ N₀,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (U t x)) - q x| ≤ ε / 2) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ T ≥ R,
      |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) - q x| ≤ ε := by
  have hlim : Tendsto (fun N : ℕ => 2 * C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  let M : ℕ := max 1 (max N₀ N₁)
  refine ⟨(M : ℝ), ?_, ?_⟩
  · exact_mod_cast (le_max_left 1 (max N₀ N₁))
  · intro x hx T hT
    have hM : 1 ≤ M := le_max_left _ _
    have hT₁ : 1 ≤ T := (show (1 : ℝ) ≤ (M : ℝ) by exact_mod_cast hM).trans hT
    have hT₀ : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans hT₁
    have hfM : M ≤ ⌊T⌋₊ := (Nat.le_floor_iff hT₀).mpr hT
    have hf₀ : N₀ ≤ ⌊T⌋₊ := (le_trans (le_max_left N₀ N₁) (le_max_right 1 _)).trans hfM
    have hf₁ : N₁ ≤ ⌊T⌋₊ := (le_trans (le_max_right N₀ N₁) (le_max_right 1 _)).trans hfM
    have hb := normalized_integral_floor_bound (fun t => f (U t x)) (hint x)
      C hC (fun t => hbound (U t x)) T hT₁
    have hg := hgood x hx ⌊T⌋₊ hf₀
    have hsmall := hN₁ ⌊T⌋₊ hf₁
    calc
      _ ≤ |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) -
          (⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), f (U t x))| +
          |(⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), f (U t x)) - q x| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub
          (T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)))
          ((⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), f (U t x))) (q x)
      _ ≤ 2 * C / (⌊T⌋₊ : ℝ) + ε / 2 := add_le_add hb hg
      _ ≤ ε := by linarith

/-- The constant-mean specialization retains the original generic-set API. -/
theorem real_window_control_of_integer_control
    {Y : Type*} (U : ℝ → Y → Y) (f : Y → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (G : Set Y) (c ε : ℝ) (hε : 0 < ε) (N₀ : ℕ)
    (hgood : ∀ x ∈ G, ∀ N ≥ N₀,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (U t x)) - c| ≤ ε / 2) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ T ≥ R,
      |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) - c| ≤ ε :=
  real_window_control_of_integer_mean_control U f hint C hC hbound G
    (fun _ => c) ε hε N₀ hgood

theorem exists_uniform_real_flow_generic_set
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : Y →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) - ∫ y, f y ∂μ| ≤ ε := by
  obtain ⟨G, hG, hGμ, N₀, hN₀⟩ := exists_uniform_integer_flow_generic_set
    μ f (ε / 2) δ (by positivity) hδ
  refine ⟨G, hG, hGμ, ?_⟩
  exact real_window_control_of_integer_control realActionTime f
    (fun x a b => ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    ‖f‖ (norm_nonneg f) (fun x => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    G (∫ y, f y ∂μ) ε hε N₀ hN₀

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingMeasureLimits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A limiting shear preserves the limiting measure

This is the measure step in the unipotent shearing argument. If two
families of probability measures have the same weak limit, and one is
the translate of the other by converging group elements, the limiting
element preserves that measure. Compact observables give uniform control
even when the sampled points leave every compact set.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace DukePrimeDegree

variable {G X I : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [TopologicalSpace X] [LocallyCompactSpace X]
  [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {l : Filter I} [NeBot l]

omit [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [NeBot l] in
/-- Moving translations of a compact observable converge uniformly. -/
lemma compact_observable_varying_smul
    (f : X → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ x,
      |f (a i • x) - f (g • x)| < ε := by
  have hid : Tendsto (fun i => a i * g⁻¹) l (𝓝 1) := by
    simpa only [mul_inv_cancel] using ha.mul_const g⁻¹
  intro ε hε
  have hu := Metric.tendstoUniformly_iff.mp
    (compact_observable_smul_tendstoUniformly (G := G) f hf hc) ε hε
  filter_upwards [hid.eventually hu] with i hi x
  simpa only [mul_smul, inv_smul_smul, Real.dist_eq, abs_sub_comm] using hi (g • x)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactFamilyGeneric
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A fixed generic set for a compact family of observables

The limiting shear is selected after the generic set. Compactness of the
possible shears gives a compact family of translated observables in the
uniform norm. A finite approximation therefore suffices for one common
generic set and time threshold. No commutation of the translating group
with the averaging flow is required.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

theorem exists_finite_uniform_real_flow_generic_set
    {Y I : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    [Fintype I]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : I → Y →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ i, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f i (realActionTime t x)) -
          ∫ y, f i y ∂μ| ≤ ε := by
  classical
  let a : ℝ := δ / (Fintype.card I + 1)
  have ha : 0 < a := div_pos hδ (by positivity)
  choose G hG hGμ R hR hgood using
    fun i => exists_uniform_real_flow_generic_set μ (f i) ε a hε ha
  let N := Finset.univ.sup (fun i => ⌈R i⌉₊)
  refine ⟨⋂ i, G i, MeasurableSet.iInter hG, ?_, max 1 (N : ℝ), le_max_left _ _, ?_⟩
  · rw [compl_iInter]
    calc
      μ (⋃ i, (G i)ᶜ) ≤ ∑ i, μ (G i)ᶜ := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _i : I, ENNReal.ofReal a := Finset.sum_le_sum (fun i _ => hGμ i)
      _ = ENNReal.ofReal ((Fintype.card I : ℝ) * a) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => ha.le)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [a]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card I + 1)]
        nlinarith
  · intro x hx i T hT
    apply hgood i x (mem_iInter.mp hx i) T
    have hi : ⌈R i⌉₊ ≤ N := Finset.le_sup (f := fun i => ⌈R i⌉₊) (Finset.mem_univ i)
    have hi' : (⌈R i⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    exact (Nat.le_ceil (R i)).trans (hi'.trans
      ((le_max_right 1 (N : ℝ)).trans hT))

lemma flow_average_error_of_uniform_approximation
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f g : Y →ᵇ ℝ) (b ε : ℝ) (_hb : 0 ≤ b)
    (hfg : dist f g ≤ b) (x : Y) (T : ℝ) (hT : 0 < T)
    (hf : |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) -
      ∫ y, f y ∂μ| ≤ ε) :
    |T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) -
      ∫ y, g y ∂μ| ≤ ε + 2 * b := by
  have hpoint (y : Y) : |f y - g y| ≤ b := by
    simpa only [Real.dist_eq] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) y).trans hfg
  have hmean : |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤ b := by
    rw [← integral_sub (f.integrable (μ := μ)) (g.integrable (μ := μ))]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun y => f y - g y) (C := b)
      (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hpoint y))
    have hμ : μ.real univ = 1 := by simp
    simpa only [Real.norm_eq_abs, hμ, mul_one] using h
  have hfi : IntervalIntegrable (fun t => f (realActionTime t x)) volume 0 T :=
    ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 T
  have hgi : IntervalIntegrable (fun t => g (realActionTime t x)) volume 0 T :=
    ((continuous_flow_observable g).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 T
  have havg : |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) -
      T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x))| ≤ b := by
    rw [← mul_sub, ← intervalIntegral.integral_sub hfi hgi, abs_mul,
      abs_of_pos (inv_pos.mpr hT)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => f (realActionTime t x) - g (realActionTime t x))
      (a := 0) (b := T) (C := b)
      (fun t _ => by simpa only [Real.norm_eq_abs] using hpoint (realActionTime t x))
    have h' : |∫ t in (0 : ℝ)..T,
        f (realActionTime t x) - g (realActionTime t x)| ≤ b * T := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hT] using h
    calc
      _ ≤ T⁻¹ * (b * T) := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hT.le)
      _ = b := by field_simp
  have hd : T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) - ∫ y, g y ∂μ =
      (T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) -
        T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x))) +
      (T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) - ∫ y, f y ∂μ) +
      ((∫ y, f y ∂μ) - ∫ y, g y ∂μ) := by ring
  rw [hd]
  calc
    _ ≤ |T⁻¹ * (∫ t in (0 : ℝ)..T, g (realActionTime t x)) -
          T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x))| +
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) - ∫ y, f y ∂μ| +
        |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ b + ε + b := add_le_add
      (add_le_add (by simpa only [abs_sub_comm] using havg) hf) hmean
    _ = ε + 2 * b := by ring

/-- Compactness is in the uniform norm on bounded continuous functions. -/
theorem exists_compact_family_real_flow_generic_set
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (K : Set (Y →ᵇ ℝ)) (hK : IsCompact K)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ f ∈ K, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) -
          ∫ y, f y ∂μ| ≤ ε := by
  classical
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover
    (fun f : K => Metric.ball f.val (ε / 4)) (fun _ => Metric.isOpen_ball)
    (fun f hf => mem_iUnion.mpr ⟨⟨f, hf⟩, Metric.mem_ball_self (by positivity)⟩)
  obtain ⟨G, hG, hGμ, R, hR, hgood⟩ :=
    exists_finite_uniform_real_flow_generic_set μ
      (fun i : J => i.val.val) (ε / 2) δ (by positivity) hδ
  refine ⟨G, hG, hGμ, R, hR, ?_⟩
  intro x hx f hf T hT
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hJ hf)
  have hdist : dist g.val f ≤ ε / 4 := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hfg).le
  have h := flow_average_error_of_uniform_approximation μ g.val f
    (ε / 4) (ε / 2) (by positivity) hdist x T
    (lt_of_lt_of_le zero_lt_one (hR.trans hT)) (hgood x hx ⟨g, hg⟩ T hT)
  linarith

theorem continuous_compactObservableTranslate
    {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [WeaklyLocallyCompactSpace H] [TopologicalSpace Y]
    [MulAction H Y] [ContinuousSMul H Y]
    (f : CompactlySupportedContinuousMap Y ℝ) :
    Continuous (compactObservableTranslate (H := H) f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [compact_observable_varying_smul f f.continuous f.hasCompactSupport
    (id : H → H) a tendsto_id ε hε] with b hb x
  simpa only [compactObservableTranslate, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
    id_eq, Real.dist_eq, abs_sub_comm] using hb x

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerMetric
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed vectors from small group sandwiches

These metric arguments are the part of the Mautner phenomenon needed
for the actual root-pair calculation. They apply to the continuous
isometric action on L². No ergodicity or homogeneous-orbit premise is
introduced.
-/

noncomputable section
open Filter
open scoped Topology

namespace DukePrimeDegree

variable {G Y : Type*} [Group G] [TopologicalSpace G]
  [MetricSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [IsIsometricSMul G Y]

omit [TopologicalSpace G] [ContinuousSMul G Y] in
lemma dist_sandwich_of_fixed (x : Y) (a b c : G)
    (ha : a • x = x) (hb : b • x = x) :
    dist ((a * c * b) • x) x = dist (c • x) x := by
  rw [mul_smul, mul_smul, hb]
  calc
    dist (a • (c • x)) x = dist (a • (c • x)) (a • x) := by rw [ha]
    _ = dist (c • x) x := dist_smul a _ _

/-- Large left and right factors which fix the vector may squeeze a
small middle factor to a nontrivial group limit. That limit still fixes
the vector because both outer factors act isometrically. -/
theorem fixed_of_sandwich_tendsto
    (x : Y) (a b c : ℕ → G) (g : G)
    (ha : ∀ k, a k • x = x) (hb : ∀ k, b k • x = x)
    (hc : Tendsto c atTop (𝓝 1))
    (hlim : Tendsto (fun k => a k * c k * b k) atTop (𝓝 g)) :
    g • x = x := by
  have hsmall : Tendsto (fun k => dist (c k • x) x) atTop (𝓝 0) := by
    simpa only [one_smul, dist_self] using
      (hc.smul_const x).dist (tendsto_const_nhds (x := x))
  have hdist : Tendsto (fun k => dist ((a k * c k * b k) • x) x)
      atTop (𝓝 0) := by
    exact hsmall.congr' (Eventually.of_forall fun k =>
      (dist_sandwich_of_fixed x (a k) (b k) (c k) (ha k) (hb k)).symm)
  have hvalue := (hlim.smul_const x).dist (tendsto_const_nhds (x := x))
  exact dist_eq_zero.mp (tendsto_nhds_unique hvalue hdist)

/-- The usual contraction form of Mautner: a group element contracted
to identity by elements fixing the vector also fixes the vector. -/
theorem fixed_of_conjugate_tendsto
    (x : Y) (a : ℕ → G) (g : G)
    (ha : ∀ k, a k • x = x)
    (hlim : Tendsto (fun k => a k * g * (a k)⁻¹) atTop (𝓝 1)) :
    g • x = x := by
  have hai (k : ℕ) : (a k)⁻¹ • x = x := by
    apply (MulAction.injective (a k))
    simpa only [smul_smul, mul_inv_cancel, one_smul] using (ha k).symm
  have hzero : Tendsto (fun k => dist ((a k * g * (a k)⁻¹) • x) x)
      atTop (𝓝 0) := by
    simpa only [one_smul, dist_self] using
      (hlim.smul_const x).dist (tendsto_const_nhds (x := x))
  have hconst : Tendsto (fun _ : ℕ => dist (g • x) x) atTop (𝓝 0) := by
    exact hzero.congr' (Eventually.of_forall fun k =>
      dist_sandwich_of_fixed x (a k) ((a k)⁻¹) g (ha k) (hai k))
  exact dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hconst)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerRootPair
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mautner's root-pair calculation inside the actual acting subgroup

The subgroup parameter is essential: the ambient finite measure is not
assumed invariant under all of SLₙ. The two opposite roots belong to its
invariant block group, and the isometric action is restricted to that
group. A concrete two-by-two identity supplies the diagonal fixed vector.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Root-fixed vectors are fixed by every nonzero root-pair diagonal.
The large root parameters are never estimated directly; the isometry
removes them before taking the limit. -/
theorem diag2n_fixed_of_root_fixed {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (H : Subgroup (G n))
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ H)
    (hV : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij.symm t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y]
    (x : Y) (hfix : ∀ t : ℝ,
      (⟨Matrix.SpecialLinearGroup.transvection hij t, hU t⟩ : H) • x = x)
    (a : ℝ) (ha : a ≠ 0) :
    (⟨Matrix.SpecialLinearGroup.diag2n hij a ha,
      diag2n_mem_of_opposite_roots hij H hU hV a ha⟩ : H) • x = x := by
  let s : ℕ → ℝ := fun k => (k : ℝ) + 1
  let t : ℕ → ℝ := fun k => (a - 1) / s k
  let A : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.transvection hij (s k), hU _⟩
  let B : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.transvection hij (-s k / a), hU _⟩
  let C : ℕ → H := fun k => ⟨Matrix.SpecialLinearGroup.transvection hij.symm (t k), hV _⟩
  let D : H := ⟨Matrix.SpecialLinearGroup.diag2n hij a ha,
    diag2n_mem_of_opposite_roots hij H hU hV a ha⟩
  have hs (k : ℕ) : s k ≠ 0 := by dsimp only [s] <;> positivity
  have hstop : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop (𝓝 0) := tendsto_const_nhds.div_atTop hstop
  have hC : Tendsto C atTop (𝓝 1) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun k => Matrix.SpecialLinearGroup.transvection hij.symm (t k))
      atTop (𝓝 (1 : G n))
    simpa only [C, Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
      (continuous_rootTransvection hij.symm).continuousAt.tendsto.comp ht
  have hsmall : Tendsto (fun k => (a - 1) / (s k * a)) atTop (𝓝 0) := by
    have he (k : ℕ) : (a - 1) / (s k * a) = t k / a := by
      dsimp only [t]
      rw [div_div]
    simp_rw [he]
    simpa only [zero_div] using ht.div_const a
  have hlim : Tendsto (fun k => A k * C k * B k) atTop (𝓝 D) := by
    apply tendsto_subtype_rng.mpr
    have he (k : ℕ) : (A k * C k * B k : H).val =
        Matrix.SpecialLinearGroup.transvection hij.symm ((a - 1) / (s k * a)) * D.val :=
      root_pair_gauss_identity hij a (s k) ha (hs k)
    simp_rw [he]
    simpa only [Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul] using
      ((continuous_rootTransvection hij.symm).continuousAt.tendsto.comp hsmall).mul_const D.val
  exact fixed_of_sandwich_tendsto x A B C D (fun k => hfix _) (fun k => hfix _) hC hlim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerBlock
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A root fixed vector is fixed by its whole coordinate block

The ambient acting group is still the specified measure stabilizer.  It
only needs to contain the root groups inside the chosen coordinate set.
The root-pair diagonal contracts every root touching its first pivot;
commutators then supply the remaining roots of that coordinate block.
This is the fixed-vector step for using a genuine unipotent ergodic flow
on a component of one block group, without a diagonal-ergodicity premise.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonalOneParameter_rootPair_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (t : ℝ) :
    diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j) t =
      Matrix.SpecialLinearGroup.diag2n hij (Real.exp t) (Real.exp_ne_zero t) := by
  apply Subtype.ext
  apply congrArg Matrix.diagonal
  funext k
  by_cases hki : k = i
  · subst k
    simp [rootIsolationWeights, hij]
  · by_cases hkj : k = j
    · subst k
      simp [rootIsolationWeights, hij.symm, Real.exp_neg]
    · simp [rootIsolationWeights, hki, hkj]

/-- A diagonal group that fixes a vector also fixes each root with
nonzero weight.  The contracting times are chosen explicitly. -/
theorem root_fixed_of_diagonal_fixed {n : ℕ}
    (H : Subgroup (G n)) (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (hD : ∀ t, diagonalOneParameter ell hell t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y] (x : Y)
    (hfix : ∀ t : ℝ, (⟨diagonalOneParameter ell hell t, hD t⟩ : H) • x = x)
    {p q : Fin n} (hpq : p ≠ q)
    (hU : ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hpq t ∈ H)
    (hw : ell p ≠ ell q) (s : ℝ) :
    (⟨Matrix.SpecialLinearGroup.transvection hpq s, hU s⟩ : H) • x = x := by
  let times : ℕ → ℝ := fun k => -(k : ℝ) / (ell p - ell q)
  let D : ℕ → H := fun k => ⟨diagonalOneParameter ell hell (times k), hD _⟩
  let u : H := ⟨Matrix.SpecialLinearGroup.transvection hpq s, hU s⟩
  apply fixed_of_conjugate_tendsto x D u (fun k => hfix (times k))
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k => (D k * u * (D k)⁻¹ : H).val) atTop (𝓝 (1 : G n))
  have hweight : ell p - ell q ≠ 0 := sub_ne_zero.mpr hw
  have he (k : ℕ) : (D k * u * (D k)⁻¹ : H).val =
      Matrix.SpecialLinearGroup.transvection hpq (Real.exp (-(k : ℝ)) * s) := by
    change diagonalOneParameter ell hell (times k) *
      Matrix.SpecialLinearGroup.transvection hpq s *
      (diagonalOneParameter ell hell (times k))⁻¹ = _
    rw [← diagonalOneParameter_neg, diagonal_conjugation_transvection]
    have ht : (ell p - ell q) * times k = -(k : ℝ) := by
      dsimp only [times]
      field_simp [hweight]
    rw [ht]
  have hparam : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ)) * s) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).mul_const s
  simp_rw [he]
  simpa only [Function.comp_def, Matrix.SpecialLinearGroup.transvection_coeff_zero] using
    (continuous_rootTransvection hpq).continuousAt.tendsto.comp hparam

/-- Only the roots with both endpoints in `S` are used.  In particular,
the theorem does not assert ergodicity of a root across distinct blocks. -/
theorem block_roots_fixed_of_one_root_fixed {n : ℕ}
    (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (H : Subgroup (G n))
    (hroot : ∀ p ∈ S, ∀ q ∈ S, ∀ (hpq : p ≠ q) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hpq t ∈ H)
    {Y : Type*} [MetricSpace Y] [MulAction H Y] [ContinuousSMul H Y]
    [IsIsometricSMul H Y] (x : Y)
    (hfix : ∀ t : ℝ,
      (⟨Matrix.SpecialLinearGroup.transvection hij t, hroot i hi j hj hij t⟩ : H) • x = x)
    (p : Fin n) (hp : p ∈ S) (q : Fin n) (hq : q ∈ S)
    (hpq : p ≠ q) (t : ℝ) :
    (⟨Matrix.SpecialLinearGroup.transvection hpq t, hroot p hp q hq hpq t⟩ : H) • x = x := by
  let ell := rootIsolationWeights i j
  have hell : ∑ k, ell k = 0 := rootIsolationWeights_sum i j
  have hD (a : ℝ) : diagonalOneParameter ell hell a ∈ H := by
    rw [diagonalOneParameter_rootPair_eq hij]
    exact diag2n_mem_of_opposite_roots hij H (hroot i hi j hj hij)
      (hroot j hj i hi hij.symm) _ (Real.exp_ne_zero a)
  have hDx (a : ℝ) : (⟨diagonalOneParameter ell hell a, hD a⟩ : H) • x = x := by
    have h := diag2n_fixed_of_root_fixed hij H (hroot i hi j hj hij)
      (hroot j hj i hi hij.symm) x hfix (Real.exp a) (Real.exp_ne_zero a)
    have he : (⟨diagonalOneParameter ell hell a, hD a⟩ : H) =
        ⟨Matrix.SpecialLinearGroup.diag2n hij (Real.exp a) (Real.exp_ne_zero a),
          diag2n_mem_of_opposite_roots hij H (hroot i hi j hj hij)
            (hroot j hj i hi hij.symm) _ (Real.exp_ne_zero a)⟩ :=
      Subtype.ext (diagonalOneParameter_rootPair_eq hij a)
    rw [he]
    exact h
  have hweight (k : Fin n) (hki : k ≠ i) : ell k ≠ ell i := by
    by_cases hkj : k = j
    · subst k
      norm_num [ell, rootIsolationWeights, hij, hij.symm]
    · simp [ell, rootIsolationWeights, hki, hkj, hij]
  have hpivot (k : Fin n) (hk : k ∈ S) (hki : k ≠ i) (s : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hki s, hroot k hk i hi hki s⟩ : H) • x = x :=
    root_fixed_of_diagonal_fixed H ell hell hD x hDx hki
      (hroot k hk i hi hki) (hweight k hki) s
  have hpivot' (k : Fin n) (hk : k ∈ S) (hik : i ≠ k) (s : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hik s, hroot i hi k hk hik s⟩ : H) • x = x :=
    root_fixed_of_diagonal_fixed H ell hell hD x hDx hik
      (hroot i hi k hk hik) (Ne.symm (hweight k hik.symm)) s
  by_cases hpi : p = i
  · subst p
    exact hpivot' q hq hpq t
  by_cases hqi : q = i
  · subst q
    exact hpivot p hp hpq t
  have hiq : i ≠ q := Ne.symm hqi
  let a (s : ℝ) : H := ⟨Matrix.SpecialLinearGroup.transvection hpi s,
    hroot p hp i hi hpi s⟩
  let b (s : ℝ) : H := ⟨Matrix.SpecialLinearGroup.transvection hiq s,
    hroot i hi q hq hiq s⟩
  have he : a t * b 1 * a (-t) * b (-1) =
      (⟨Matrix.SpecialLinearGroup.transvection hpq t,
        hroot p hp q hq hpq t⟩ : H) := by
    apply Subtype.ext
    simpa only [a, b, Subgroup.coe_mul, Subgroup.coe_mk, mul_one] using
      transvection_chain_commutator hpi hiq hpq t (1 : ℝ)
  have ha_fixed (s : ℝ) : a s • x = x := hpivot p hp hpi s
  have hb_fixed (s : ℝ) : b s • x = x := hpivot' q hq hiq s
  rw [← he]
  simp only [mul_smul, ha_fixed, hb_fixed]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LatticeGroupDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The lattice group action and its ergodic components

Taking inverses writes the right lattice action as a left action.
Measurable ergodic decomposition gives probability components for each
closed matrix subgroup preserving the measure. Adjoining an invariant
subgroup to the diagonal action preserves invariance and ergodicity
of a diagonal-ergodic probability, as required by Margulis--Tomanov.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma latticeSubgroup_preserving {n : ℕ} (H : Subgroup (G n))
    (μ : Measure (X n)) (hH : H ≤ invariantRightSubgroup μ) (h : H) :
    MeasurePreserving (fun x : X n => h • x) μ μ :=
  ⟨(continuous_rightAction h.val⁻¹).measurable, hH (H.inv_mem h.property)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerLatticeL2
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mautner for the actual lattice L² action

Only the specified subgroup preserves the measure. Pullback by its
right action is a continuous isometric action on L². Thus a root-flow
invariant L² observable is also invariant under the opposite root and
the associated diagonal elements of that subgroup.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_inverseDomainHom (H : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] : Continuous (inverseDomainHom H) :=
  DomMulAct.continuous_mk.comp continuous_inv

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MautnerBlockL2
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-block Mautner argument on actual lattice observables

A root-invariant square-integrable observable is invariant under every
root of the same coordinate block, provided those roots preserve the
measure.  The group used in the proof is the specified subgroup, not the
full special linear group.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_block_root_fixed_of_L2_root_fixed {n : ℕ}
    (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (H : Subgroup (G n)) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (hroot : ∀ p ∈ S, ∀ q ∈ S, ∀ (hpq : p ≠ q) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hpq t ∈ H)
    (f : Lp ℝ 2 μ)
    (hfix : ∀ t : ℝ,
      (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hij t))) =ᵐ[μ] f)
    (p : Fin n) (hp : p ∈ S) (q : Fin n) (hq : q ∈ S)
    (hpq : p ≠ q) (t : ℝ) :
    (fun x => f (rightAction x (Matrix.SpecialLinearGroup.transvection hpq t))) =ᵐ[μ] f := by
  let : SMulInvariantMeasure H (X n) μ :=
    ⟨fun h s hs => (latticeSubgroup_preserving H μ hH h).measure_preimage hs.nullMeasurableSet⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MulAction H (Lp ℝ 2 μ) := MulAction.compHom _ (inverseDomainHom H)
  let : ContinuousSMul H (Lp ℝ 2 μ) :=
    MulAction.continuousSMul_compHom (continuous_inverseDomainHom H)
  let : IsIsometricSMul H (Lp ℝ 2 μ) :=
    ⟨fun h => isometry_smul (Lp ℝ 2 μ) (inverseDomainHom H h)⟩
  have hrep (h : H) : (h • f : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => f (rightAction x h.val)) := by
    have he := DomMulAct.smul_Lp_ae_eq (inverseDomainHom H h) f
    change (h • f : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x => f (rightAction x (h.val⁻¹)⁻¹)) at he
    simpa only [inv_inv] using he
  have hrootfix (u : ℝ) :
      (⟨Matrix.SpecialLinearGroup.transvection hij u, hroot i hi j hj hij u⟩ : H) • f = f :=
    Lp.ext ((hrep _).trans (hfix u))
  have hpqfix := block_roots_fixed_of_one_root_fixed S hij hi hj H hroot f hrootfix
    p hp q hq hpq t
  simpa only [hpqfix] using (hrep ⟨_, hroot p hp q hq hpq t⟩).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ReverseRootFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reverse root flow used by a right-action shearing pair

For points separated on the right by g, sampling both at U(-t) gives
relative displacement U(t) g U(-t). This action has exactly the same
invariant sets as the original root flow, so its ergodicity follows
from full real-root ergodicity, without selecting a discrete time.
-/

noncomputable section
open MeasureTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma reverseRootTranslationAction_continuous {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) :
    let := reverseRootTranslationAction hij
    ContinuousSMul (Multiplicative ℝ) (X n) := by
  let := reverseRootTranslationAction hij
  constructor
  have hu : Continuous (fun t : Multiplicative ℝ =>
      Matrix.SpecialLinearGroup.transvection hij (-t.toAdd)) :=
    (continuous_rootTransvection hij).comp (by fun_prop)
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk (hu.comp continuous_fst))

theorem reverseRootTranslationAction_ergodic {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n))
    (herg : let := rootTranslationAction hij
      ErgodicSMul (Multiplicative ℝ) (X n) μ) :
    let := reverseRootTranslationAction hij
    ErgodicSMul (Multiplicative ℝ) (X n) μ := by
  let := reverseRootTranslationAction hij
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro t B hB
    change μ ((fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij (-t.toAdd))) ⁻¹' B) = μ B
    let := rootTranslationAction hij
    let : ErgodicSMul (Multiplicative ℝ) (X n) μ := herg
    exact SMulInvariantMeasure.measure_preimage_smul
      (Multiplicative.ofAdd (-t.toAdd)) hB
  · intro B hB hfix
    have hf (t : Multiplicative ℝ) :
        (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t.toAdd)) ⁻¹' B =ᵐ[μ] B := by
      have ht := hfix (Multiplicative.ofAdd (-t.toAdd))
      change (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij (-(-t.toAdd)))) ⁻¹' B =ᵐ[μ] B at ht
      simpa only [neg_neg] using ht
    let := rootTranslationAction hij
    let : ErgodicSMul (Multiplicative ℝ) (X n) μ := herg
    exact ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hB hf

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootPairErgodicity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ergodicity of a root inside its actual two-root group

The chosen root is ergodic on an ergodic component of the group generated
by it and its opposite. This follows from the concrete Mautner argument,
not from an implication from diagonal ergodicity. Only the two-root group
is required to preserve the measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace DukePrimeDegree
open PrimeDegreePackets

lemma subgroup_le_invariantRightSubgroup_of_invariant_action {n : ℕ}
    (H : Subgroup (G n)) (μ : Measure (X n)) [SMulInvariantMeasure H (X n) μ] :
    H ≤ invariantRightSubgroup μ := by
  intro g hg
  have hp := (measurePreserving_smul (⟨g, hg⟩ : H)⁻¹ μ).map_eq
  change μ.map (fun x => rightAction x ((g⁻¹)⁻¹)) = μ at hp
  change μ.map (fun x => rightAction x g) = μ
  simpa only [inv_inv] using hp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockErgodicity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An actual ergodic root flow on a single block component

For a fixed coordinate block, the group generated by its root groups has
the same invariant measurable sets as any one of its nontrivial root
flows.  The Mautner argument proves this for the actual lattice action.
The coordinate block is not required to be the whole ambient space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_mem_singleBlockRootGroup {n : ℕ} (S : Set (Fin n))
    (p : Fin n) (hp : p ∈ S) (q : Fin n) (hq : q ∈ S) (hpq : p ≠ q) (t : ℝ) :
    Matrix.SpecialLinearGroup.transvection hpq t ∈ singleBlockRootGroup S :=
  Subgroup.subset_closure ⟨p, q, hpq, t, hp, hq, rfl⟩

lemma singleBlockRootGroup_le_of_roots {n : ℕ} (S : Set (Fin n))
    (H : Subgroup (G n))
    (hroot : ∀ p ∈ S, ∀ q ∈ S, ∀ (hpq : p ≠ q) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hpq t ∈ H) :
    singleBlockRootGroup S ≤ H := by
  rw [singleBlockRootGroup, Subgroup.closure_le]
  rintro g ⟨p, q, hpq, t, hp, hq, rfl⟩
  exact hroot p hp q hq hpq t

/-- The one-parameter subgroup used for generic points is ergodic on a
genuine single-block ergodic component.  No diagonal-ergodicity input is
used, and other blocks need not act ergodically on that component. -/
theorem root_ergodic_of_single_block_ergodic {n : ℕ}
    (S : Set (Fin n)) {i j : Fin n} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    [ErgodicSMul (singleBlockRootGroup S) (X n) μ] :
    let := rootTranslationAction hij
    ErgodicSMul (Multiplicative ℝ) (X n) μ := by
  classical
  let H := singleBlockRootGroup S
  have hH : H ≤ invariantRightSubgroup μ :=
    subgroup_le_invariantRightSubgroup_of_invariant_action H μ
  have hroot := root_mem_singleBlockRootGroup S
  have hpU (t : ℝ) : MeasurePreserving (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij t)) μ μ :=
    ⟨(continuous_rightAction _).measurable, hH (hroot i hi j hj hij t)⟩
  let := rootTranslationAction hij
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro t B hB
    exact (hpU t.toAdd).measure_preimage hB.nullMeasurableSet
  · intro B hB hBU
    let q : X n → ℝ := B.indicator (fun _ => (1 : ℝ))
    have hq : MemLp q 2 μ := (memLp_const (1 : ℝ)).indicator hB
    let F : Lp ℝ 2 μ := hq.toLp q
    have hF : (F : X n → ℝ) =ᵐ[μ] q := hq.coeFn_toLp
    have hFroot (t : ℝ) : (fun x => F (rightAction x
        (Matrix.SpecialLinearGroup.transvection hij t))) =ᵐ[μ] F := by
      filter_upwards [(hpU t).quasiMeasurePreserving.ae_eq_comp hF,
        hF, (hBU (Multiplicative.ofAdd t)).mem_iff] with x hleft hright hmem
      change F (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        q (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) at hleft
      change rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∈ B ↔ x ∈ B at hmem
      rw [hleft, hright]
      simp only [q, Set.indicator_apply, hmem]
    have hBroots (p : Fin n) (hp : p ∈ S) (q' : Fin n) (hq' : q' ∈ S)
        (hpq : p ≠ q') (t : ℝ) :
        (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hpq t)) ⁻¹' B =ᵐ[μ] B := by
      have hpV : MeasurePreserving (fun x => rightAction x
          (Matrix.SpecialLinearGroup.transvection hpq t)) μ μ :=
        ⟨(continuous_rightAction _).measurable, hH (hroot p hp q' hq' hpq t)⟩
      have hFV := ae_block_root_fixed_of_L2_root_fixed S hij hi hj H μ hH hroot
        F hFroot p hp q' hq' hpq t
      have hqV : (fun x => q (rightAction x
          (Matrix.SpecialLinearGroup.transvection hpq t))) =ᵐ[μ] q :=
        (hpV.quasiMeasurePreserving.ae_eq_comp hF).symm.trans (hFV.trans hF)
      apply Filter.Eventually.set_eq
      filter_upwards [hqV] with x hx
      change (rightAction x (Matrix.SpecialLinearGroup.transvection hpq t) ∈ B ↔ x ∈ B)
      by_cases hleft : rightAction x (Matrix.SpecialLinearGroup.transvection hpq t) ∈ B <;>
        by_cases hright : x ∈ B <;> simp_all [q]
    let K := (MulAction.aestabilizer H μ B).map H.subtype
    have hKroot (p : Fin n) (hp : p ∈ S) (q' : Fin n) (hq' : q' ∈ S)
        (hpq : p ≠ q') (t : ℝ) :
        Matrix.SpecialLinearGroup.transvection hpq t ∈ K := by
      refine Subgroup.mem_map.mpr ⟨⟨_, hroot p hp q' hq' hpq t⟩, ?_, rfl⟩
      rw [MulAction.mem_aestabilizer, ← preimage_smul_inv]
      change (fun x => rightAction x
        ((Matrix.SpecialLinearGroup.transvection hpq t)⁻¹)⁻¹) ⁻¹' B =ᵐ[μ] B
      simpa only [inv_inv] using hBroots p hp q' hq' hpq t
    have hHK : H ≤ K := singleBlockRootGroup_le_of_roots S K hKroot
    apply aeconst_of_forall_smul_ae_eq H hB.nullMeasurableSet
    intro h
    obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.mp (hHK h.property)
    have hkh : k = h := Subtype.ext hkval
    exact MulAction.mem_aestabilizer.mp (hkh ▸ hk)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TerminalGenericWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Generic control on a fixed terminal fraction of a real orbit

Polynomial shearing changes uniformly little on a sufficiently short
fixed terminal fraction.  Prefix genericity controls that fraction
with the explicit loss `2 / delta`.  The fraction is chosen after the
finite test accuracy, and is independent of the pair and stopping time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

theorem terminal_window_average_error
    (F : ℝ → ℝ) (c ε δ T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hT : 0 < T) (hε : 0 ≤ ε)
    (hint : ∀ a b, IntervalIntegrable F volume a b)
    (hfull : |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c| ≤ ε)
    (hprefix : |((1 - δ) * T)⁻¹ *
      (∫ t in (0 : ℝ)..((1 - δ) * T), F t) - c| ≤ ε) :
    |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, F t) - c| ≤ 2 * ε / δ := by
  let a := (1 - δ) * T
  have ha : 0 < a := mul_pos (sub_pos.mpr hδ1) hT
  have haT : a ≤ T := by dsimp only [a] <;> nlinarith
  have hdT : 0 < δ * T := mul_pos hδ hT
  have heq : (δ * T)⁻¹ * (∫ t in a..T, F t) - c =
      (δ * T)⁻¹ * (T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c) -
        a * (a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a T)]
    dsimp only [a]
    field_simp [ne_of_gt hδ, ne_of_gt hT, ne_of_gt (sub_pos.mpr hδ1)]
    ring
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hdT)]
  calc
    _ ≤ (δ * T)⁻¹ * (|T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c)| +
        |a * (a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c)|) := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdT.le)
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c)) 0
          (a * (a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c)))
    _ = (δ * T)⁻¹ * (T * |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c| +
        a * |a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c|) := by
      rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_pos ha]
    _ ≤ (δ * T)⁻¹ * (T * ε + a * ε) := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdT.le)
      exact add_le_add (mul_le_mul_of_nonneg_left hfull hT.le)
        (mul_le_mul_of_nonneg_left hprefix ha.le)
    _ ≤ (δ * T)⁻¹ * (2 * T * ε) := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdT.le)
      nlinarith
    _ = 2 * ε / δ := by field_simp

/-- One prefix-generic set controls every sufficiently late terminal
window, including a stopping time depending on both initial points. -/
theorem terminal_window_control_of_prefix_control
    {Y : Type*} (U : ℝ → Y → Y) (f : Y → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (G : Set Y) (c ε δ R : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R)
    (hgood : ∀ x ∈ G, ∀ T ≥ R,
      |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) - c| ≤ ε) :
    ∀ x ∈ G, ∀ T ≥ R / (1 - δ),
      |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, f (U t x)) - c| ≤ 2 * ε / δ := by
  intro x hx T hT
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  have hprefix : R ≤ (1 - δ) * T := by
    have he := (div_le_iff₀ hden).mp hT
    linarith
  have hTpos : 0 < T := by nlinarith
  have hTR : R ≤ T := by nlinarith
  exact terminal_window_average_error (fun t => f (U t x)) c ε δ T
    hδ hδ1 hTpos hε (hint x) (hgood x hx T hTR)
    (hgood x hx ((1 - δ) * T) hprefix)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RightObservableUniformity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform observables near a compact family of right translations

The tolerance is selected before the eventual shearing limit. Matrix
entry control then bounds a compact observable at every base point,
including points outside compact subsets of the lattice space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

section OppositeAction

attribute [local instance] OAI.DukePrimeDegree.rightLatticeOppositeAction
local instance rightLatticeOppositeAction_continuous (n : ℕ) :
    ContinuousSMul (G n)ᵐᵒᵖ (X n) where
  continuous_smul := (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk (MulOpposite.continuous_unop.comp continuous_fst))

lemma continuous_rightCompactObservable {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ) :
    Continuous (rightCompactObservable f) := by
  exact (continuous_compactObservableTranslate (H := (G n)ᵐᵒᵖ) f).comp MulOpposite.continuous_op

end OppositeAction

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockGenericSet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One generic set for all roots of the selected block

The shearing root and its limiting displacement are chosen after the
initial pair. Finiteness of the roots and compactness of the possible
displacements give a single good set and one terminal-time threshold
that work for every possible choice. Full real-root ergodicity comes
from the actual single-block component and the Mautner argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_singleBlock_terminal_generic_set_oai {n : ℕ}
    (S : Set (Fin n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup S) (X n) μ]
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K)
    (ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) :
    ∃ E : Set (X n), MeasurableSet E ∧ μ Eᶜ ≤ ENNReal.ofReal η ∧
      ∃ R : ℝ, 0 < R ∧
        ∀ x ∈ E, ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j), ∀ f ∈ F, ∀ T ≥ R,
          |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
            f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))) -
              ∫ y, f y ∂μ| ≤ ε ∧
          ∀ h ∈ K,
            |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
              f (rightAction (rightAction x
                (Matrix.SpecialLinearGroup.transvection hij (-t))) h)) -
                  ∫ y, f (rightAction y h) ∂μ| ≤ ε := by
  classical
  let A := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2}
  let D : Set (X n →ᵇ ℝ) := ⋃ f : F,
    insert f.val.toBoundedContinuousFunction (rightCompactObservable f.val '' K)
  have hD : IsCompact D := isCompact_iUnion fun f : F =>
    (hK.image (continuous_rightCompactObservable f.val)).insert _
  let η₀ := η / (Fintype.card A + 1)
  have hη₀ : 0 < η₀ := div_pos hη (by positivity)
  have hper (p : A) : ∃ E : Set (X n), MeasurableSet E ∧
      μ Eᶜ ≤ ENNReal.ofReal η₀ ∧ ∃ R : ℝ, 0 < R ∧
        ∀ x ∈ E, ∀ f ∈ D, ∀ T ≥ R,
          |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
            f (rightAction x (Matrix.SpecialLinearGroup.transvection p.property.2.2 (-t)))) -
              ∫ y, f y ∂μ| ≤ ε := by
    let := reverseRootTranslationAction p.property.2.2
    let : ContinuousSMul (Multiplicative ℝ) (X n) :=
      reverseRootTranslationAction_continuous p.property.2.2
    let : ErgodicSMul (Multiplicative ℝ) (X n) μ :=
      reverseRootTranslationAction_ergodic p.property.2.2 μ
        (root_ergodic_of_single_block_ergodic S p.property.2.2 p.property.1
          p.property.2.1 μ)
    obtain ⟨E, hE, hEμ, R, hR, hgood⟩ := exists_compact_family_real_flow_generic_set
      μ D hD (ε * δ / 2) η₀ (by positivity) hη₀
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    refine ⟨E, hE, hEμ, R / (1 - δ), div_pos hRpos (sub_pos.mpr hδ1), ?_⟩
    intro x hx f hf T hT
    have hc := terminal_window_control_of_prefix_control realActionTime f
      (fun y a b => ((continuous_flow_observable f).comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      E (∫ y, f y ∂μ) (ε * δ / 2) δ R (by positivity) hδ hδ1 hRpos
      (fun y hy t ht => hgood y hy f hf t ht) x hx T hT
    convert hc using 1
    · rfl
    · field_simp
  choose E hE hEμ R hR hgood using hper
  let N := Finset.univ.sup (fun p : A => ⌈R p⌉₊)
  let R₀ : ℝ := max 1 N
  have hRR (p : A) : R p ≤ R₀ := by
    have hp : ⌈R p⌉₊ ≤ N := Finset.le_sup (f := fun p => ⌈R p⌉₊) (Finset.mem_univ p)
    have hp' : (⌈R p⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp
    exact (Nat.le_ceil (R p)).trans (hp'.trans (le_max_right _ _))
  refine ⟨⋂ p, E p, MeasurableSet.iInter hE, ?_, R₀,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  · rw [compl_iInter]
    calc
      μ (⋃ p, (E p)ᶜ) ≤ ∑ p, μ (E p)ᶜ := measure_iUnion_fintype_le μ _
      _ ≤ ∑ _p : A, ENNReal.ofReal η₀ := Finset.sum_le_sum (fun p _ => hEμ p)
      _ = ENNReal.ofReal ((Fintype.card A : ℝ) * η₀) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hη₀.le)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal η := by
        apply ENNReal.ofReal_le_ofReal
        dsimp only [η₀]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card A + 1)]
        nlinarith
  · intro x hx i hi j hj hij f hf T hT
    let p : A := ⟨(i, j), hi, hj, hij⟩
    have hxE : x ∈ E p := mem_iInter.mp hx p
    have hTf : R p ≤ T := (hRR p).trans hT
    constructor
    · exact hgood p x hxE f.toBoundedContinuousFunction
        (mem_iUnion.mpr ⟨⟨f, hf⟩, Or.inl rfl⟩) T hTf
    · intro h hh
      exact hgood p x hxE (rightCompactObservable f h)
        (mem_iUnion.mpr ⟨⟨f, hf⟩, Or.inr ⟨h, hh, rfl⟩⟩) T hTf

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set_oai := @OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set_oai
