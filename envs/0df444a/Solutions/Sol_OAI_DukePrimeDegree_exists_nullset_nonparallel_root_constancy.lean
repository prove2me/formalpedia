-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_nullset_nonparallel_root_constancy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:55.155019+00:00
-- url     : https://prove2.me/submissions/554a586e-bbba-4f87-b4f2-ffe76285219d

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
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
import Definitions.Def_OAIQ244Duke044
import Theorems.Thm_OAI_DukePrimeDegree_exists_nullset_neutral_root_holonomy

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootWeights
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Neutral diagonal directions for root leaves

Root leaves are unchanged along the kernel of their root character.
For two nonparallel roots, an explicit diagonal direction is neutral on
the first and expands the second. These are the directions used to
compare the root foliations in the entropy argument.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology Classical

namespace DukePrimeDegree

open PrimeDegreePackets

lemma rootCanonicalWeights_neutral (d : ℕ) {i j p : Fin (d + 1)}
    (hip : i ≠ p) (hjp : j ≠ p) :
    rootCanonicalWeights d p i = rootCanonicalWeights d p j := by
  simp [rootCanonicalWeights, coordinateContractionWeights, hip, hjp]

/-- Every root which is not equal or opposite to a fixed root is expanded
by a diagonal direction which centralizes the fixed root. -/
theorem exists_neutral_expanding_weights (d : ℕ)
    {i j k l : Fin (d + 1)} (_hij : i ≠ j) (hkl : k ≠ l)
    (hforward : ¬ (k = i ∧ l = j)) (hbackward : ¬ (k = j ∧ l = i)) :
    ∃ ell : Fin (d + 1) → ℝ,
      (∑ r, ell r) = 0 ∧ ell i = ell j ∧ ell l - ell k = 1 := by
  by_cases hli : l = i
  · have hki : k ≠ i := by simpa only [hli] using hkl
    have hkj : k ≠ j := by
      intro h
      exact hbackward ⟨h, hli⟩
    refine ⟨fun r => -rootCanonicalWeights d k r, ?_, ?_, ?_⟩
    · simp only [Finset.sum_neg_distrib, rootCanonicalWeights_sum, neg_zero]
    · exact congrArg Neg.neg (rootCanonicalWeights_neutral d hki.symm hkj.symm)
    · have h := rootCanonicalWeights_difference d hkl.symm
      linarith
  · by_cases hlj : l = j
    · have hki : k ≠ i := by
        intro h
        exact hforward ⟨h, hlj⟩
      have hkj : k ≠ j := by simpa only [hlj] using hkl
      refine ⟨fun r => -rootCanonicalWeights d k r, ?_, ?_, ?_⟩
      · simp only [Finset.sum_neg_distrib, rootCanonicalWeights_sum, neg_zero]
      · exact congrArg Neg.neg (rootCanonicalWeights_neutral d hki.symm hkj.symm)
      · have h := rootCanonicalWeights_difference d hkl.symm
        linarith
    · exact ⟨rootCanonicalWeights d l, rootCanonicalWeights_sum d l,
        rootCanonicalWeights_neutral d (Ne.symm hli) (Ne.symm hlj),
        rootCanonicalWeights_difference d hkl⟩

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootStableHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root-leaf constancy along every stable root pair off a null set
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_conjugate_tendsto_one
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hneg : ell i - ell j < 0) (r : ℝ) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t *
      Matrix.SpecialLinearGroup.transvection hij r * diagonalOneParameter ell hell (-t))
      atTop (𝓝 1) := by
  have he (t : ℝ) : (ell i - ell j) * t = -((ell j - ell i) * t) := by ring
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Filter.Tendsto.const_mul_atTop (by linarith : 0 < ell j - ell i) tendsto_id)
  have hp : Tendsto (fun t : ℝ => Real.exp ((ell i - ell j) * t) * r) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, he, zero_mul] using ht.mul_const r
  have h := (continuous_rootTransvection hij).tendsto 0 |>.comp hp
  simpa only [Function.comp_def, diagonal_conjugation_transvection,
    Matrix.SpecialLinearGroup.transvection_coeff_zero] using h

lemma basedRealMeasure_zero_of_unit (ν : Measure ℝ) (hunit : ν (Metric.ball 0 1) = 1) :
    basedRealMeasure ν 0 = ν := by
  have he : (Homeomorph.subRight (0 : ℝ) : ℝ → ℝ) = id := by
    funext x
    simp
  rw [basedRealMeasure, centerRealMeasure, he, Measure.map_id]
  simp only [anchorNormalize, hunit, inv_one, one_smul]

theorem exists_nullset_nonparallel_root_constancy_oai
    (d : ℕ) {a b i j : Fin (d + 1)} (hab : a ≠ b) (hij : i ≠ j)
    (hf : ¬ (i = a ∧ j = b)) (hb : ¬ (i = b ∧ j = a))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ t : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N →
        intrinsicRootLeaf hab μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          intrinsicRootLeaf hab μ x := by
  obtain ⟨ell, hell, hn, hw⟩ := exists_neutral_expanding_weights d hab hij hf hb
  obtain ⟨N, hN, hNzero, hhol⟩ := exists_nullset_neutral_root_holonomy d hab μ hA ell hell hn
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hab t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx a b hab
  obtain ⟨E, hbad, hE, hEzero⟩ := exists_measurable_superset_of_null
    (ae_iff.mp ((ae_intrinsicRootLeaf_spec hab μ hfree).mono fun _ h => h.2))
  refine ⟨N ∪ E, hN.union hE, measure_union_null hNzero hEzero, ?_⟩
  intro x hx t hy
  have hunit : intrinsicRootLeaf hab μ x (Metric.ball 0 1) = 1 := by
    by_contra h
    exact hx (Or.inr (hbad h))
  have h := hhol x (fun h => hx (Or.inl h))
    (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) (fun h => hy (Or.inl h))
    (Matrix.SpecialLinearGroup.transvection hij t) rfl 0 (by
      simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using
        root_conjugate_tendsto_one hij ell hell (by linarith) t)
  rwa [basedRealMeasure_zero_of_unit _ hunit] at h

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_nullset_nonparallel_root_constancy_oai := @OAI.DukePrimeDegree.exists_nullset_nonparallel_root_constancy_oai
