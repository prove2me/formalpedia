-- Prove2me | solution 1 for OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:46:39.257206+00:00
-- url     : https://prove2.me/submissions/04552a62-841f-4556-989d-c4d0b6d187fc

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Pairing
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

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

lemma norm_sub_one_lt_of_matrixLogLength_lt {n : ℕ} (g : G n) {ε : ℝ} (hε : 0 < ε)
    (h : matrixLogLength g < Real.log (1+ε)) : ‖g.val-1‖ < ε := by
  have hi : 0 ≤ Real.log (1+‖(g⁻¹).val-1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)])
  have hlog : Real.log (1+‖g.val-1‖) < Real.log (1+ε) := by
    unfold matrixLogLength at h
    linarith
  by_contra hn
  have hle : 1+ε ≤ 1+‖g.val-1‖ := by linarith
  exact (not_lt_of_ge (Real.log_le_log (by linarith) hle)) hlog

theorem tendsto_one_of_matrixLogLength_tendsto_zero {α : Type*} {l : Filter α}
    {n : ℕ} (g : α → G n) (h : Tendsto (fun a => matrixLogLength (g a)) l (𝓝 0)) :
    Tendsto g l (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp : 0 < Real.log (1+ε) := Real.log_pos (by linarith)
  filter_upwards [h.eventually (gt_mem_nhds hp)] with a ha
  rw [dist_eq_norm]
  change ‖(g a).val-1‖ < ε
  exact norm_sub_one_lt_of_matrixLogLength_lt (g a) hε ha

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralOrbitCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Time-independent covers of compact neutral displacements

Compact sets of displacements commuting with the diagonal flow admit a
fixed finite orbit cover, valid for every time and every base point.
Thus their geometric covering cost does not grow with orbit length.
-/

noncomputable section
open Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem quotientLogDistance_commuting_displacements {n : ℕ}
    (x : X n) (g h a : G n) (hg : Commute g a) (hh : Commute h a) :
    quotientLogDistance (rightAction (rightAction x g) a)
      (rightAction (rightAction x h) a) ≤ matrixLogLength (g⁻¹*h) := by
  apply quotientLogDistance_le_length _ _ (g⁻¹*h)
  simp only [rightAction_mul]
  congr 1
  calc
    (g*a)*(g⁻¹*h) = (a*g)*(g⁻¹*h) := by rw [hg.eq]
    _ = a*h := by group
    _ = h*a := hh.eq.symm

end DukePrimeDegree

end

end OAI
end

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

lemma kernel_comp_real {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (τ : Measure Z) (κ : Kernel Z Y) [IsMarkovKernel κ]
    {S : Set Y} (hS : MeasurableSet S) :
    (κ ∘ₘ τ).real S = ∫ z, (κ z).real S ∂τ := by
  rw [measureReal_def, Measure.bind_apply hS κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hS).aemeasurable
    (ae_of_all _ fun z => measure_lt_top (κ z) S)).symm

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_ConditionalShannon
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma conditionalObservationEntropy_chain [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) (P : Y → α) (R : Y → β) (Q : Y → γ) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) Q =
      conditionalObservationEntropy μ P Q +
      conditionalObservationEntropy μ R (fun y => (Q y,P y)) := by
  unfold conditionalObservationEntropy
  rw [observationEntropy_assoc]
  ring

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

theorem conditionalObservationEntropy_pair_le
    [Fintype α] [Fintype β] [Fintype γ]
    (μ : Measure Y) [IsFiniteMeasure μ] (P : Y → α) (R : Y → β) (Q : Y → γ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hR : ∀ b, MeasurableSet {y | R y = b})
    (hQ : ∀ c, MeasurableSet {y | Q y = c}) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) Q ≤
      conditionalObservationEntropy μ P Q + conditionalObservationEntropy μ R Q := by
  rw [conditionalObservationEntropy_chain]
  exact add_le_add le_rfl (conditionalObservationEntropy_conditioning_le μ R Q P hR hQ hP)

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationRefinement
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem conditionalObservationEntropy_pair_pair_le
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (P : Y → α) (R : Y → β) (Q : Y → γ) (S : Y → δ)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hR : ∀ b, MeasurableSet {y | R y = b})
    (hQ : ∀ c, MeasurableSet {y | Q y = c})
    (hS : ∀ d, MeasurableSet {y | S y = d}) :
    conditionalObservationEntropy μ (fun y => (P y,R y)) (fun y => (Q y,S y)) ≤
      conditionalObservationEntropy μ P Q + conditionalObservationEntropy μ R S := by
  have hQS := observationPair_measurable_fiber Q S hQ hS
  refine (conditionalObservationEntropy_pair_le μ P R (fun y => (Q y,S y))
    hP hR hQS).trans ?_
  exact add_le_add
    (conditionalObservationEntropy_coarsening_le μ P (fun y => (Q y,S y)) Prod.fst hP hQS)
    (conditionalObservationEntropy_coarsening_le μ R (fun y => (Q y,S y)) Prod.snd hR hQS)

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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma conditionalOrbitEntropy_one [Fintype α] [Fintype β]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) (Q : Y → β) :
    conditionalObservationEntropy μ (orbitName T P 1) (orbitName T Q 1) =
      conditionalObservationEntropy μ P Q := by
  rw [orbitName_one, orbitName_one]
  exact conditionalObservationEntropy_injective μ P Q
    (fun a (_ : Fin 1) => a) (fun b (_ : Fin 1) => b)
    (fun _ _ h => congrFun h 0) (fun _ _ h => congrFun h 0)

theorem conditionalOrbitEntropy_le [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) (N : ℕ) :
    conditionalObservationEntropy μ (orbitName T P N) (orbitName T Q N) ≤
      (N : ℝ) * conditionalObservationEntropy μ P Q := by
  induction N with
  | zero =>
      let : Unique ((Fin 0 → β) × (Fin 0 → α)) :=
        uniqueOfSubsingleton (default, default)
      unfold conditionalObservationEntropy
      rw [observationEntropy_unique, observationEntropy_unique]
      simp
  | succ N ih =>
      have hPN := orbitName_measurable_fiber hT.measurable hP N
      have hQN := orbitName_measurable_fiber hT.measurable hQ N
      have hP1 := orbitName_measurable_fiber hT.measurable hP 1
      have hQ1 := orbitName_measurable_fiber hT.measurable hQ 1
      have heq :
          conditionalObservationEntropy μ (orbitName T P (N+1)) (orbitName T Q (N+1)) =
          conditionalObservationEntropy μ
            (fun y => (orbitName T P N y, orbitName T P 1 (T^[N] y)))
            (fun y => (orbitName T Q N y, orbitName T Q 1 (T^[N] y))) := by
        rw [orbitName_add T P N 1, orbitName_add T Q N 1]
        exact conditionalObservationEntropy_injective μ _ _
          (Fin.appendEquiv N 1) (Fin.appendEquiv N 1)
          (Fin.appendEquiv N 1).injective (Fin.appendEquiv N 1).injective
      rw [heq]
      have H := conditionalObservationEntropy_pair_pair_le μ
        (orbitName T P N) (fun y => orbitName T P 1 (T^[N] y))
        (orbitName T Q N) (fun y => orbitName T Q 1 (T^[N] y))
        hPN (fun a => (hP1 a).preimage (hT.measurable.iterate N))
        hQN (fun b => (hQ1 b).preimage (hT.measurable.iterate N))
      rw [conditionalObservationEntropy_comp_preserving μ _ _ hP1 hQ1 (hT.iterate N),
        conditionalOrbitEntropy_one] at H
      refine H.trans ?_
      have H' := add_le_add ih (le_refl (conditionalObservationEntropy μ P Q))
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using H'

/-- A finite observation approximates entropy rates up to its one-step
conditional entropy. This is the standard finite-partition approximation bound. -/
theorem observationEntropyRate_le_add_conditional [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hQ : ∀ b, MeasurableSet {y | Q y = b}) :
    observationEntropyRate μ T P ≤
      observationEntropyRate μ T Q + conditionalObservationEntropy μ P Q := by
  have H : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName T P N) / (N : ℝ) ≤
      observationEntropy μ (orbitName T Q N) / (N : ℝ) +
        conditionalObservationEntropy μ P Q := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have H₁ := observationEntropy_le_add_conditional μ
      (orbitName T P N) (orbitName T Q N)
      (orbitName_measurable_fiber hT.measurable hP N)
      (orbitName_measurable_fiber hT.measurable hQ N)
    have H₂ := conditionalOrbitEntropy_le μ hT P Q hP hQ N
    calc
      _ ≤ (observationEntropy μ (orbitName T Q N) +
          (N : ℝ) * conditionalObservationEntropy μ P Q) / (N : ℝ) :=
        div_le_div_of_nonneg_right (H₁.trans (add_le_add le_rfl H₂)) (Nat.cast_nonneg N)
      _ = _ := by rw [add_div]; congr 1; field_simp
  exact le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hP)
    ((tendsto_observationEntropyRate μ hT Q hQ).add tendsto_const_nhds) H

end PrimeDegreePackets

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RareLabelEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entropy cost of rare observation errors

This finite-label estimate converts small boundary-visit frequencies
into a small entropy cost for the neutral orbit covers.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rareLabelCost_small (q : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ε ∧
      ∀ p : ℝ, 0 ≤ p → p < ε → rareLabelCost q δ p < η := by
  let δ := 1-Real.exp (-η/2)
  have hd : 0 < δ := by
    have he : Real.exp (-η/2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [δ]
    linarith
  have hd1 : δ < 1 := by dsimp [δ] <;> linarith [Real.exp_pos (-η/2)]
  let L := Real.log q-Real.log δ
  let ε := η/(2*(1+|L|))
  have he : 0 < ε := div_pos hη (by positivity)
  refine ⟨δ,ε,hd,hd1,he,?_⟩
  intro p hp hpε
  have hbase : -Real.log (1-δ) = η/2 := by
    dsimp [δ]
    rw [sub_sub_cancel,Real.log_exp]
    ring
  have hprod : p*(1+|L|) < η/2 := by
    have h := (mul_lt_mul_iff_left₀ (show 0 < 1+|L| by positivity)).mpr hpε
    have hden : 1+|L| ≠ 0 := ne_of_gt (by positivity)
    have hε : ε*(1+|L|)=η/2 := by dsimp [ε]; field_simp [hden]
    nlinarith
  have hL : p*L ≤ p*|L| := mul_le_mul_of_nonneg_left (le_abs_self L) hp
  change -Real.log (1-δ)+p*L < η
  rw [hbase]
  linarith

theorem finiteShannon_option_le {α : Type*} [Fintype α] [Nonempty α]
    (p : Option α → ℝ) (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    finiteShannon p ≤ rareLabelCost (Fintype.card α) δ (1-p none) := by
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by
    change 0 < (Fintype.card α : ℝ)
    exact_mod_cast (Fintype.card_pos (α := α))
  let q : Option α → ℝ := fun a => match a with
    | none => 1-δ
    | some _ => δ/n
  have hq a : 0 < q a := by cases a <;> dsimp [q] <;> positivity
  have hqs : ∑ a, q a = 1 := by
    rw [Fintype.sum_option]
    simp only [q,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change 1-δ+n*(δ/n)=1
    field_simp [ne_of_gt hn]
    ring
  have H := finiteShannon_le_cross hp (fun a => (hq a).le) hs hqs
    (fun a ha => (ne_of_gt (hq a) ha).elim)
  have hsum : ∑ a : α, p (some a) = 1-p none := by
    rw [Fintype.sum_option] at hs
    linarith
  have hp1 : p none ≤ 1 := by
    have hnn : 0 ≤ ∑ a : α, p (some a) := Finset.sum_nonneg fun a _ => hp _
    linarith
  have hlog : Real.log (1-δ) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have he : (∑ a : Option α, -p a * Real.log (q a)) =
      -p none * Real.log (1-δ) + (1-p none)*(Real.log n-Real.log δ) := by
    rw [Fintype.sum_option]
    simp only [q,Real.log_div (ne_of_gt hδ) (ne_of_gt hn)]
    have hh : (∑ a : α, -p (some a)*(Real.log δ-Real.log n)) =
        (∑ a : α, p (some a))*(Real.log n-Real.log δ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hh,hsum]
  rw [he] at H
  unfold rareLabelCost
  dsimp only [n] at H
  nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (neg_nonneg.mpr hlog)]

theorem observationEntropy_option_le {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] (μ : Measure Y) [IsProbabilityMeasure μ]
    (E : Y → Option α) (hE : ∀ a, MeasurableSet {y | E y=a})
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    observationEntropy μ E ≤
      rareLabelCost (Fintype.card α) δ (1-μ.real {y | E y=none}) :=
  finiteShannon_option_le (fun a => μ.real {y | E y=a})
    (fun _ => measureReal_nonneg)
    (observation_distribution_sum μ E hE) hδ hδ1

theorem conditionalObservationEntropy_le_error {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P R : Y → α) (hP : Measurable P) (hR : Measurable R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalObservationEntropy μ P R ≤
      rareLabelCost (Fintype.card α) δ (μ.real {y | P y ≠ R y}) := by
  let E := observationError P R
  have hE (a : Option α) : MeasurableSet {y | E y=a} := by
    cases a with
    | none =>
      convert (measurableSet_eq_fun hP hR) using 1
      all_goals try with_reducible_and_instances rfl
      ext y
      simp [E,observationError]
    | some a =>
      convert (measurableSet_eq_fun hP hR).compl.inter
        (hP (measurableSet_singleton a)) using 1
      all_goals try with_reducible_and_instances rfl
      ext y
      by_cases h : P y=R y <;> simp [E,observationError,h]
  have href : ∀ x y, (R x,E x) = (R y,E y) → (R x,P x) = (R y,P y) := by
    intro x y h
    have hr : R x=R y := congrArg Prod.fst h
    have he : E x=E y := congrArg Prod.snd h
    apply Prod.ext hr
    by_cases hx : P x = R x
    · have hy : P y = R y := by
        by_contra hy
        simp [E,observationError,hx,hy] at he
      exact hx.trans (hr.trans hy.symm)
    · by_cases hy : P y = R y
      · simp [E,observationError,hx,hy] at he
      · simpa only [E,observationError,ite_eq_right hx,ite_eq_right hy,Option.some.injEq] using he
  have H := observationEntropy_le_of_refines μ (fun y => (R y,P y))
    (fun y => (R y,E y))
    (observationPair_measurable_fiber R P
      (fun a => hR (measurableSet_singleton a)) (fun a => hP (measurableSet_singleton a)))
    (observationPair_measurable_fiber R E
      (fun a => hR (measurableSet_singleton a)) hE) href
  have H' := observationEntropy_joint_le μ R E
    (fun a => hR (measurableSet_singleton a))
    hE
  have herr := observationEntropy_option_le μ E hE hδ hδ1
  have heq : 1-μ.real {y | E y=none} = μ.real {y | P y ≠ R y} := by
    have hs : {y | E y=none} = {y | P y=R y} := by
      ext y
      simp [E,observationError]
    rw [hs,show {y | P y ≠ R y} = {y | P y=R y}ᶜ from rfl,
      measureReal_compl (measurableSet_eq_fun hP hR),probReal_univ]
  rw [heq] at herr
  unfold conditionalObservationEntropy
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NameErrorEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy of finite names controlled by their coordinate errors -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalVectorEntropy_le_sum {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (N : ℕ)
    (P R : Y → Fin N → α) (hP : Measurable P) (hR : Measurable R) :
    conditionalObservationEntropy μ P R ≤
      ∑ i : Fin N, conditionalObservationEntropy μ (fun y => P y i) (fun y => R y i) := by
  induction N with
  | zero =>
    let : Unique ((Fin 0 → α) × (Fin 0 → α)) :=
      uniqueOfSubsingleton (default,default)
    simp only [conditionalObservationEntropy,observationEntropy_unique,sub_self,
      Fin.sum_univ_zero,le_refl]
  | succ N ih =>
    let e := (Fin.consEquiv (fun _ : Fin (N+1) => α)).symm
    let P₀ := fun y => P y 0
    let R₀ := fun y => R y 0
    let Pt := fun y (i : Fin N) => P y i.succ
    let Rt := fun y (i : Fin N) => R y i.succ
    have hp0 : Measurable P₀ := (measurable_pi_apply 0).comp hP
    have hr0 : Measurable R₀ := (measurable_pi_apply 0).comp hR
    have hpt : Measurable Pt := measurable_pi_iff.mpr fun i =>
      (measurable_pi_apply i.succ).comp hP
    have hrt : Measurable Rt := measurable_pi_iff.mpr fun i =>
      (measurable_pi_apply i.succ).comp hR
    have he : conditionalObservationEntropy μ (fun y => (P₀ y,Pt y))
        (fun y => (R₀ y,Rt y)) = conditionalObservationEntropy μ P R :=
      conditionalObservationEntropy_injective μ P R e e e.injective e.injective
    rw [←he]
    have H := conditionalObservationEntropy_pair_pair_le μ P₀ Pt R₀ Rt
      (fun a => hp0 (measurableSet_singleton a))
      (fun a => hpt (measurableSet_singleton a))
      (fun a => hr0 (measurableSet_singleton a))
      (fun a => hrt (measurableSet_singleton a))
    refine H.trans ?_
    have HH := ih Pt Rt hpt hrt
    rw [Fin.sum_univ_succ]
    exact add_le_add le_rfl HH

theorem conditionalNameEntropy_le_errors {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (N : ℕ)
    (P R : Y → Fin N → α) (hP : Measurable P) (hR : Measurable R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalObservationEntropy μ P R ≤
      (N : ℝ)*(-Real.log (1-δ)) +
        (∑ i : Fin N, μ.real {y | P y i ≠ R y i}) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  refine (conditionalVectorEntropy_le_sum μ N P R hP hR).trans ?_
  have H := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin N) _ =>
    conditionalObservationEntropy_le_error μ (fun y => P y i) (fun y => R y i)
      ((measurable_pi_apply i).comp hP) ((measurable_pi_apply i).comp hR) hδ hδ1)
  refine H.trans_eq ?_
  simp only [rareLabelCost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Finset.sum_mul]

end DukePrimeDegree

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalNameCovers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating finite-name covers over conditional probability kernels

Reference names may depend on the conditioning parameter. Errors need
only lie in the bad sets almost surely for the corresponding conditional
measure. Their integrated cost is measured by the actual kernel mixture.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem nameEntropy_le_reference_bad_sets
    {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (ν : Measure Y) [IsProbabilityMeasure ν] (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : Y → Fin M) (hr : Measurable r) (v : Fin M → Fin N → α)
    (B : Fin N → Set Y)
    (hbad : ∀ i, ∀ᵐ y ∂ν, P y i ≠ v (r y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    observationEntropy ν P ≤ Real.log M+(N : ℝ)*(-Real.log (1-δ))+
      (∑ i : Fin N, ν.real (B i))*(Real.log (Fintype.card α)-Real.log δ) := by
  let R := v ∘ r
  have hR : Measurable R := (measurable_of_finite v).comp hr
  have href : observationEntropy ν R ≤ observationEntropy ν r :=
    observationEntropy_le_of_refines ν R r
      (fun a => hR (measurableSet_singleton a))
      (fun a => hr (measurableSet_singleton a))
      (fun x y h => congrArg v h)
  have hcard : observationEntropy ν r ≤ Real.log M := by
    simpa only [observationEntropy,Fintype.card_fin] using
      (finiteShannon_le_log_card (fun _ => measureReal_nonneg)
        (observation_distribution_sum ν r (fun a => hr (measurableSet_singleton a))))
  have hjoint := observationEntropy_le_add_conditional ν P R
    (fun a => hP (measurableSet_singleton a))
    (fun a => hR (measurableSet_singleton a))
  have hc := conditionalNameEntropy_le_errors ν N P R hP hR hδ hδ1
  have hsum : (∑ i : Fin N, ν.real {y | P y i ≠ R y i}) ≤
      ∑ i : Fin N, ν.real (B i) := by
    apply Finset.sum_le_sum
    intro i _
    exact ENNReal.toReal_mono (measure_ne_top ν (B i)) (measure_mono_ae (hbad i))
  have hslope : 0 ≤ Real.log (Fintype.card α)-Real.log δ := by
    have hn : 1 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith [Real.log_nonneg hn,Real.log_neg hδ hδ1]
  have hm := mul_le_mul_of_nonneg_right hsum hslope
  linarith

/-- The conditional error estimate integrates against the actual law of
the conditioning parameter. No joint measurability of the chosen reference
labels is needed; only the conditional entropy and bad-set probabilities
are integrated. -/
theorem integral_nameEntropy_le_reference_bad_sets
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (τ : Measure S) [IsProbabilityMeasure τ]
    (κ : Kernel S Y) [IsMarkovKernel κ] (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : S → Y → Fin M) (hr : ∀ s, Measurable (r s))
    (v : S → Fin M → Fin N → α) (B : Fin N → Set Y)
    (hB : ∀ i, MeasurableSet (B i))
    (hbad : ∀ᵐ s ∂τ, ∀ i, ∀ᵐ y ∂κ s, P y i ≠ v s (r s y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (∫ s, observationEntropy (κ s) P ∂τ) ≤
      Real.log M+(N : ℝ)*(-Real.log (1-δ))+
        (∑ i : Fin N, (κ ∘ₘ τ).real (B i)) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  let C := Real.log M+(N : ℝ)*(-Real.log (1-δ))
  let L := Real.log (Fintype.card α)-Real.log δ
  have hp : Integrable (fun s => observationEntropy (κ s) P) τ :=
    integrable_kernel_entropy τ κ P (fun a => hP (measurableSet_singleton a))
  have hb (i : Fin N) : Integrable (fun s => (κ s).real (B i)) τ :=
    integrable_kernel_real τ κ (hB i)
  have hs : Integrable (fun s => ∑ i : Fin N, (κ s).real (B i)) τ :=
    integrable_finsetSum _ (fun i _ => hb i)
  have hbound : Integrable (fun s => C+(∑ i : Fin N, (κ s).real (B i))*L) τ :=
    (integrable_const C).add (hs.mul_const L)
  have H := integral_mono_ae hp hbound (hbad.mono fun s hs =>
    nameEntropy_le_reference_bad_sets (κ s) N M P hP (r s) (hr s) (v s) B hs hδ hδ1)
  have he : (∫ s, C+(∑ i : Fin N, (κ s).real (B i))*L ∂τ) =
      C+(∑ i : Fin N, (κ ∘ₘ τ).real (B i))*L := by
    rw [integral_add (integrable_const C) (hs.mul_const L),integral_mul_const,
      integral_finsetSum _ (fun i _ => hb i)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    exact (kernel_comp_real τ κ (hB i)).symm
  exact H.trans_eq he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralNameCovers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable selection of neutral orbit approximations

A finite cover by neutral displacements admits a measurable choice of
reference displacement. The same finite list works for every orbit length.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local instance] OAI.DukePrimeDegree.instMeasurableSpaceG
local instance instBorelSpaceG (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem measurable_choice_fin_cover {Y : Type*} [MeasurableSpace Y]
    {N : ℕ} (S : Fin N → Set Y) (hS : ∀ i, MeasurableSet (S i))
    (hcover : ∀ y, ∃ i, y ∈ S i) :
    ∃ r : Y → Fin N, Measurable r ∧ ∀ y, y ∈ S (r y) := by
  classical
  let p (y : Y) (k : ℕ) := ∃ hk : k < N, y ∈ S ⟨k,hk⟩
  have hp (y : Y) : ∃ k, p y k := by
    obtain ⟨i,hi⟩ := hcover y
    exact ⟨i.val,i.isLt,hi⟩
  have hm : Measurable (fun y => Nat.find (hp y)) := by
    apply measurable_find hp
    intro k
    by_cases hk : k < N
    · have he : {y | p y k} = S ⟨k,hk⟩ := by
        ext y
        simp [p,hk]
      rw [he]
      exact hS ⟨k,hk⟩
    · have he : {y | p y k} = ∅ := by ext y; simp [p,hk]
      rw [he]
      exact MeasurableSet.empty
  let r (y : Y) : Fin N := ⟨Nat.find (hp y),(Nat.find_spec (hp y)).choose⟩
  refine ⟨r,?_,fun y => (Nat.find_spec (hp y)).choose_spec⟩
  apply measurable_to_countable'
  intro i
  have he : r ⁻¹' {i} = (fun y => Nat.find (hp y)) ⁻¹' {i.val} := by
    ext y
    exact Fin.ext_iff
  rw [he]
  exact hm (measurableSet_singleton _)

/-- A compact collection of neutral displacements can be encoded by one
measurable finite label, uniformly for all real times. -/
theorem compact_neutral_measurable_selector {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (K : Set (G n)) (hK : IsCompact K)
    (hcomm : ∀ g ∈ K, ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (g : Fin N → G n) (r : K → Fin N),
      (∀ i, g i ∈ K) ∧ Measurable r ∧
      ∀ (k : K) (x : X n) (t : ℝ),
        quotientLogDistance
          (rightAction (rightAction x k.val) (diagonalOneParameter ell hell t))
          (rightAction (rightAction x (g (r k))) (diagonalOneParameter ell hell t)) < ε := by
  classical
  let U (h : K) : Set (G n) := {g | matrixLogLength (g⁻¹*h.val) < ε}
  have hU (h : K) : IsOpen (U h) :=
    isOpen_lt ((continuous_matrixLogLength n).comp (continuous_inv.mul continuous_const))
      continuous_const
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (fun g hg =>
    mem_iUnion.mpr ⟨⟨g,hg⟩,by simpa only [U,mem_ofPred_eq,inv_mul_cancel,
      matrixLogLength_one] using hε⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let g (i : Fin (Fintype.card s)) : G n := (e i).val.val
  let S (i : Fin (Fintype.card s)) : Set K := {k | matrixLogLength (k.val⁻¹*g i) < ε}
  have hm (i : Fin (Fintype.card s)) : MeasurableSet (S i) := by
    exact (isOpen_lt ((continuous_matrixLogLength n).comp
      (continuous_subtype_val.inv.mul continuous_const)) continuous_const).measurableSet
  have hc (k : K) : ∃ i, k ∈ S i := by
    obtain ⟨h,hh,hkh⟩ := mem_iUnion₂.mp (hs k.prop)
    refine ⟨e.symm ⟨h,hh⟩,?_⟩
    simpa only [S,g,U,mem_ofPred_eq,Equiv.apply_symm_apply] using hkh
  obtain ⟨r,hr,hsel⟩ := measurable_choice_fin_cover S hm hc
  refine ⟨Fintype.card s,g,r,fun i => (e i).val.prop,hr,?_⟩
  intro k x t
  exact (quotientLogDistance_commuting_displacements x k.val (g (r k))
    (diagonalOneParameter ell hell t) (hcomm k.val k.prop t)
    (hcomm (g (r k)) (e (r k)).val.prop t)).trans_lt (hsel k)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

theorem quotientLogDistance_eq_zero_iff {n : ℕ} (x y : X n) :
    quotientLogDistance x y=0 ↔ x=y := by
  constructor
  · intro hzero
    choose g hg hlen using fun k : ℕ => exists_rightAction_length_lt x y
      (show 0 < (1:ℝ)/((k:ℝ)+1) by positivity)
    have hlength : Tendsto (fun k => matrixLogLength (g k)) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => matrixLogLength_nonneg _)
        (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [hzero,zero_add] using (hlen k).le
    have hgroup := tendsto_one_of_matrixLogLength_tendsto_zero g hlength
    have horbit := (continuous_rightOrbit n x).continuousAt.tendsto.comp hgroup
    have hconst : Tendsto (fun _ : ℕ => y) atTop (𝓝 x) := by
      simpa only [Function.comp_def,hg,rightAction_one] using horbit
    exact (tendsto_nhds_unique tendsto_const_nhds hconst).symm
  · rintro rfl
    exact quotientLogDistance_self x

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LeafLusin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact sets with continuous root-leaf data

The Lusin step in EKL (2006), Section 4.3, is applied to a countable
family of compactly supported tests determining locally finite real
measures. A finer Polish topology and inner regularity provide a compact
set in the original topology, outside any specified null set.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology Classical ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuousOn_of_finer_compact {Y Z : Type*}
    {t t' : TopologicalSpace Y} {tZ : TopologicalSpace Z} [@T2Space Y t]
    (hle : t' ≤ t) {K : Set Y} (hK : @IsCompact Y t' K)
    {f : Y → Z} (hf : @Continuous Y Z t' tZ f) :
    @ContinuousOn Y Z t tZ f K := by
  let : TopologicalSpace Y := t
  apply continuousOn_iff_isClosed.mpr
  intro C hC
  have hc : @IsCompact Y t' (f ⁻¹' C ∩ K) := by
    let : TopologicalSpace Y := t'
    exact hK.inter_left (hC.preimage hf)
  have hid : @Continuous Y Y t' t id := continuous_id_of_le hle
  have hcold : @IsCompact Y t (f ⁻¹' C ∩ K) := by
    simpa only [image_id] using @IsCompact.image Y Y t' t _ id hc hid
  exact ⟨f ⁻¹' C ∩ K, hcold.isClosed, by simp only [inter_assoc, inter_self]⟩

/-- A compact Lusin set avoiding a prescribed measurable null set. -/
theorem exists_compact_continuousOn_outside_null
    {Y Z : Type*} [tY : TopologicalSpace Y] [PolishSpace Y]
    [mY : MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → Z) (hf : Measurable f)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  have hB : mY = @borel Y tY := BorelSpace.measurable_eq
  obtain ⟨t', hle, hf', hp⟩ := hf.exists_continuous
  have hBt : mY = @borel Y t' :=
    hB.trans (borel_eq_borel_of_le hp (inferInstance : @PolishSpace Y tY) hle).symm
  let : TopologicalSpace Y := t'
  let : PolishSpace Y := hp
  let : BorelSpace Y := ⟨hBt⟩
  obtain ⟨K, hKN, hK, hsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
    (measure_ne_top μ Nᶜ) hε
  have hsmall' : μ Kᶜ < ε := by
    have heq : Nᶜ \ K = Kᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hsmall
  refine ⟨K, ?_, hKN, hsmall', continuousOn_of_finer_compact hle hK hf'⟩
  simpa only [image_id] using @IsCompact.image Y Y t' tY K id hK (continuous_id_of_le hle)

/-- The compact-set version only needs a metrizable source and inner
regularity; the source need not be equipped with a complete metric. -/
theorem exists_compact_continuousOn_metrizable
    {Y Z : Type*} [TopologicalSpace Y] [MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Y) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]
    (f : Y → Z) (hf : Measurable f)
    (N : Set Y) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Nᶜ ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Fin 2)
  have hsum : δ 0 + δ 1 < ε := by simpa only [tsum_fintype, Fin.sum_univ_two] using hδsum
  obtain ⟨C, hCN, hC, hCsmall⟩ := hN.compl.exists_isCompact_sdiff_lt
    (measure_ne_top μ Nᶜ) (hδ 0).ne'
  have hCsmall' : μ Cᶜ < δ 0 := by
    have heq : Nᶜ \ C = Cᶜ \ N := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, and_comm]
    rwa [heq, measure_sdiff_null hNzero] at hCsmall
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : MetricSpace C := TopologicalSpace.metrizableSpaceMetric C
  let : PolishSpace C := inferInstance
  let ν : Measure C := μ.comap Subtype.val
  have he : MeasurableEmbedding (Subtype.val : C → Y) :=
    (hC.isClosed.isClosedEmbedding_subtypeVal).measurableEmbedding
  let : IsFiniteMeasure ν := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [he.comap_apply]
    exact measure_lt_top μ _⟩
  obtain ⟨L, hL, _, hLsmall, hLcont⟩ := exists_compact_continuousOn_outside_null
    ν (f ∘ Subtype.val) (hf.comp measurable_subtype_coe) ∅ MeasurableSet.empty
    (by simp) (δ 1) (hδ 1).ne'
  let K : Set Y := Subtype.val '' L
  have hK : IsCompact K := hL.image continuous_subtype_val
  have hKsmall : μ (C \ K) < δ 1 := by
    have heq : Subtype.val '' Lᶜ = C \ K := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, fun ⟨z, hz, hez⟩ => hy (Subtype.ext hez ▸ hz)⟩
      · rintro ⟨hxC, hxK⟩
        exact ⟨⟨x, hxC⟩, fun h => hxK ⟨⟨x, hxC⟩, h, rfl⟩, rfl⟩
    change μ.comap Subtype.val Lᶜ < δ 1 at hLsmall
    rw [he.comap_apply, heq] at hLsmall
    exact hLsmall
  refine ⟨K, hK, ?_, ?_, ?_⟩
  · rintro x ⟨y, _, rfl⟩
    exact hCN y.property
  · have hsub : Kᶜ ⊆ Cᶜ ∪ (C \ K) := by intro x hx; by_cases h : x ∈ C <;> tauto
    exact (((measure_mono hsub).trans (measure_union_le _ _)).trans
      (add_le_add hCsmall'.le hKsmall.le)).trans_lt hsum
  · exact Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_image_iff.mpr hLcont

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactNeutralFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite covers of neutral itinerary fibers

The small displacement bound puts every bilateral fiber in one fixed
compact subset of the diagonal centralizer. Thus the number of reference
orbits needed for a given accuracy is independent of the base point and
the length of the observed orbit.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

local instance instMeasurableSpaceG_1_re52295_1 (n : ℕ) : MeasurableSpace (G n) := borel (G n)
local instance instBorelSpaceG_1_re52295_1 (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
theorem isCompact_compactNeutralDisplacements {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    IsCompact (compactNeutralDisplacements ell hell) := by
  have hbox : IsCompact {M : Matrix (Fin n) (Fin n) ℝ |
      ∀ i j, |M i j| ≤ 2} := by
    have h : IsCompact ((Icc (-2 : ℝ) 2).matrix : Set (Matrix (Fin n) (Fin n) ℝ)) :=
      isCompact_Icc.matrix
    simpa only [Set.matrix,mem_Icc,abs_le] using h
  have hbound : IsCompact {g : G n | ∀ i j, |g.val i j| ≤ 2} :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hbox
  have hcomm : IsClosed {g : G n | ∀ t : ℝ,
      Commute g (diagonalOneParameter ell hell t)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro t
    exact isClosed_eq (continuous_id.mul continuous_const)
      (continuous_const.mul continuous_id)
  exact hbound.inter_right hcomm

theorem mem_compactNeutralDisplacements_of_small {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (g : G n)
    (hg : g ∈ matrixBall n 1)
    (hc : ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) :
    g ∈ compactNeutralDisplacements ell hell := by
  refine ⟨?_,hc⟩
  intro i j
  have h := hg i j
  have he : |(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have ht := abs_add_le (g.val i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j)
    ((1 : Matrix (Fin n) (Fin n) ℝ) i j)
  rw [sub_add_cancel] at ht
  linarith

/-- A bilateral fiber with a small neutral lift admits a fixed finite
list of reference orbits; its geometric coding cost does not grow in time. -/
theorem finite_neutral_itinerary_cover {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ)
    (hQ : ∀ x y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → G n), ∀ x y,
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) →
      (∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) →
      ∃ i, ∀ t : ℝ,
        quotientLogDistance (rightAction y (diagonalOneParameter ell hell t))
          (rightAction (rightAction x (v i)) (diagonalOneParameter ell hell t)) < ε := by
  let K := compactNeutralDisplacements ell hell
  obtain ⟨N,v,r,_,_,hcov⟩ := compact_neutral_measurable_selector ell hell K
    (isCompact_compactNeutralDisplacements ell hell) (fun g hg => hg.2) hε
  refine ⟨N,v,?_⟩
  intro x y hf hb
  obtain ⟨g,hg,hgx,hgc⟩ := hQ x y hf hb
  let k : K := ⟨g,mem_compactNeutralDisplacements_of_small ell hell g hg hgc⟩
  refine ⟨r k,?_⟩
  intro t
  simpa only [k,hgx] using hcov k x t

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralFiberNames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable reference names on bilateral itinerary fibers -/

noncomputable section
open MeasureTheory Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem measurable_choice_fin_on {Y : Type*} [MeasurableSpace Y]
    {M : ℕ} (i₀ : Fin M) (S : Fin M → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (E : Set Y) (hE : MeasurableSet E)
    (hcover : ∀ y ∈ E, ∃ i, y ∈ S i) :
    ∃ r : Y → Fin M, Measurable r ∧ ∀ y ∈ E, y ∈ S (r y) := by
  obtain ⟨r,hr,h⟩ := measurable_choice_fin_cover (fun i => S i ∪ Eᶜ)
    (fun i => (hS i).union hE.compl) (fun y => by
      by_cases hy : y ∈ E
      · obtain ⟨i,hi⟩ := hcover y hy
        exact ⟨i,Or.inl hi⟩
      · exact ⟨i₀,Or.inr hy⟩)
  refine ⟨r,hr,?_⟩
  intro y hy
  rcases h y with hi | hi
  · exact hi
  · exact (hi hy).elim

theorem measurableSet_bilateralNameFiber {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (x : X n) :
    MeasurableSet (bilateralNameFiber ell hell Q x) := by
  have hT (t : ℝ) : Measurable (fun z : X n =>
      rightAction z (diagonalOneParameter ell hell t)) :=
    (continuous_rightAction _).measurable
  simp only [bilateralNameFiber,Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun k : ℕ =>
    measurableSet_eq_fun (hQ.comp ((hT (-1)).iterate k)) measurable_const).inter
      (MeasurableSet.iInter fun k : ℕ =>
        measurableSet_eq_fun (hQ.comp ((hT 1).iterate k)) measurable_const)

/-- Every finite time segment has a measurable reference label on the
fiber, using a list whose size is independent of the time segment. -/
theorem measurable_neutral_fiber_names {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (v : Fin M → G n), ∀ (N : ℕ) (x : X n),
      ∃ r : X n → Fin M, Measurable r ∧
        ∀ y ∈ bilateralNameFiber ell hell Q x, ∀ j : Fin N,
          quotientLogDistance
            (rightAction (rightAction x (v (r y)))
              (diagonalOneParameter ell hell (-(j.val:ℝ))))
            (rightAction y (diagonalOneParameter ell hell (-(j.val:ℝ)))) < ε := by
  obtain ⟨M,v,hcover⟩ := finite_neutral_itinerary_cover ell hell Q
    (fun x y hf hb => hlift x y ⟨hf,hb⟩) hε
  let x₀ : X n := Quotient.mk _ (1 : G n)
  obtain ⟨i₀,_⟩ := hcover x₀ x₀ (fun _ => rfl) (fun _ => rfl)
  refine ⟨M,v,?_⟩
  intro N x
  let S (i : Fin M) : Set (X n) := {y | ∀ j : Fin N,
    quotientLogDistance
      (rightAction (rightAction x (v i)) (diagonalOneParameter ell hell (-(j.val:ℝ))))
      (rightAction y (diagonalOneParameter ell hell (-(j.val:ℝ)))) < ε}
  have hS (i : Fin M) : MeasurableSet (S i) := by
    simp only [S,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (isOpen_lt ((continuous_quotientLogDistance n _).comp
      (continuous_rightAction _)) continuous_const).measurableSet
  obtain ⟨r,hr,hs⟩ := measurable_choice_fin_on i₀ S hS
    (bilateralNameFiber ell hell Q x) (measurableSet_bilateralNameFiber ell hell Q hQ x)
    (fun y hy => by
      obtain ⟨i,hi⟩ := hcover x y hy.1 hy.2
      refine ⟨i,fun j => ?_⟩
      rw [quotientLogDistance_symm]
      exact hi (-(j.val:ℝ)))
  exact ⟨r,hr,hs⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralConditionalSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem measurable_bilateralNameObservation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q) :
    Measurable (bilateralNameObservation ell hell Q) := by
  have hT (t : ℝ) : Measurable (fun z : X n =>
      rightAction z (diagonalOneParameter ell hell t)) :=
    (continuous_rightAction _).measurable
  exact (measurable_pi_iff.mpr fun k => hQ.comp ((hT (-1)).iterate k)).prodMk
    (measurable_pi_iff.mpr fun k => hQ.comp ((hT 1).iterate k))

theorem bilateralNameObservation_eq_iff {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (x y : X n) :
    bilateralNameObservation ell hell Q y = bilateralNameObservation ell hell Q x ↔
      y ∈ bilateralNameFiber ell hell Q x := by
  simp only [bilateralNameObservation,Prod.mk.injEq,funext_iff,bilateralNameFiber,
    mem_ofPred_eq]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FiniteBlockEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy comparison at finite block scales -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem observationEntropyRate_le_of_refines
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hQ : ∀ a, MeasurableSet {y | Q y=a})
    (href : ∀ x y, Q x=Q y → P x=P y) :
    observationEntropyRate μ T P ≤ observationEntropyRate μ T Q := by
  apply le_of_tendsto_of_tendsto (tendsto_observationEntropyRate μ hT P hP)
    (tendsto_observationEntropyRate μ hT Q hQ)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply observationEntropy_le_of_refines μ _ _
    (orbitName_measurable_fiber hT.measurable hP N)
    (orbitName_measurable_fiber hT.measurable hQ N)
  intro x y hxy
  funext i
  exact href _ _ (congrFun hxy i)

theorem observationEntropyRate_comp_commuting {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y) (hS : MeasurePreserving S μ μ)
    (hcomm : Function.Commute S T) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) (hT : Measurable T) :
    observationEntropyRate μ T (P ∘ S)=observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  congr 1
  have he : orbitName T (P ∘ S) N = (orbitName T P N) ∘ S := by
    funext y i
    exact congrArg P (hcomm.iterate_right i.val y)
  rw [he]
  exact observationEntropy_comp_preserving μ (orbitName T P N)
    (orbitName_measurable_fiber hT hP N) hS

private lemma orbitName_blocks {Y α : Type*}
    (T : Y → Y) (P : Y → α) (N q : ℕ) :
    orbitName T P (N*q) = fun y =>
      blockWordEquiv α N q (orbitName (T^[q]) (orbitName T P q) N y) := by
  funext y
  apply (blockWordEquiv α N q).symm.injective
  rw [Equiv.symm_apply_apply]
  funext i j
  change P (T^[j.val+q*i.val] y)=P (T^[j.val] ((T^[q])^[i.val] y))
  rw [Function.iterate_add_apply,Function.iterate_mul]

theorem observationEntropyRate_blocks {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) {q : ℕ} (hq : 0 < q) :
    observationEntropyRate μ (T^[q]) (orbitName T P q) =
      (q : ℝ)*observationEntropyRate μ T P := by
  have hsub : Tendsto (fun N : ℕ => N*q) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    exact hN.trans (Nat.le_mul_of_pos_right _ hq)
  have H := (tendsto_observationEntropyRate μ hT P hP).comp hsub
  have hscaled : Tendsto (fun N : ℕ => (q : ℝ)*
      (observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))) atTop
      (𝓝 ((q : ℝ)*observationEntropyRate μ T P)) := tendsto_const_nhds.mul H
  have heq : (fun N : ℕ => (q : ℝ)*
      (observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))) =
      (fun N : ℕ => observationEntropy μ
        (orbitName (T^[q]) (orbitName T P q) N)/N) := by
    funext N
    rw [orbitName_blocks,observationEntropy_equiv]
    by_cases hN : N=0
    · subst N
      simp
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    push_cast
    field_simp [hNr,hqr]
  rw [heq] at hscaled
  exact tendsto_nhds_unique
    (tendsto_observationEntropyRate μ (hT.iterate q) (orbitName T P q)
      (orbitName_measurable_fiber hT.measurable hP q)) hscaled

/-- Observing a fixed finite window at every q-th step has at most q
times the entropy rate of the underlying observation. -/
theorem observationEntropyRate_sampled_window_le {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) {q : ℕ} (hq : 0 < q) (W : ℕ) :
    observationEntropyRate μ (T^[q]) (orbitName T P W) ≤
      (q : ℝ)*observationEntropyRate μ T P := by
  have hb (N : ℕ) : observationEntropy μ
      (orbitName (T^[q]) (orbitName T P W) N) ≤
      observationEntropy μ (orbitName T P (N*q))+
        observationEntropy μ (orbitName T P W) := by
    apply le_trans (b := observationEntropy μ (orbitName T P (N*q+W)))
    · apply observationEntropy_le_of_refines μ _ _
        (orbitName_measurable_fiber (hT.measurable.iterate q)
          (orbitName_measurable_fiber hT.measurable hP W) N)
        (orbitName_measurable_fiber hT.measurable hP (N*q+W))
      intro x y hxy
      funext i j
      have hindex : j.val+q*i.val < N*q+W := by
        have hi := i.isLt
        have hj := j.isLt
        nlinarith
      have h := congrFun hxy ⟨j.val+q*i.val,hindex⟩
      simpa only [orbitName,Function.iterate_add_apply,Function.iterate_mul] using h
    · exact orbitEntropy_subadditive μ hT P hP (N*q) W
  have hbound : ∀ᶠ N : ℕ in atTop,
      observationEntropy μ (orbitName (T^[q]) (orbitName T P W) N)/(N : ℝ) ≤
      (q : ℝ)*(observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))+
        observationEntropy μ (orbitName T P W)/(N : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
    have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have H := div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg N)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    field_simp [hn,hqr]
  have hsub : Tendsto (fun N : ℕ => N*q) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    exact hN.trans (Nat.le_mul_of_pos_right _ hq)
  have hmain : Tendsto (fun N : ℕ => (q : ℝ)*
      (observationEntropy μ (orbitName T P (N*q))/(N*q : ℕ))) atTop
      (𝓝 ((q : ℝ)*observationEntropyRate μ T P)) :=
    tendsto_const_nhds.mul ((tendsto_observationEntropyRate μ hT P hP).comp hsub)
  have herr : Tendsto
      (fun N : ℕ => observationEntropy μ (orbitName T P W)/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := hmain.add herr
  simp only [add_zero] at hlim
  exact le_of_tendsto_of_tendsto
    (tendsto_observationEntropyRate μ (hT.iterate q) (orbitName T P W)
      (orbitName_measurable_fiber hT.measurable hP W)) hlim hbound

/-- Sampling a finite observation every q steps costs at most q times
its original entropy rate. -/
theorem observationEntropyRate_iterate_le {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) {q : ℕ} (hq : 0 < q) :
    observationEntropyRate μ (T^[q]) P ≤ (q : ℝ)*observationEntropyRate μ T P := by
  have h := observationEntropyRate_le_of_refines μ (hT.iterate q) P (orbitName T P 1)
    hP (orbitName_measurable_fiber hT.measurable hP 1)
    (fun x y hxy => by
      have he := congrFun hxy (0 : Fin 1)
      simpa only [orbitName,Fin.val_zero,Function.iterate_zero_apply] using he)
  exact h.trans (observationEntropyRate_sampled_window_le μ hT P hP hq 1)

theorem observationEntropyRate_le_block_conditional
    {Y α β : Type*} [MeasurableSpace Y] [Fintype α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (Q : Y → β)
    (hP : ∀ a, MeasurableSet {y | P y=a})
    (hQ : ∀ a, MeasurableSet {y | Q y=a}) {q : ℕ} (hq : 0 < q) :
    observationEntropyRate μ T P ≤ observationEntropyRate μ T Q+
      conditionalObservationEntropy μ (orbitName T P q) Q/(q : ℝ) := by
  have H := observationEntropyRate_le_add_conditional μ (hT.iterate q)
    (orbitName T P q) Q (orbitName_measurable_fiber hT.measurable hP q) hQ
  rw [observationEntropyRate_blocks μ hT P hP hq] at H
  have H' := observationEntropyRate_iterate_le μ hT Q hQ hq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  apply (mul_le_mul_iff_right₀ hqr).mp
  rw [mul_add,mul_div_cancel₀ _ hqr.ne']
  nlinarith [H.trans (add_le_add H' le_rfl)]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalMapEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

theorem conditionalSigmaEntropy_comap_le_reference_bad_sets
    {S Y α : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F) (N M : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : S → Y → Fin M) (hr : ∀ s, Measurable (r s))
    (v : S → Fin M → Fin N → α) (B : Fin N → Set Y)
    (hB : ∀ i, MeasurableSet (B i))
    (hbad : ∀ᵐ s ∂μ.map F, ∀ i, ∀ᵐ y ∂condDistrib id F μ s,
      P y i ≠ v s (r s y) i → y ∈ B i)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) ≤
      Real.log M+(N : ℝ)*(-Real.log (1-δ))+
        (∑ i : Fin N, μ.real (B i)) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  rw [conditionalSigmaEntropy_comap_eq_integral μ F hF P
    (fun a => hP (measurableSet_singleton a))]
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  have H := integral_nameEntropy_le_reference_bad_sets (μ.map F) (condDistrib id F μ)
    N M P hP r hr v B hB hbad hδ hδ1
  have hm : condDistrib id F μ ∘ₘ (μ.map F)=μ := by
    simpa only [Measure.map_id] using condDistrib_comp_map hF.aemeasurable aemeasurable_id
  simpa only [hm] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RobustFiniteObservations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite measurable observations away from a small exceptional set -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem continuous_quotientLogDistance_pair (n : ℕ) :
    Continuous (fun p : X n × X n => quotientLogDistance p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := by positivity
  have hx : ∀ᶠ z : X n × X n in 𝓝 p, quotientLogDistance p.1 z.1 < ε/2 := by
    exact (((continuous_quotientLogDistance n p.1).comp continuous_fst).tendsto p).eventually
      (p := fun a : ℝ => a < ε/2)
      (gt_mem_nhds (by simpa only [Function.comp_apply,quotientLogDistance_self] using hhalf))
  have hy : ∀ᶠ z : X n × X n in 𝓝 p, quotientLogDistance p.2 z.2 < ε/2 := by
    exact (((continuous_quotientLogDistance n p.2).comp continuous_snd).tendsto p).eventually
      (p := fun a : ℝ => a < ε/2)
      (gt_mem_nhds (by simpa only [Function.comp_apply,quotientLogDistance_self] using hhalf))
  filter_upwards [hx,hy] with z hx hy
  have h₁ := quotientLogDistance_triangle z.1 p.1 z.2
  have h₂ := quotientLogDistance_triangle p.1 p.2 z.2
  have h₃ := quotientLogDistance_triangle p.1 z.1 p.2
  have h₄ := quotientLogDistance_triangle z.1 z.2 p.2
  rw [quotientLogDistance_symm z.1 p.1] at h₁
  rw [quotientLogDistance_symm z.2 p.2] at h₄
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem compact_finite_observation_separation {n M : ℕ}
    (K : Set (X n)) (hK : IsCompact K) (P : X n → Fin M)
    (hP : ContinuousOn P K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K,
      quotientLogDistance x y < δ → P x=P y := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (K × K) := {p | P p.1.val ≠ P p.2.val}
  have hp : Continuous (fun x : K => P x.val) := continuousOn_iff_continuous_domRestrict.mp hP
  have hS : IsClosed S :=
    (isClosed_discrete {q : Fin M × Fin M | q.1 ≠ q.2}).preimage
      ((hp.comp continuous_fst).prodMk (hp.comp continuous_snd))
  have hf : Continuous (fun p : K × K => quotientLogDistance p.1.val p.2.val) :=
    (continuous_quotientLogDistance_pair n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  obtain ⟨δ,hδ,hlower⟩ := hS.isCompact.exists_forall_le' hf.continuousOn
    (a := (0 : ℝ)) (fun p hp => by
      apply lt_of_le_of_ne (quotientLogDistance_nonneg _ _)
      intro h
      exact hp (congrArg P ((quotientLogDistance_eq_zero_iff _ _).mp h.symm)))
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy
  by_contra hne
  exact (not_lt_of_ge (hlower (⟨x,hx⟩,⟨y,hy⟩) hne)) hxy

/-- A reference point can be assigned a robust label even when the
reference point itself lies outside the good compact set. -/
theorem compact_finite_reference_labels {n M : ℕ}
    (K : Set (X n)) (hK : IsCompact K) (P : X n → Fin M)
    (hP : ContinuousOn P K) :
    ∃ (δ : ℝ) (R : X n → Fin M), 0 < δ ∧
      ∀ z y, y ∈ K → quotientLogDistance z y < δ → P y=R z := by
  classical
  obtain ⟨ε,hε,hsep⟩ := compact_finite_observation_separation K hK P hP
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  let E (z : X n) := ∃ y ∈ K, quotientLogDistance z y < δ
  let y₀ : X n := Quotient.mk _ (1 : G n)
  let R (z : X n) : Fin M := if h : E z then P h.choose else P y₀
  refine ⟨δ,R,hδ,?_⟩
  intro z y hy hzy
  have he : E z := ⟨y,hy,hzy⟩
  have hc := he.choose_spec
  have hnear : quotientLogDistance y he.choose < ε := by
    have ht := quotientLogDistance_triangle y z he.choose
    rw [quotientLogDistance_symm y z] at ht
    dsimp [δ] at hzy hc
    linarith [hc.2]
  simpa only [R,dite_eq_left he] using hsep y hy he.choose hc.1 hnear

theorem exists_robust_finite_observation {n M : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (P : X n → Fin M) (hP : Measurable P)
    (η : ℝ≥0∞) (hη : η ≠ 0) :
    ∃ (B : Set (X n)) (δ : ℝ) (R : X n → Fin M),
      MeasurableSet B ∧ μ B < η ∧ 0 < δ ∧
        ∀ z y, y ∉ B → quotientLogDistance z y < δ → P y=R z := by
  obtain ⟨K,hK,_,hsmall,hcont⟩ := exists_compact_continuousOn_metrizable
    μ P hP ∅ MeasurableSet.empty (by simp) η hη
  obtain ⟨δ,R,hδ,hr⟩ := compact_finite_reference_labels K hK P hcont
  exact ⟨Kᶜ,δ,R,hK.isClosed.measurableSet.compl,hsmall,hδ,
    fun z y hy hzy => hr z y (not_not.mp hy) hzy⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NeutralRelativeEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative entropy of finite names over the bilateral itinerary factor -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_negative_iterate {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (j : ℕ) (x : X n) :
    (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[j] x =
      rightAction x (diagonalOneParameter ell hell (-(j:ℝ))) := by
  rw [rightAction_iterate,diagonalOneParameter_neg,inv_pow,
    ←diagonalOneParameter_nat,←diagonalOneParameter_neg]

theorem bilateral_name_entropy_le_robust_error {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P)
    (B : Set (X n)) (hB : MeasurableSet B) (R : X n → Fin k)
    {r : ℝ} (hr : 0 < r)
    (hrobust : ∀ z y, y ∉ B → quotientLogDistance z y < r → P y=R z)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, ∀ N : ℕ,
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance) ≤
        Real.log M+(N : ℝ)*rareLabelCost k δ (μ.real B) := by
  classical
  let x₀ : X n := Quotient.mk _ (1 : G n)
  let : Nonempty (Fin k) := ⟨P x₀⟩
  let F := bilateralNameObservation ell hell Q
  have hF : Measurable F := measurable_bilateralNameObservation ell hell Q hQ
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  obtain ⟨M,v,hcover⟩ := measurable_neutral_fiber_names ell hell Q hQ hlift hr
  choose c hc hclose using hcover
  let x (s : (ℕ → ℕ) × (ℕ → ℕ)) : X n :=
    if h : ∃ y, F y=s then h.choose else x₀
  have hsupport := ae_condDistrib_self_fiber μ F hF
  have hx : ∀ᵐ s ∂μ.map F, F (x s)=s := by
    filter_upwards [hsupport] with s hs
    have he : ∃ y, F y=s := hs.exists
    simpa only [x,dite_eq_left he] using he.choose_spec
  refine ⟨M,?_⟩
  intro N
  let refs (s : (ℕ → ℕ) × (ℕ → ℕ)) (i : Fin M) (j : Fin N) :=
    R (rightAction (rightAction (x s) (v i))
      (diagonalOneParameter ell hell (-(j.val:ℝ))))
  let bad (j : Fin N) := (T^[j.val]) ⁻¹' B
  have hbad (j : Fin N) : MeasurableSet (bad j) :=
    hB.preimage (hT.measurable.iterate j.val)
  have he : ∀ᵐ s ∂μ.map F, ∀ j : Fin N,
      ∀ᵐ y ∂condDistrib id F μ s,
        orbitName T P N y j ≠ refs s (c N (x s) y) j → y ∈ bad j := by
    filter_upwards [hsupport,hx] with s hs hxs
    intro j
    filter_upwards [hs] with y hy
    intro hne
    have hmem : y ∈ bilateralNameFiber ell hell Q (x s) :=
      (bilateralNameObservation_eq_iff ell hell Q (x s) y).mp (hy.trans hxs.symm)
    have hdist := hclose N (x s) y hmem j
    by_contra hnot
    apply hne
    exact hrobust _ _ hnot (by
      simpa only [T,diagonal_negative_iterate] using hdist)
  have H := conditionalSigmaEntropy_comap_le_reference_bad_sets μ F hF N M
    (orbitName T P N) (measurable_pi_iff.mpr fun j =>
      hP.comp (hT.measurable.iterate j.val))
    (fun s => c N (x s)) (fun s => hc N (x s)) refs bad hbad he hδ hδ1
  have hm (j : Fin N) : μ.real (bad j)=μ.real B :=
    (hT.iterate j.val).measureReal_preimage hB.nullMeasurableSet
  simpa only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    rareLabelCost,mul_add,mul_assoc,add_assoc] using H

/-- Conditioning on the actual bilateral itinerary leaves a sublinear
amount of information in every finite measurable observation. -/
theorem bilateral_name_entropy_sublinear {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N : ℕ,
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance) ≤
        Real.log M+(N : ℝ)*ε := by
  obtain ⟨δ,η,hδ,hδ1,hη,hcost⟩ := rareLabelCost_small k hε
  obtain ⟨B,r,R,hB,hsmall,hr,hrobust⟩ := exists_robust_finite_observation μ P hP
    (ENNReal.ofReal η) (by simp only [ne_eq,ENNReal.ofReal_eq_zero] <;> linarith)
  have hsmall' : μ.real B < η := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [Measure.real,ENNReal.toReal_ofReal hη.le] using h
  obtain ⟨M,hM⟩ := bilateral_name_entropy_le_robust_error ell hell Q hQ hlift
    μ hT P hP B hB R hr hrobust hδ hδ1
  refine ⟨M,fun N => (hM N).trans ?_⟩
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (hcost (μ.real B) measureReal_nonneg hsmall').le (Nat.cast_nonneg N))

theorem bilateral_name_relative_entropy_tendsto_zero {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P) :
    Tendsto (fun N : ℕ =>
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance) / N)
      atTop (𝓝 0) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let F := bilateralNameObservation ell hell Q
  let E (N : ℕ) := conditionalSigmaEntropy μ (orbitName T P N)
    (MeasurableSpace.comap F inferInstance)
  have hE (N : ℕ) : 0 ≤ E N := conditionalSigmaEntropy_comap_nonneg μ F
    (measurable_bilateralNameObservation ell hell Q hQ) (orbitName T P N)
    (orbitName_measurable_fiber hT.measurable
      (fun a => hP (measurableSet_singleton a)) N)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := bilateral_name_entropy_sublinear ell hell Q hQ hlift
    μ hT P hP (show 0 < ε/2 by positivity)
  have hlim : Tendsto (fun N : ℕ => Real.log M/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (show 0 < ε/2 by positivity)),
    eventually_ge_atTop (1 : ℕ)] with N hlog hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb : E N/(N : ℝ) ≤ Real.log M/(N : ℝ)+ε/2 := by
    apply (div_le_iff₀ hn).mpr
    have he : (Real.log M/(N : ℝ)+ε/2)*N = Real.log M+N*(ε/2) := by
      field_simp
    rw [he]
    exact hM N
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hE N) hn.le)]
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_BilateralFiniteCodes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite codes exhausting the actual bilateral itinerary factor -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem bilateralFiniteCode_measurable {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (m : ℕ) :
    Measurable (bilateralFiniteCode ell hell Q m) := by
  have hT (t : ℝ) : Measurable (fun z : X n =>
      rightAction z (diagonalOneParameter ell hell t)) :=
    (continuous_rightAction _).measurable
  exact (measurable_pi_iff.mpr fun i : Fin m =>
    (heightClip_measurable hQ m).comp ((hT (-1)).iterate i.val)).prodMk
      (measurable_pi_iff.mpr fun i : Fin m =>
        (heightClip_measurable hQ m).comp ((hT 1).iterate i.val))

theorem truncate_bilateralFiniteCode {n m l : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (hml : m ≤ l) (x : X n) :
    truncateBilateralCode hml (bilateralFiniteCode ell hell Q l x) =
      bilateralFiniteCode ell hell Q m x := by
  apply Prod.ext <;> funext i <;> apply Fin.ext <;>
    simp only [truncateBilateralCode,bilateralFiniteCode,heightClip] <;> omega

theorem bilateralFiniteCode_sigma_monotone {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ) :
    Monotone (fun m => observationSigma (bilateralFiniteCode ell hell Q m)) := by
  intro m l hml
  have he : bilateralFiniteCode ell hell Q m =
      truncateBilateralCode hml ∘ bilateralFiniteCode ell hell Q l :=
    funext fun x => (truncate_bilateralFiniteCode ell hell Q hml x).symm
  change observationSigma (bilateralFiniteCode ell hell Q m) ≤
    observationSigma (bilateralFiniteCode ell hell Q l)
  rw [he]
  simpa only [Function.comp_def] using
    observationSigma_comp_le (bilateralFiniteCode ell hell Q l) (truncateBilateralCode hml)

theorem bilateralFiniteCode_sigma_generate {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ) :
    (⨆ m, observationSigma (bilateralFiniteCode ell hell Q m)) =
      MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance := by
  let F := bilateralNameObservation ell hell Q
  apply le_antisymm
  · let : MeasurableSpace (X n) := MeasurableSpace.comap F inferInstance
    have hF : Measurable F := comap_measurable F
    apply iSup_le
    intro m
    have hl (i : Fin m) : Measurable (fun x => (F x).1 i.val) :=
      (measurable_pi_apply i.val).comp (measurable_fst.comp hF)
    have hr (i : Fin m) : Measurable (fun x => (F x).2 i.val) :=
      (measurable_pi_apply i.val).comp (measurable_snd.comp hF)
    have hC : Measurable (bilateralFiniteCode ell hell Q m) :=
      (measurable_pi_iff.mpr fun i => heightClip_measurable (hl i) m).prodMk
        (measurable_pi_iff.mpr fun i => heightClip_measurable (hr i) m)
    exact observationSigma_le _ (fun a => hC (measurableSet_singleton a))
  · let : MeasurableSpace (X n) :=
      ⨆ m, observationSigma (bilateralFiniteCode ell hell Q m)
    have hC (m : ℕ) : Measurable (bilateralFiniteCode ell hell Q m) := by
      apply measurable_to_countable'
      intro a
      exact (le_iSup (fun l => observationSigma (bilateralFiniteCode ell hell Q l)) m)
        _ ⟨{a},trivial,rfl⟩
    have hl (k : ℕ) : Measurable (fun x => (F x).1 k) := by
      apply measurable_to_countable'
      intro a
      let m := max (k+1) (a+1)
      have hk : k < m := by dsimp [m]; omega
      have ha : a < m := by dsimp [m]; omega
      let g (x : X n) := ((bilateralFiniteCode ell hell Q m x).1 ⟨k,hk⟩).val
      have hg : Measurable g := (measurable_of_finite (fun v : Fin (m+1) => v.val)).comp
        ((measurable_pi_apply (⟨k,hk⟩ : Fin m)).comp (measurable_fst.comp (hC m)))
      have he : {x | (F x).1 k=a}={x | g x=a} := by
        ext x
        change Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)=a ↔
          min (Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) m=a
        omega
      change MeasurableSet {x | (F x).1 k=a}
      rw [he]
      exact measurableSet_eq_fun hg measurable_const
    have hr (k : ℕ) : Measurable (fun x => (F x).2 k) := by
      apply measurable_to_countable'
      intro a
      let m := max (k+1) (a+1)
      have hk : k < m := by dsimp [m]; omega
      have ha : a < m := by dsimp [m]; omega
      let g (x : X n) := ((bilateralFiniteCode ell hell Q m x).2 ⟨k,hk⟩).val
      have hg : Measurable g := (measurable_of_finite (fun v : Fin (m+1) => v.val)).comp
        ((measurable_pi_apply (⟨k,hk⟩ : Fin m)).comp (measurable_snd.comp (hC m)))
      have he : {x | (F x).2 k=a}={x | g x=a} := by
        ext x
        change Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)=a ↔
          min (Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) m=a
        omega
      change MeasurableSet {x | (F x).2 k=a}
      rw [he]
      exact measurableSet_eq_fun hg measurable_const
    exact ((measurable_pi_iff.mpr hl).prodMk (measurable_pi_iff.mpr hr)).comap_le

theorem conditional_bilateralFiniteCode_tendsto {n : ℕ} {α : Type*} [Fintype α]
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (P : X n → α) (hP : ∀ a, MeasurableSet {x | P x=a}) :
    Tendsto (fun m => conditionalObservationEntropy μ P (bilateralFiniteCode ell hell Q m))
      atTop (𝓝 (conditionalSigmaEntropy μ P
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance))) := by
  have H := conditionalObservationEntropy_tendsto_sigma μ P hP
    (bilateralFiniteCode ell hell Q)
    (fun m a => bilateralFiniteCode_measurable ell hell Q hQ m (measurableSet_singleton a))
    (bilateralFiniteCode_sigma_monotone ell hell Q)
  rwa [bilateralFiniteCode_sigma_generate] at H

private theorem diagonal_positive_iterate {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (j : ℕ) (x : X n) :
    (fun z => rightAction z (diagonalOneParameter ell hell 1))^[j] x =
      rightAction x (diagonalOneParameter ell hell (j:ℝ)) := by
  rw [rightAction_iterate,←diagonalOneParameter_nat]

private theorem shifted_window_symbol {n m W : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (x : X n) (j : Fin W) :
    orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1)))
      (heightClip Q m) W (rightAction x (diagonalOneParameter ell hell (m:ℝ))) j =
      heightClip Q m (rightAction x
        (diagonalOneParameter ell hell ((m:ℝ)-(j.val:ℝ)))) := by
  change heightClip Q m
    ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[j.val]
      (rightAction x (diagonalOneParameter ell hell (m:ℝ)))) = _
  rw [diagonal_negative_iterate,rightAction_mul,←diagonalOneParameter_add]
  rfl

/-- A bilateral finite code is a factor of a shifted finite orbit window,
so it has no more entropy than the clipped countable observation. -/
theorem bilateralFiniteCode_entropyRate_le (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (m : ℕ) :
    observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))
      (bilateralFiniteCode ell hell Q m) ≤
    observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let S := fun z => rightAction z (diagonalOneParameter ell hell (m:ℝ))
  have hp (t : ℝ) : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell t)) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hcomm : Function.Commute S T := by
    intro x
    dsimp [S,T]
    rw [rightAction_mul,rightAction_mul,←diagonalOneParameter_add,
      ←diagonalOneParameter_add,
      show (-1:ℝ)+(m:ℝ)=(m:ℝ)+(-1) from add_comm _ _]
  let R := orbitName T (heightClip Q m) (2*m+1)
  have hR : Measurable R := measurable_pi_iff.mpr fun i =>
    (heightClip_measurable hQ m).comp ((hp (-1)).measurable.iterate i.val)
  have hfactor : ∀ x y, (R ∘ S) x=(R ∘ S) y →
      bilateralFiniteCode ell hell Q m x=bilateralFiniteCode ell hell Q m y := by
    intro x y hxy
    have hf (z : X (d+1)) (i : Fin m) :
        (R ∘ S) z ⟨m+i.val,by omega⟩ =
          (bilateralFiniteCode ell hell Q m z).1 i := by
      rw [show (R ∘ S) z ⟨m+i.val,by omega⟩ =
        orbitName T (heightClip Q m) (2*m+1) (S z) ⟨m+i.val,by omega⟩ from rfl]
      rw [shifted_window_symbol]
      change heightClip Q m (rightAction z
        (diagonalOneParameter ell hell ((m:ℝ)-((m+i.val:ℕ):ℝ)))) =
        heightClip Q m (T^[i.val] z)
      rw [diagonal_negative_iterate]
      congr 3
      push_cast
      ring
    have hb (z : X (d+1)) (i : Fin m) :
        (R ∘ S) z ⟨m-i.val,by omega⟩ =
          (bilateralFiniteCode ell hell Q m z).2 i := by
      change orbitName T (heightClip Q m) (2*m+1) (S z) ⟨m-i.val,by omega⟩ = _
      rw [shifted_window_symbol]
      change heightClip Q m (rightAction z
        (diagonalOneParameter ell hell ((m:ℝ)-((m-i.val:ℕ):ℝ)))) =
        heightClip Q m ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[i.val] z)
      rw [diagonal_positive_iterate]
      congr 3
      rw [Nat.cast_sub (by omega : i.val ≤ m)]
      ring
    apply Prod.ext <;> funext i
    · exact (hf x i).symm.trans ((congrFun hxy ⟨m+i.val,by omega⟩).trans (hf y i))
    · exact (hb x i).symm.trans ((congrFun hxy ⟨m-i.val,by omega⟩).trans (hb y i))
  have H := observationEntropyRate_le_of_refines μ (hp (-1))
    (bilateralFiniteCode ell hell Q m) (R ∘ S)
    (fun a => bilateralFiniteCode_measurable ell hell Q hQ m (measurableSet_singleton a))
    (fun a => (hR.comp (hp m).measurable) (measurableSet_singleton a)) hfactor
  rw [observationEntropyRate_comp_commuting μ T S (hp m) hcomm R
    (fun a => hR (measurableSet_singleton a)) (hp (-1)).measurable] at H
  refine H.trans ?_
  simpa only [Function.iterate_one,Nat.cast_one,one_mul] using
    observationEntropyRate_sampled_window_le μ (hp (-1)) (heightClip Q m)
      (fun a => heightClip_measurable hQ m (measurableSet_singleton a))
      (q := 1) (by omega) (2*m+1)

/-- The small neutral fibers make a uniform entropy bound on all finite
clips of Q an entropy bound for every finite measurable observation. -/
theorem entropyRate_le_of_bilateral_heightClip_bounds (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (B : ℝ)
    (hbound : ∀ m, observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) ≤ B)
    {k : ℕ} (P : X (d+1) → Fin k) (hP : Measurable P) :
    observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P ≤ B := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let F := bilateralNameObservation ell hell Q
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hblock (N : ℕ) (hN : 0 < N) :
      observationEntropyRate μ T P ≤ B+
        conditionalSigmaEntropy μ (orbitName T P N)
          (MeasurableSpace.comap F inferInstance)/(N : ℝ) := by
    have hm (m : ℕ) : observationEntropyRate μ T P ≤ B+
        conditionalObservationEntropy μ (orbitName T P N)
          (bilateralFiniteCode ell hell Q m)/(N : ℝ) := by
      have H := observationEntropyRate_le_block_conditional μ hT P
        (bilateralFiniteCode ell hell Q m)
        (fun a => hP (measurableSet_singleton a))
        (fun a => bilateralFiniteCode_measurable ell hell Q hQ m
          (measurableSet_singleton a)) hN
      exact H.trans (add_le_add
        ((bilateralFiniteCode_entropyRate_le d ell hell Q hQ μ hA m).trans (hbound m)) le_rfl)
    have hlim := ((conditional_bilateralFiniteCode_tendsto ell hell Q hQ μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable
        (fun a => hP (measurableSet_singleton a)) N)).div_const (N : ℝ)).const_add B
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hm)
  have hlim := (bilateral_name_relative_entropy_tendsto_zero ell hell Q hQ hlift
    μ hT P hP).const_add B
  have h := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact hblock N (by omega))
  simpa only [add_zero] using h

theorem measureEntropy_le_of_bilateral_heightClip_bounds_oai (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (B : ℝ)
    (hbound : ∀ m, observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) ≤ B) :
    measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal B := by
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  exact ENNReal.ofReal_le_ofReal (entropyRate_le_of_bilateral_heightClip_bounds
    d ell hell Q hQ μ hA hlift B hbound P (by apply measurable_to_countable'; exact hP))

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds_oai := @OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds_oai
