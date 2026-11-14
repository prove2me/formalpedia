-- Prove2me | solution 1 for OAI.DukePrimeDegree.isHaar_of_prime_symmetric_invariant_roots
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:51:00.032832+00:00
-- url     : https://prove2.me/submissions/43b797f5-eb7f-4f84-97df-55b435e49642

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
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
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
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_ae_normalized_component_velocity_support
import Theorems.Thm_OAI_DukePrimeDegree_exists_positive_singleBlock_orbit

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockDiagonalAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The algebra of scalars on root blocks

For a partition of the coordinate indices, the block-scalar algebra is
the actual diagonal matrix algebra whose diagonal is constant on each
block. Its dimension is the number of blocks. It is also the common
centralizer of the full diagonal algebra and the elementary root
matrices within the blocks. These are algebraic statements, without
any homogeneous-measure classification assumption.
-/

noncomputable section
open Matrix
open scoped Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_blockScalarAlgebra_iff (r : Setoid ι) (M : Matrix ι ι ℝ) :
    M ∈ blockScalarAlgebra r ↔
      M = Matrix.diagonal (fun i => M i i) ∧ ∀ i j, r i j → M i i = M j j := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨?_, ?_⟩
    · change Matrix.diagonal (fun i => c (Quotient.mk r i)) =
        Matrix.diagonal (fun i => Matrix.diagonal (fun k => c (Quotient.mk r k)) i i)
      simp only [Matrix.diagonal_apply_eq]
    · intro i j hij
      change Matrix.diagonal (fun k => c (Quotient.mk r k)) i i =
        Matrix.diagonal (fun k => c (Quotient.mk r k)) j j
      simpa only [Matrix.diagonal_apply_eq] using congrArg c (Quotient.sound hij)
  · rintro ⟨hd, hr⟩
    let c : Quotient r → ℝ := Quotient.lift (fun i => M i i) (fun i j hij => hr i j hij)
    refine ⟨c, ?_⟩
    change Matrix.diagonal (fun i => M i i) = M
    exact hd.symm

/-- A diagonal matrix commutes with an elementary root exactly when
its two corresponding diagonal entries coincide. -/
theorem diagonal_commute_transvection_iff (c : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    Commute (Matrix.diagonal c) (Matrix.transvection i j 1) ↔ c i = c j := by
  constructor
  · intro h
    have he := congrArg (fun A : Matrix ι ι ℝ => A i j) h.eq
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection,
      Matrix.one_apply, Matrix.single_apply, hij] using he
  · intro hc
    change Matrix.diagonal c * Matrix.transvection i j 1 =
      Matrix.transvection i j 1 * Matrix.diagonal c
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst b
      rw [mul_comm]
    · by_cases hai : a = i
      · subst a
        by_cases hbj : b = j
        · subst b
          rw [hc, mul_comm]
        · simp [Matrix.transvection, hab, Ne.symm hbj]
      · simp [Matrix.transvection, hab, Ne.symm hai]

/-- A matrix commuting with every block scalar has no entries between
different coordinate blocks. -/
theorem commute_blockScalars_iff (r : Setoid ι) (M : Matrix ι ι ℝ) :
    (∀ A ∈ blockScalarAlgebra r, Commute M A) ↔
      ∀ i j, ¬ r i j → M i j = 0 := by
  constructor
  · intro h i j hij
    let c : Quotient r → ℝ := fun q => if q = Quotient.mk r i then 1 else 0
    have hq : Quotient.mk r j ≠ Quotient.mk r i := by
      intro he
      exact hij (r.symm (Quotient.exact he))
    have he := congrArg (fun A : Matrix ι ι ℝ => A i j)
      (h (blockScalarAlgHom r c) ⟨c, rfl⟩).eq
    change (M * Matrix.diagonal (fun k => c (Quotient.mk r k))) i j =
      (Matrix.diagonal (fun k => c (Quotient.mk r k)) * M) i j at he
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, c, hq] using he.symm
  · intro h A hA
    obtain ⟨c, rfl⟩ := hA
    change M * blockScalarAlgHom r c = blockScalarAlgHom r c * M
    ext i j
    change (M * Matrix.diagonal (fun k => c (Quotient.mk r k))) i j =
      (Matrix.diagonal (fun k => c (Quotient.mk r k)) * M) i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : r i j
    · rw [Quotient.sound hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PrimeBlockRationality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.rowBasis_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational diagonal stabilizers of actual lattices

The rational coordinate space below is constructed from an actual lattice
matrix. Its diagonal stabilizer is a concrete subalgebra of real coordinate
functions, not a separately assumed field action. The absence of lattice
vectors on coordinate hyperplanes makes this algebra a field of degree
dividing the ambient dimension.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rationalRowMap_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℚ) :
    rationalRowMap g z = Matrix.vecMul (fun i => (z i : ℝ)) g := by
  ext i
  simp [rationalRowMap, Matrix.vecMul, dotProduct, Finset.sum_apply, Rat.smul_def]

lemma rationalRowMap_injective {n : ℕ} (g : G n) :
    Function.Injective (rationalRowMap g.val) := by
  intro z w h
  simp only [rationalRowMap_apply] at h
  have hu : IsUnit g.val := (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.property]; simp)
  have H := Matrix.vecMul_injective_of_isUnit hu h
  exact funext (fun i => Rat.cast_injective (congrFun H i))

lemma finrank_rationalRowSpace {n : ℕ} (g : G n) :
    Module.finrank ℚ (rationalRowSpace g) = n := by
  let e := LinearEquiv.ofInjective (rationalRowMap g.val) (rationalRowMap_injective g)
  change Module.finrank ℚ (LinearMap.range (rationalRowMap g.val)) = n
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma row_mem_rationalRowSpace {n : ℕ} (g : G n) (i : Fin n) :
    g.val i ∈ rationalRowSpace g := by
  refine ⟨Pi.single i 1, ?_⟩
  change (∑ x : Fin n, ((Pi.single i (1 : ℚ) : Fin n → ℚ) x) • g.val x) = g.val i
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul]
  simpa only [Finset.mem_univ, ite_true, if_true] using Finset.sum_ite_eq' Finset.univ i g.val

/-- The rational row space is small over `ℚ`, but spans the whole real
coordinate space. This retains the actual invertible lattice matrix. -/
theorem real_span_rationalRowSpace {n : ℕ} (g : G n) :
    Submodule.span ℝ (rationalRowSpace g : Set (Fin n → ℝ)) = ⊤ := by
  have hrows : LinearIndependent ℝ g.val :=
    Matrix.linearIndependent_rows_of_det_ne_zero (by rw [g.property]; exact one_ne_zero)
  have hspan := hrows.span_eq_top_of_card_eq_finrank'
    (by simp : Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ))
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact row_mem_rationalRowSpace g i

/-- The generic-lattice condition also excludes coordinate zeroes in
the rational span; localization introduces no new linear relations. -/
theorem rationalRowSpace_no_coordinate_zero {n : ℕ} (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ j, v j ≠ 0) :
    ∀ v ∈ rationalRowSpace g, ∀ j, v j = 0 → v = 0 := by
  intro v hv j hvj
  obtain ⟨z, rfl⟩ := hv
  have hliZ : LinearIndependent ℤ (fun i : Fin n => g.val i j) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have he : integerRowMap g.val a = 0 := by
      by_contra hne
      have hm : integerRowMap g.val a ∈ rowLattice g.val := by
        rw [← integerRowMap_range]
        exact ⟨a, rfl⟩
      exact hzero _ hm hne j (by simpa [integerRowMap, Finset.sum_apply] using ha)
    have ha0 : a = 0 := (integerRowMap_injective g) (he.trans (map_zero _).symm)
    exact congrFun ha0 i
  have hliQ : LinearIndependent ℚ (fun i : Fin n => g.val i j) :=
    hliZ.localization ℚ (nonZeroDivisors ℤ)
  have hsum : ∑ i, z i • g.val i j = 0 := by
    simpa [rationalRowMap, Finset.sum_apply] using hvj
  have hz : z = 0 := funext (Fintype.linearIndependent_iff.mp hliQ z hsum)
  rw [hz, map_zero]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RationalCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rationality of matrix centralizers

The commutant of a finite collection of rational matrices is spanned over
the reals by its rational matrices. This is the linear algebra part of
the homogeneous-orbit rationality step: it uses exactness of scalar
extension, and does not assert that a lattice stabilizer is dense in a
block group.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree

section Kernel

variable {V U V' U' : Type*}
  [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U]
  [AddCommGroup V'] [Module ℚ V'] [Module ℝ V'] [IsScalarTower ℚ ℝ V']
  [AddCommGroup U'] [Module ℚ U'] [Module ℝ U'] [IsScalarTower ℚ ℝ U']

/-- Exact scalar extension expresses every real kernel vector as a real
linear combination of rational kernel vectors. -/
private theorem kernel_spanned_of_baseChange
    (f : V →ₗ[ℚ] U) (f' : V' →ₗ[ℝ] U')
    (cV : V →ₗ[ℚ] V') (cU : U →ₗ[ℚ] U')
    (hV : IsBaseChange ℝ cV) (hU : IsBaseChange ℝ cU)
    (hcomm : cU.comp f = (f'.restrictScalars ℚ).comp cV) :
    f'.ker = Submodule.span ℝ (cV '' (f.ker : Set V)) := by
  let k : f.ker →ₗ[ℚ] f'.ker :=
    LinearMap.codRestrict (f'.ker.restrictScalars ℚ) (cV.comp f.ker.subtype) (by
      intro x
      change f' (cV x.val) = 0
      have he := LinearMap.congr_fun hcomm x.val
      have hx : f x.val = 0 := x.property
      simpa only [LinearMap.comp_apply, hx, map_zero,
        LinearMap.restrictScalars_apply] using he.symm)
  have hbase : IsBaseChange ℝ k :=
    IsBaseChange.of_left_exact ℝ k cV cU (by ext x; rfl) hcomm hV hU
      f.exact_subtype_ker_map Subtype.val_injective
      f'.exact_subtype_ker_map Subtype.val_injective
  apply le_antisymm
  · intro x hx
    have H : (⟨x, hx⟩ : f'.ker).val ∈ Submodule.span ℝ (cV '' (f.ker : Set V)) := by
      induction (⟨x, hx⟩ : f'.ker) using hbase.inductionOn with
      | zero => exact Submodule.zero_mem _
      | tmul v => exact Submodule.subset_span ⟨v.val, v.property, rfl⟩
      | smul a v hv => exact Submodule.smul_mem _ a hv
      | add v w hv hw => exact Submodule.add_mem _ hv hw
    exact H
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change f' (cV v) = 0
    have he := LinearMap.congr_fun hcomm v
    have hv0 : f v = 0 := hv
    simpa only [LinearMap.comp_apply, hv0, map_zero,
      LinearMap.restrictScalars_apply] using he.symm

end Kernel

section Matrices

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

lemma rationalMatrixCast_isBaseChange : IsBaseChange ℝ (rationalMatrixCast (ι := ι)) := by
  change IsBaseChange ℝ (((Algebra.linearMap ℚ ℝ).compLeft ι).compLeft ι)
  exact IsBaseChange.finitePow ι (IsBaseChange.finitePow ι (IsBaseChange.linearMap ℚ ℝ))

lemma mem_commutatorFamily_ker {K : Type*} [Field K]
    (B : κ → Matrix ι ι K) (M : Matrix ι ι K) :
    M ∈ (commutatorFamily B).ker ↔ ∀ k, Commute M (B k) := by
  change (fun k => M * B k - B k * M) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero, commute_iff_eq]

variable [Finite κ]

/-- The exact rationality statement for a finite matrix centralizer. -/
theorem real_commutant_eq_span_rational (B : κ → Matrix ι ι ℚ) :
    (commutatorFamily (fun k => rationalMatrixCast (B k))).ker =
      Submodule.span ℝ
        (rationalMatrixCast '' ((commutatorFamily B).ker : Set (Matrix ι ι ℚ))) := by
  apply kernel_spanned_of_baseChange (commutatorFamily B)
    (commutatorFamily fun k => rationalMatrixCast (B k))
    rationalMatrixCast (rationalMatrixCast.compLeft κ)
    rationalMatrixCast_isBaseChange
    (IsBaseChange.finitePow κ rationalMatrixCast_isBaseChange)
  apply LinearMap.ext
  intro M
  funext k
  change (Algebra.ofId ℚ ℝ).mapMatrix (M * B k - B k * M) =
    (Algebra.ofId ℚ ℝ).mapMatrix M * (Algebra.ofId ℚ ℝ).mapMatrix (B k) -
      (Algebra.ofId ℚ ℝ).mapMatrix (B k) * (Algebra.ofId ℚ ℝ).mapMatrix M
  simp only [map_sub, map_mul]

end Matrices

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LatticeCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centralizers of actual lattice stabilizers

The matrix centralizer of an arbitrary family of rational matrices is
spanned over `ℝ` by its rational matrices. Finite dimensionality reduces
the family to a basis of its rational span. This applies, in particular,
to the integral stabilizer of a homogeneous orbit in the lattice space.
The identification of that centralizer with the real block algebra is
kept separate from this rational linear algebra statement.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

private lemma commute_cast_of_mem_span
    (B : κ → Matrix ι ι ℚ) (M : Matrix ι ι ℝ)
    (hM : ∀ k, Commute M (rationalMatrixCast (B k)))
    {v : Matrix ι ι ℚ} (hv : v ∈ Submodule.span ℚ (Set.range B)) :
    Commute M (rationalMatrixCast v) := by
  let P : Submodule ℚ (Matrix ι ι ℚ) :=
    (Subalgebra.centralizer ℚ ({M} : Set (Matrix ι ι ℝ))).toSubmodule.comap rationalMatrixCast
  have hP : Submodule.span ℚ (Set.range B) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change rationalMatrixCast (B k) ∈ Subalgebra.centralizer ℚ ({M} : Set (Matrix ι ι ℝ))
    rw [Subalgebra.mem_centralizer_iff]
    intro X hX
    have he : X = M := Set.mem_singleton_iff.mp hX
    simpa only [he] using (hM k).eq
  have H := hP hv
  change rationalMatrixCast v ∈ Subalgebra.centralizer ℚ ({M} : Set (Matrix ι ι ℝ)) at H
  exact (Subalgebra.mem_centralizer_iff ℚ).mp H M (by simp)

lemma commute_rationalMatrixCast_iff (M N : Matrix ι ι ℚ) :
    Commute (rationalMatrixCast M) (rationalMatrixCast N) ↔ Commute M N := by
  change Commute ((Algebra.ofId ℚ ℝ).mapMatrix M) ((Algebra.ofId ℚ ℝ).mapMatrix N) ↔ _
  apply commute_map_iff
  exact Matrix.map_injective (FaithfulSMul.algebraMap_injective ℚ ℝ)

/-- No finiteness assumption on the matrix family is needed: only its
linear span matters, and that span has finite dimension. -/
theorem real_commutant_eq_span_rational_family (B : κ → Matrix ι ι ℚ) :
    (commutatorFamily (fun k => rationalMatrixCast (B k))).ker =
      Submodule.span ℝ
        (rationalMatrixCast '' ((commutatorFamily B).ker : Set (Matrix ι ι ℚ))) := by
  let S := Submodule.span ℚ (Set.range B)
  let b := Module.finBasis ℚ S
  let C : Fin (Module.finrank ℚ S) → Matrix ι ι ℚ := fun i => (b i).val
  have hS : Submodule.span ℚ (Set.range C) = S := by
    have h := congrArg (Submodule.map S.subtype) b.span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top,
      Function.comp_def, Submodule.subtype_apply, C] using h
  have hreal : (commutatorFamily (fun k => rationalMatrixCast (B k))).ker =
      (commutatorFamily (fun i => rationalMatrixCast (C i))).ker := by
    ext M
    rw [mem_commutatorFamily_ker, mem_commutatorFamily_ker]
    constructor
    · intro h i
      exact commute_cast_of_mem_span B M h (b i).property
    · intro h k
      apply commute_cast_of_mem_span C M h
      rw [hS]
      exact Submodule.subset_span ⟨k, rfl⟩
  have hrat : (commutatorFamily B).ker = (commutatorFamily C).ker := by
    ext M
    have H : rationalMatrixCast M ∈ (commutatorFamily (fun k => rationalMatrixCast (B k))).ker ↔
        rationalMatrixCast M ∈ (commutatorFamily (fun i => rationalMatrixCast (C i))).ker := by
      rw [hreal]
    simpa only [mem_commutatorFamily_ker, commute_rationalMatrixCast_iff] using H
  rw [hreal, real_commutant_eq_span_rational, ← hrat]

/-- The centralizer of an actual homogeneous-orbit stabilizer is
rational. The orbit group is arbitrary; no density or homogeneity
classification is built into this statement. -/
theorem latticeStabilizer_commutant_rational {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    (commutatorFamily (fun γ => rationalMatrixCast (latticeStabilizerMatrix g H γ))).ker =
      Submodule.span ℝ (rationalMatrixCast ''
        ((commutatorFamily (latticeStabilizerMatrix g H)).ker :
          Set (Matrix (Fin n) (Fin n) ℚ))) :=
  real_commutant_eq_span_rational_family (latticeStabilizerMatrix g H)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixConjugationDensity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite measures in the matrix conjugation representation

This is the elementary recurrence part of the needed Borel-density
argument. A finite measure invariant under a strict real contraction is
concentrated at zero. Applied to matrix coefficients, split diagonal
conjugation forces invariant finite matrix measures onto diagonal matrices.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree

lemma continuous_rootMatrixConjugation {n : ℕ} (i j : Fin n) (t : ℝ) :
    Continuous (rootMatrixConjugation i j t) := by
  unfold rootMatrixConjugation
  fun_prop

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ConjugationOrbit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugation maps on actual lattice orbit quotients

A matrix commuting with the lattice stabilizer defines a continuous
conjugation map on the corresponding homogeneous orbit quotient. Right
invariance of a measure on that quotient gives conjugation invariance of
its pushforward. This is the geometric bridge used by the elementary
matrix-density argument.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_slMatrixConjugation {n : ℕ} (h : G n) :
    Continuous (slMatrixConjugation h) := by
  unfold slMatrixConjugation
  fun_prop

lemma continuous_latticeOrbitRightAction {n : ℕ} (g : G n) (H : Subgroup (G n)) (h : H) :
    Continuous (fun x => latticeOrbitRightAction g H x h) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_id.mul continuous_const)

lemma continuous_conjugationOrbitMap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val) :
    Continuous (conjugationOrbitMap g H M hM) := by
  apply continuous_quot_lift
  unfold slMatrixConjugation
  fun_prop

lemma conjugationOrbitMap_rightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val)
    (x : LatticeOrbitQuotient g H) (h : H) :
    conjugationOrbitMap g H M hM (latticeOrbitRightAction g H x h) =
      slMatrixConjugation h.val (conjugationOrbitMap g H M hM x) := by
  induction x using Quotient.inductionOn with
  | h k => exact slMatrixConjugation_mul k.val h.val M

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FiniteOrbitDensity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix density for finite-volume lattice orbits

The actual lattice orbit quotient carries a nonzero finite invariant
measure. Conjugating any matrix which commutes with its stabilizer gives
a finite invariant matrix measure. Recurrence under a regular split
diagonal and the within-block root subgroups then forces the matrix into
the block-scalar algebra. No homogeneous classification is assumed here.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_root {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    slMatrixConjugation (Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ)) =
      rootMatrixConjugation i j 1 := by
  funext M
  simp only [slMatrixConjugation, Matrix.SpecialLinearGroup.transvection_inv,
    neg_neg, Matrix.SpecialLinearGroup.transvection_coe, rootMatrixConjugation,
    Matrix.transvection]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitRationality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational block centralizers from finite-volume lattice orbits

The rational matrices in the integral orbit-stabilizer centralizer span
its real centralizer. Conjugation by the actual lattice matrix transports
this statement to the embedding coordinates. Finite-orbit density then
identifies this transported centralizer with the block-scalar algebra.
-/

noncomputable section
open Matrix Module Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rationalMatrixCast_latticeStabilizer {n : ℕ} (g : G n) (H : Subgroup (G n))
    (γ : latticeOrbitStabilizer g H) :
    rationalMatrixCast (latticeStabilizerMatrix g H γ) =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val).val := by
  ext i j
  simp [rationalMatrixCast_apply, latticeStabilizerMatrix]

/-- Every actual point stabilizer element is a conjugated integral
stabilizer element. This uses the integral quotient, not an abstract
field action. -/
lemma pointOrbitStabilizer_eq_conjugate {n : ℕ} (g : G n) (H : Subgroup (G n))
    (s : pointOrbitStabilizer g H) :
    ∃ γ : latticeOrbitStabilizer g H,
      slMatrixConjugation g (rationalMatrixCast (latticeStabilizerMatrix g H γ)) =
        s.val.val.val := by
  have hs : (MulAut.conj g) s.val.val ∈ integralGroup n := s.property
  obtain ⟨γ, hγ⟩ := hs
  have hc : (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) =
      s.val.val := by
    rw [hγ]
    simp [MulAut.conj_apply, mul_assoc]
  have hm : γ ∈ latticeOrbitStabilizer g H := by
    change (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) ∈ H
    rw [hc]
    exact s.val.property
  refine ⟨⟨γ, hm⟩, ?_⟩
  rw [rationalMatrixCast_latticeStabilizer]
  simpa only [slMatrixConjugation, MulAut.conj_apply, inv_inv,
    Matrix.SpecialLinearGroup.coe_mul] using congrArg Subtype.val hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockOrbit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The standard block group and its finite-volume lattice orbits

The group here is defined by its concrete action on the coordinate
blocks. The split diagonals and all within-block root groups lie in it.
The preceding rationality argument then forces any nontrivial partition
with a finite-volume orbit through a generic prime-degree lattice to be
the universal partition.
-/

noncomputable section
open Matrix Module Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma blockMatrixGroup_commute {n : ℕ} (r : Setoid (Fin n))
    (g : blockMatrixGroup r) (c : Fin n → ℝ) (hc : c ∈ blockCoordinateAlgebra r) :
    Commute (Matrix.diagonal c) g.val.val := by
  have he := congrArg (fun M => g.val.val * M) (g.property c hc)
  have hg : g.val.val * g.val⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  change Matrix.diagonal c * g.val.val = g.val.val * Matrix.diagonal c
  simpa only [slMatrixConjugation, ← mul_assoc, hg, one_mul] using he

lemma transvection_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (i j : Fin n) (hij : i ≠ j) (hr : r i j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ blockMatrixGroup r := by
  intro c hc
  apply slMatrixConjugation_eq_self
  exact (diagonal_commute_transvection_iff c hij).mpr (hc i j hr)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockNormalizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The connected normalizer of the block algebra

Conjugation permutes the primitive block projections. In a connected
family starting at the identity these projections cannot move, since
their diagonal coordinates remain idempotents. Consequently the identity
component of the block-algebra normalizer preserves every block.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma blockProjection_mul_self {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    blockProjection r k * blockProjection r k = blockProjection r k := by
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  dsimp only
  split_ifs <;> norm_num

lemma slMatrixConjugation_eq_self_iff {n : ℕ} (g : G n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation g M = M ↔ Commute M g.val := by
  constructor
  · intro h
    have he := congrArg (fun A => g.val * A) h
    have hg : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change M * g.val = g.val * M
    simpa only [slMatrixConjugation, ← mul_assoc, hg, one_mul] using he
  · exact slMatrixConjugation_eq_self g M

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockNormalizerFiniteIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite quotient of the block normalizer

Conjugation acts on the finite set of idempotents in the block-scalar
algebra. The kernel is precisely the block matrix group. Thus the latter
has finite index in the full normalizer, including its disconnected part.
-/

noncomputable section
open Matrix Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_eq_self_of_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (g : G n) (hg : g ∈ blockMatrixGroup r)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ blockScalarAlgebra r) :
    slMatrixConjugation g M = M := by
  obtain ⟨hD, hc⟩ := (mem_blockScalarAlgebra_iff r M).mp hM
  rw [hD]
  exact hg _ hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootSubgroups
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

 
lemma diag2n_decompose {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
      Matrix.SpecialLinearGroup.transvection hij a *
      Matrix.SpecialLinearGroup.transvection hij (-1) *
      Matrix.SpecialLinearGroup.transvection hij.symm 1 *
      Matrix.SpecialLinearGroup.transvection hij (-1) := by
  ext r c
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.SpecialLinearGroup.transvection_coe,mul_add,add_mul,Matrix.one_mul,Matrix.mul_one]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hci : c = i <;> by_cases hcj : c = j
  all_goals simp_all [Matrix.single_apply,Matrix.diagonal_apply,
    Matrix.one_apply,eq_comm]

 
theorem specialLinear_transvection_induction {ι F : Type*} [Fintype ι]
    [DecidableEq ι] [Nontrivial ι] [Field F]
    (P : Matrix.SpecialLinearGroup ι F → Prop)
    (hroot : ∀ (i j : ι) (hij : i ≠ j) (a : F),
      P (Matrix.SpecialLinearGroup.transvection hij a))
    (hmul : ∀ A B, P A → P B → P (A*B))
    (g : Matrix.SpecialLinearGroup ι F) : P g := by
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' P g _ hroot hmul
  intro i j hij a ha
  rw [diag2n_decompose hij a ha]
  refine hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ ?_ ?_) ?_) ?_) ?_) ?_
  all_goals exact hroot _ _ _ _

end PrimeDegreePackets


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

 
lemma root_subgroup_chain {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (H : Subgroup (Matrix.SpecialLinearGroup ι F)) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hijH : ∀ a : F, Matrix.SpecialLinearGroup.transvection hij a ∈ H)
    (hjkH : ∀ b : F, Matrix.SpecialLinearGroup.transvection hjk b ∈ H) :
    ∀ c : F, Matrix.SpecialLinearGroup.transvection hik c ∈ H := by
  intro c
  rw [← mul_one c,← transvection_chain_commutator hij hjk hik c 1]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hijH _) (hjkH _)) (hijH _)) (hjkH _)

end PrimeDegreePackets


namespace PrimeDegreePackets



theorem right_invariant_of_all_roots {n : ℕ} (hn : 2 ≤ n)
    (μ : Measure (X n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j) (a : ℝ),
      Measure.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) μ = μ) :
    ∀ g : G n, Measure.map (fun x => rightAction x g) μ = μ := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro g
  exact specialLinear_transvection_induction (fun g => g ∈ invariantRightSubgroup μ)
    hroot (fun _ _ hg hh => (invariantRightSubgroup μ).mul_mem hg hh) g

end PrimeDegreePackets

open scoped Topology Classical Matrix
namespace PrimeDegreePackets

lemma rootInvarianceRelation_trans {n : ℕ} (μ : Measure (X n)) :
    ∀ ⦃i j k : Fin n⦄, rootInvarianceRelation μ i j →
      rootInvarianceRelation μ j k → rootInvarianceRelation μ i k := by
  intro i j k hij hjk
  rcases hij with rfl | ⟨hij,Hij⟩
  · exact hjk
  rcases hjk with rfl | ⟨hjk,Hjk⟩
  · exact Or.inr ⟨hij,Hij⟩
  by_cases hik : i = k
  · exact Or.inl hik
  exact Or.inr ⟨hik,root_subgroup_chain _ hij hjk hik Hij Hjk⟩



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

 

theorem fixedPoint_mem_closed_convex_orbit {H E : Type*} [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : H → E →ₗᵢ[ℝ] E) (hU : ∀ g h x, U g (U h x) = U (g*h) x)
    (x : E) : ∃ v : E, v ∈ closure (convexHull ℝ (Set.range (fun g => U g x))) ∧
      ∀ g, U g v = v := by
  let O := Set.range (fun g => U g x)
  let C := closure (convexHull ℝ O)
  have hconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hnon : C.Nonempty := ⟨U 1 x,subset_closure (subset_convexHull ℝ O ⟨1,rfl⟩)⟩
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hnon
    isClosed_closure.isComplete hconv (0:E)
  refine ⟨v,hv,?_⟩
  intro g
  have himage : U g '' C ⊆ C := by
    calc
      U g '' C ⊆ closure (U g '' convexHull ℝ O) :=
        image_closure_subset_closure_image (U g).continuous
      _ = closure (convexHull ℝ (U g '' O)) := by
        exact congrArg closure ((U g).toLinearMap.image_convexHull O)
      _ ⊆ C := closure_mono (convexHull_mono ?_)
    rintro _ ⟨_,⟨h,rfl⟩,rfl⟩
    exact ⟨g*h,(hU g h x).symm⟩
  have hg : U g v ∈ C := himage ⟨v,hv,rfl⟩
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin (U g v) hg
  have hn := norm_sub_sq_real (U g v) v
  have hh : inner ℝ v (U g v) = inner ℝ (U g v) v := real_inner_comm _ _
  simp only [zero_sub,inner_neg_left,inner_sub_right,real_inner_self_eq_norm_sq] at hinner
  rw [(U g).norm_map] at hn
  have he : ‖U g v-v‖^2 = 0 := by nlinarith [sq_nonneg ‖U g v-v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))



end PrimeDegreePackets

open scoped Classical
namespace PrimeDegreePackets


lemma measurable_actionInvariantSigma {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] {f : Y → ℝ} (hf : Measurable f)
    (hinv : ∀ (g : H) (y : Y), f (g • y) = f y) : Measurable[actionInvariantSigma H Y] f := by
  intro s hs
  rw [actionInvariantSigma,MeasurableSpace.measurableSet_iInf]
  intro g
  refine ⟨hf hs,?_⟩
  ext y
  simp only [Set.mem_preimage,hinv]

 

theorem exists_pointwise_invariant_representative {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [MeasurableSpace Y] (μ : Measure Y)
    (hm : ∀ g : H, Measurable (fun y : Y => g • y))
    (f : Y → ℝ) (hf : Measurable f)
    (hinv : ∀ g : H, (fun y => f (g • y)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[actionInvariantSigma H Y] f₀ ∧ f₀ =ᵐ[μ] f ∧
      ∀ (g : H) (y : Y), f₀ (g • y) = f₀ y := by
  let A : Set Y := {y | ∀ g : H, f (g • y) = f y}
  have hA : MeasurableSet A := by
    simpa only [A,Set.ofPred_forall,Function.comp_apply] using
      MeasurableSet.iInter (fun g => measurableSet_eq_fun (hf.comp (hm g)) hf)
  have hconull : ∀ᵐ y ∂μ, y ∈ A := ae_all_iff.mpr hinv
  have hstable (g : H) (y : Y) : g • y ∈ A ↔ y ∈ A := by
    constructor
    · intro hy h
      have hfgy : f y = f (g • y) := by simpa only [inv_smul_smul] using hy g⁻¹
      have hh := hy (h*g⁻¹)
      simpa only [mul_smul,inv_smul_smul,hfgy] using hh
    · intro hy h
      simpa only [mul_smul,hy g] using hy (h*g)
  let f₀ := A.indicator f
  have hmeas : Measurable f₀ := hf.indicator hA
  have hfixed (g : H) (y : Y) : f₀ (g • y) = f₀ y := by
    by_cases hy : y ∈ A
    · simp only [f₀,Set.indicator_of_mem hy,Set.indicator_of_mem ((hstable g y).mpr hy)]
      exact hy g
    · simp only [f₀,Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (not_imp_not.mpr (hstable g y).mp hy)]
  refine ⟨f₀,measurable_actionInvariantSigma hmeas hfixed,?_,hfixed⟩
  filter_upwards [hconull] with y hy
  exact Set.indicator_of_mem hy f

end PrimeDegreePackets

open scoped Topology ENNReal Classical
namespace PrimeDegreePackets


lemma orbitConvexHull_measurable {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (hm : ∀ g : H, Measurable (fun y : Y => g • y))
    {f F : Y → ℝ} (hf : Measurable f) (hF : F ∈ orbitConvexHull (H := H) f) :
    Measurable F := by
  have hc : Convex ℝ {F : Y → ℝ | Measurable F} := by
    intro F hF G hG a b _ _ _
    exact (hF.const_smul a).add (hG.const_smul b)
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩
  exact hf.comp (hm g)

lemma orbitConvexHull_interval {H Y : Type*} [Group H] [MulAction H Y]
    {f F : Y → ℝ} {a b : ℝ} (hf : ∀ y, f y ∈ Set.Icc a b)
    (hF : F ∈ orbitConvexHull (H := H) f) : ∀ y, F y ∈ Set.Icc a b := by
  have hc : Convex ℝ {F : Y → ℝ | ∀ y, F y ∈ Set.Icc a b} := by
    intro F hF G hG c d hc hd hcd y
    exact (convex_Icc a b) (hF y) (hG y) hc hd hcd
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩ y
  exact hf (g • y)

 

lemma orbitConvexHull_integral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    Integrable F ν ∧ (∫ y, F y ∂ν) = ∫ y, f y ∂ν := by
  let : MeasurableConstSMul H Y := ⟨fun g => (hp g).measurable⟩
  have hc : Convex ℝ {F : Y → ℝ | Integrable F ν ∧ (∫ y, F y ∂ν) = ∫ y, f y ∂ν} := by
    intro F hF G hG a b _ _ hab
    refine ⟨(hF.1.smul a).add (hG.1.smul b),?_⟩
    change (∫ y, a * F y+b * G y ∂ν) = _
    rw [integral_add (hF.1.const_mul a) (hG.1.const_mul b),
      integral_const_mul,integral_const_mul,hF.2,hG.2]
    rw [← add_mul,hab,one_mul]
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩
  exact ⟨(hp g).integrable_comp_of_integrable hf,
    (hp g).integral_comp (MeasurableEquiv.smul g).measurableEmbedding f⟩

end PrimeDegreePackets


namespace PrimeDegreePackets

 
lemma lp_convex_orbit_representative {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (μ : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ)
    {f : Y → ℝ} (hf : MemLp f 2 μ) {z : Lp ℝ 2 μ}
    (hz : z ∈ convexHull ℝ (Set.range fun g : H =>
      Lp.compMeasurePreservingₗᵢ ℝ (fun y : Y => g⁻¹ • y) (hp g⁻¹) (hf.toLp f))) :
    ∃ F ∈ orbitConvexHull (H := H) f, z =ᵐ[μ] F := by
  let C : Set (Lp ℝ 2 μ) := {z | ∃ F ∈ orbitConvexHull (H := H) f, z =ᵐ[μ] F}
  have hconv : Convex ℝ C := by
    intro z hz w hw a b ha hb hab
    obtain ⟨F,hF,hzF⟩ := hz
    obtain ⟨G,hG,hwG⟩ := hw
    refine ⟨a • F+b • G, (convex_convexHull ℝ _) hF hG ha hb hab,?_⟩
    filter_upwards [Lp.coeFn_add (a • z) (b • w),Lp.coeFn_smul a z,
      Lp.coeFn_smul b w,hzF,hwG] with y hy ha' hb' hz' hw'
    simp only [hy,ha',hb',Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz',hw']
  apply convexHull_min ?_ hconv hz
  rintro _ ⟨g,rfl⟩
  refine ⟨fun y => f (g⁻¹ • y),subset_convexHull ℝ _ ⟨g⁻¹,rfl⟩,?_⟩
  exact (Lp.coeFn_compMeasurePreserving (hf.toLp f) (hp g⁻¹)).trans
    ((hp g⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)

 

theorem exists_invariant_orbit_average_limit {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [MeasurableSpace Y] (μ : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ)
    {f : Y → ℝ} (hf : MemLp f 2 μ) :
    ∃ v : Y → ℝ, Measurable[actionInvariantSigma H Y] v ∧
      (∀ (g : H) (y : Y), v (g • y) = v y) ∧
      ∃ F : ℕ → Y → ℝ, (∀ k, F k ∈ orbitConvexHull (H := H) f) ∧
        ∀ᵐ y ∂μ, Tendsto (fun k => F k y) atTop (𝓝 (v y)) := by
  let U : H → (Lp ℝ 2 μ) →ₗᵢ[ℝ] (Lp ℝ 2 μ) := fun g =>
    Lp.compMeasurePreservingₗᵢ ℝ (fun y : Y => g⁻¹ • y) (hp g⁻¹)
  have hU (g h : H) (x : Lp ℝ 2 μ) : U g (U h x) = U (g*h) x := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ x) =
      Lp.compMeasurePreserving (fun y : Y => (g*h)⁻¹ • y) (hp (g*h)⁻¹) x
    rw [← Lp.compMeasurePreserving_comp_apply]
    simp only [Function.comp_def,_root_.mul_inv_rev,mul_smul]
  obtain ⟨v,hv,hfix⟩ := fixedPoint_mem_closed_convex_orbit U hU (hf.toLp f)
  have hvfix (g : H) : (fun y => v (g • y)) =ᵐ[μ] v := by
    have H := Lp.coeFn_compMeasurePreserving v (hp g)
    have he : Lp.compMeasurePreserving (fun y : Y => g • y) (hp g) v = v := by
      have he := hfix g⁻¹
      change Lp.compMeasurePreserving (fun y : Y => (g⁻¹)⁻¹ • y) _ v = v at he
      simpa only [inv_inv] using he
    simpa only [he,Function.comp_def] using H.symm
  obtain ⟨v₀,hv₀,hveq,hvfix₀⟩ := exists_pointwise_invariant_representative μ
    (fun g => (hp g).measurable) v (Lp.stronglyMeasurable v).measurable hvfix
  obtain ⟨z,hz,hzlim⟩ := mem_closure_iff_seq_limit.mp hv
  choose F hF hzF using fun k => lp_convex_orbit_representative μ hp hf (hz k)
  obtain ⟨ns,-,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hzlim).exists_seq_tendsto_ae
  refine ⟨v₀,hv₀,hvfix₀,F ∘ ns,fun k => hF (ns k),?_⟩
  filter_upwards [hns,hveq,ae_all_iff.mpr hzF] with y hy hvy hzy
  simpa only [Function.comp_apply,hzy,hvy] using hy

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma orbitConvexHull_aeSetIntegral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S =ᵐ[ν] S)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    (∫ y in S, F y ∂ν) = ∫ y in S, f y ∂ν := by
  apply (orbitConvexHull_integral (ν.restrict S) (fun g => ?_) hf.integrableOn hF).2
  have hg := (hp g).restrict_preimage hS
  simpa only [Measure.restrict_congr_set (hSfix g)] using hg

 

lemma invariant_set_independent_of_orbit_indicator_limit {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {B : Set Y} (hB : MeasurableSet B) {F : ℕ → Y → ℝ}
    (hF : ∀ k, F k ∈ orbitConvexHull (H := H) (B.indicator (fun _ => (1:ℝ))))
    {c : ℝ} (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => F k y) atTop (𝓝 c))
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S =ᵐ[ν] S) :
    ν.real (B ∩ S) = ν.real S * ν.real B := by
  have hbmeas : Measurable (B.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hB
  have hbint : Integrable (B.indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator hB
  have hfm (k : ℕ) : Measurable (F k) :=
    orbitConvexHull_measurable (fun g => (hp g).measurable) hbmeas (hF k)
  have hbnd (k : ℕ) (y : Y) : ‖F k y‖ ≤ 1 := by
    have hb : ∀ y : Y, B.indicator (fun _ => (1:ℝ)) y ∈ Icc (0:ℝ) 1 := by
      intro y
      by_cases hy : y ∈ B <;> simp [hy]
    have hx := orbitConvexHull_interval hb (hF k) y
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hc : ν.real B = c := by
    have H := tendsto_integral_of_dominated_convergence (fun _ : Y => (1:ℝ))
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ (hbnd k)) hlim
    have hi (k : ℕ) : (∫ y, F k y ∂ν) = ν.real B := by
      rw [(orbitConvexHull_integral ν hp hbint (hF k)).2,integral_indicator hB]
      simp [integral_const,Measure.real]
    simp only [hi,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at H
    exact tendsto_nhds_unique tendsto_const_nhds H
  have H := tendsto_integral_of_dominated_convergence (μ := ν.restrict S)
    (fun _ : Y => (1:ℝ))
    (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
    (fun k => ae_of_all _ (hbnd k)) (ae_restrict_of_ae hlim)
  have hi (k : ℕ) : (∫ y in S, F k y ∂ν) = ν.real (B ∩ S) := by
    rw [orbitConvexHull_aeSetIntegral ν hp hS hSfix hbint (hF k),integral_indicator hB]
    simp [integral_const,Measure.real,Measure.restrict_apply hB]
  simp only [hi,integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at H
  rw [← hc] at H
  exact tendsto_nhds_unique tendsto_const_nhds H

 

theorem ergodicSMul_of_orbit_indicator_limits {H Y : Type*} [Group H] [MulAction H Y]
    [mY : MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    (C : Set (Set Y)) (hgen : mY = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (havg : ∀ B ∈ C, ∃ c : ℝ, ∃ F : ℕ → Y → ℝ,
      (∀ k, F k ∈ orbitConvexHull (H := H) (B.indicator (fun _ => (1:ℝ)))) ∧
        ∀ᵐ y ∂ν, Tendsto (fun k => F k y) atTop (𝓝 c)) :
    ErgodicSMul H Y ν := by
  refine { measure_preimage_smul := fun g _ hs => (hp g).measure_preimage hs.nullMeasurableSet
           aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  intro S hS hSfix
  have hmeas (B : Set Y) (hB : B ∈ C) : MeasurableSet B := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hB
  have hind (B : Set Y) (hB : B ∈ C) : ν.real (B ∩ S) = ν.real S * ν.real B := by
    obtain ⟨c,F,hF,hlim⟩ := havg B hB
    exact invariant_set_independent_of_orbit_indicator_limit ν hp (hmeas B hB)
      hF hlim hS hSfix
  have he : ν.restrict S = (ν S) • ν := by
    apply ext_of_generate_finite C hgen hpi
    · intro B hB
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).mp
      · simpa only [Measure.real,Measure.restrict_apply (hmeas B hB),
          Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul] using hind B hB
      · simp only [Measure.smul_apply,smul_eq_mul]
        exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
    · simp
  have hreal := congrArg (fun η : Measure Y => η.real S) he
  simp only [Measure.real,Measure.restrict_apply hS,inter_self,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul] at hreal
  have hz : (ν S).toReal * ((ν S).toReal - 1) = 0 := by nlinarith [hreal]
  rw [eventuallyConst_set]
  rcases mul_eq_zero.mp hz with hz | hz
  · right
    apply measure_eq_zero_iff_ae_notMem.mp
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)
  · left
    have hmass : ν S = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
      simpa only [ENNReal.toReal_one] using sub_eq_zero.mp hz
    have hcompl : ν Sᶜ = 0 := by rw [measure_compl hS (measure_ne_top _ _),hmass,measure_univ,tsub_self]
    exact (measure_eq_zero_iff_ae_notMem.mp hcompl).mono fun y hy => not_not.mp hy

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ErgodicDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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
namespace PrimeDegreePackets

 

theorem condExpKernel_invariant {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hm : m ≤ mY) {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hfix : m ≤ MeasurableSpace.invariants T) :
    ∀ᵐ x ∂μ.trim hm, Measure.map T (condExpKernel μ m x) = condExpKernel μ m x := by
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdiag : τ ⊗ₘ κ = @Measure.map Y (Y × Y) mY (m.prod mY) Function.diag μ :=
    compProd_trim_condExpKernel hm
  have hprod : τ ⊗ₘ κ.map T = τ ⊗ₘ κ := by
    rw [Measure.compProd_map hT.measurable, hdiag]
    apply Measure.ext_prod
    intro A B hA hB
    have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
      (measurable_id'' hm).prodMk measurable_id
    rw [Measure.map_apply (measurable_id.prodMap hT.measurable) (hA.prod hB),
      Measure.map_apply hδ
        ((measurable_id.prodMap hT.measurable) (hA.prod hB)),
      Measure.map_apply hδ (hA.prod hB)]
    change μ (A ∩ T ⁻¹' B) = μ (A ∩ B)
    conv_lhs => rw [← (hfix _ hA).2, ← Set.preimage_inter]
    exact hT.measure_preimage ((hm _ hA |>.inter hB).nullMeasurableSet)
  let : IsMarkovKernel (κ.map T) := Kernel.IsMarkovKernel.map κ hT.measurable
  have H₁ := condKernel_compProd τ (κ.map T)
  have H₂ := condKernel_compProd τ κ
  have H₁' : (τ ⊗ₘ κ).condKernel =ᵐ[τ] κ.map T := by
    simpa only [hprod] using H₁
  have H := H₁'.symm.trans H₂
  filter_upwards [H] with x hx
  change (κ.map T) x = κ x at hx
  simpa only [Kernel.map_apply _ hT.measurable] using hx

 

theorem invariant_kernel_decomposition {Y I : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Countable I]
    (μ : Measure Y) [IsProbabilityMeasure μ] (T : I → Y → Y)
    (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hm : m ≤ mY)
    (hfix : ∀ i, m ≤ MeasurableSpace.invariants (T i)) :
    condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
      ∀ᵐ x ∂μ.trim hm, ∀ i, Measure.map (T i) (condExpKernel μ m x) =
        condExpKernel μ m x := by
  exact ⟨condExpKernel_comp_trim hm, ae_all_iff.mpr
    (fun i => condExpKernel_invariant m μ hm (hT i) (hfix i))⟩

 

theorem condExpKernel_ae_constant {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hm : m ≤ mY) {f : Y → ℝ} (hf : Measurable[m] f) :
    ∀ᵐ x ∂μ.trim hm, ∀ᵐ y ∂condExpKernel μ m x, f y = f x := by
  have hfull : Measurable f := hf.mono hm le_rfl
  have hset : @MeasurableSet (Y × Y) (m.prod mY) {p | f p.2 = f p.1} :=
    measurableSet_eq_fun (hfull.comp measurable_snd) (hf.comp measurable_fst)
  let : MeasurableSpace (Y × Y) := m.prod mY
  apply (Measure.ae_compProd_iff hset).mp
  rw [compProd_trim_condExpKernel hm]
  have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  exact (@ae_map_iff Y (Y × Y) mY (m.prod mY) μ Function.diag
    hδ.aemeasurable (fun p => f p.2 = f p.1) hset).mpr
      (Eventually.of_forall fun _ => rfl)

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem preserving_of_dense_action {G H Y : Type*} [Group G] [Group H]
    [TopologicalSpace G] [FirstCountableTopology G] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [HasOuterApproxClosed Y] [MulAction G Y] [ContinuousSMul G Y]
    («φ» : H →* G) (hdense : DenseRange «φ») (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ h : H, MeasurePreserving (fun y : Y => «φ» h • y) ν ν) (g : G) :
    MeasurePreserving (fun y : Y => g • y) ν ν := by
  refine ⟨(continuous_const_smul g).measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (continuous_const_smul g).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  have hcont : Continuous (fun a : G => ∫ y, f (a • y) ∂ν) :=
    continuous_of_dominated
      (fun a => (f.continuous.comp (continuous_const_smul a)).aestronglyMeasurable)
      (fun a => ae_of_all _ (fun y => f.norm_coe_le_norm (a • y)))
      (integrable_const ‖f‖)
      (ae_of_all _ (fun y => f.continuous.comp (continuous_id.smul continuous_const)))
  refine hdense.induction_on (p := fun a : G => (∫ y, f (a • y) ∂ν) = ∫ y, f y ∂ν)
    g (isClosed_eq hcont continuous_const) ?_
  intro h
  rw [← integral_map (hp h).measurable.aemeasurable f.continuous.aestronglyMeasurable,
    (hp h).map_eq]

end PrimeDegreePackets


open MeasureTheory Set Topology UniformSpace TopologicalSpace

open scoped ENNReal Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootMatrixDensity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.compatMatrixBorelSpaceFPF _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.compatMatrixBorelSpacePlucker _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite distributions in a root conjugation representation

Root conjugation is polynomial of degree at most two in its parameter.
Recurrence first kills the lower-left coefficient and then every linear
coefficient. A finite invariant matrix distribution is therefore supported
on the actual root centralizer.
-/

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree

private lemma linear_coefficient_zero_of_recurrence
    {α : Type*} [TopologicalSpace α] (f : α → α) (x : α)
    (hrec : ∀ U ∈ 𝓝 x, ∃ᶠ m : ℕ in atTop, f^[m] x ∈ U)
    (p : α → ℝ) (hp : Continuous p) (c : ℝ)
    (hlin : ∀ m : ℕ, p (f^[m] x) = p x + (m : ℝ) * c) : c = 0 := by
  by_contra hc
  let U : Set α := {y | |p y - p x| < 1}
  have hU : U ∈ 𝓝 x := by
    apply (isOpen_lt (hp.sub continuous_const).abs continuous_const).mem_nhds
    change |p x - p x| < 1
    simp
  have hgrowth : Tendsto (fun m : ℕ => (m : ℝ) * |c|) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (abs_pos.mpr hc) tendsto_natCast_atTop_atTop
  obtain ⟨m, hm, hm'⟩ := ((hrec U hU).and_eventually (hgrowth.eventually_ge_atTop 1)).exists
  change |p (f^[m] x) - p x| < 1 at hm
  rw [hlin] at hm
  have he : |p x + (m : ℝ) * c - p x| = (m : ℝ) * |c| := by
    rw [add_sub_cancel_left, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m)]
  rw [he] at hm
  exact (not_lt_of_ge hm') hm

lemma rootMatrixConjugation_add {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (s t : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    rootMatrixConjugation i j s (rootMatrixConjugation i j t M) =
      rootMatrixConjugation i j (s + t) M := by
  unfold rootMatrixConjugation
  calc
    _ = (Matrix.transvection i j s * Matrix.transvection i j t) * M *
        (Matrix.transvection i j (-t) * Matrix.transvection i j (-s)) := by noncomm_ring
    _ = _ := by
      rw [Matrix.transvection_mul_transvection_same i j hij,
        Matrix.transvection_mul_transvection_same i j hij]
      congr 2
      ring

lemma rootMatrixConjugation_iterate {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (M : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    (rootMatrixConjugation i j 1)^[m] M = rootMatrixConjugation i j (m : ℝ) M := by
  induction m with
  | zero => simp [rootMatrixConjugation]
  | succ m hm =>
    rw [Function.iterate_succ_apply', hm, rootMatrixConjugation_add i j hij]
    simp only [Nat.cast_add, Nat.cast_one, add_comm]

lemma rootMatrixConjugation_entry {n : ℕ} (i j : Fin n) (t : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    rootMatrixConjugation i j t M a b = M a b +
      t * ((if a = i then M j b else 0) - (if b = j then M a i else 0)) -
      t ^ 2 * (if a = i ∧ b = j then M j i else 0) := by
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      simp [rootMatrixConjugation]
      ring
    · simp [rootMatrixConjugation, hbj]
  · by_cases hbj : b = j
    · subst b
      simp [rootMatrixConjugation, hai]
    · simp [rootMatrixConjugation, hai, hbj]

/-- Root-conjugation recurrence forces every matrix to commute with the
root, almost everywhere for any finite invariant distribution. -/
theorem ae_commute_root_of_conjugation_invariance {n : ℕ}
    (ν : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsFiniteMeasure ν]
    (i j : Fin n) (hij : i ≠ j)
    (hinv : ν.map (rootMatrixConjugation i j 1) = ν) :
    ∀ᵐ M ∂ν, Commute M (Matrix.transvection i j (1 : ℝ)) := by
  let f := rootMatrixConjugation i j 1
  have hf : MeasurePreserving f ν ν :=
    ⟨(continuous_rootMatrixConjugation i j 1).measurable, hinv⟩
  filter_upwards [hf.conservative.ae_frequently_mem_of_mem_nhds] with M hrec
  have hji : M j i = 0 := by
    have he := linear_coefficient_zero_of_recurrence f M hrec (fun N => N j j)
      (by fun_prop) (-M j i) (by
        intro m
        rw [rootMatrixConjugation_iterate i j hij, rootMatrixConjugation_entry]
        simp [hij.symm])
    exact neg_eq_zero.mp he
  have hcoeff (a b : Fin n) :
      (if a = i then M j b else 0) - (if b = j then M a i else 0) = 0 := by
    apply linear_coefficient_zero_of_recurrence f M hrec (fun N => N a b) (by fun_prop)
    intro m
    rw [rootMatrixConjugation_iterate i j hij, rootMatrixConjugation_entry]
    simp only [hji, ite_self, mul_zero, sub_zero]
  have hfixed : rootMatrixConjugation i j 1 M = M := by
    ext a b
    rw [rootMatrixConjugation_entry, hcoeff]
    simp only [hji, ite_self, mul_zero, sub_zero, add_zero]
  have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ =>
    N * Matrix.transvection i j (1 : ℝ)) hfixed
  have hu : Matrix.transvection i j (-1 : ℝ) * Matrix.transvection i j (1 : ℝ) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij]
    simp
  change M * Matrix.transvection i j (1 : ℝ) = Matrix.transvection i j (1 : ℝ) * M
  simpa only [rootMatrixConjugation, mul_assoc, hu, mul_one] using he.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_GenericRootCommutant
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A generic finite root orbit has a commutative stabilizer centralizer

One invariant root forces one column of every centralizing matrix to be
scalar. In the rational centralizer, evaluation in that column is
faithful by genericity of the actual lattice. Rational centralizing
matrices therefore commute, and scalar extension gives the same result
for the real centralizer. This removes any need to exclude singleton
blocks before treating the larger homogeneous orbit group.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma offColumn_zero_of_commute_root {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hM : Commute M (Matrix.transvection i j (1 : ℝ)))
    (a : Fin n) (hai : a ≠ i) : M a i = 0 := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A a j) hM.eq
  simp only [Matrix.mul_transvection_apply_same,
    Matrix.transvection_mul_apply_of_ne (i := i) (j := j) a j hai 1 M, one_mul] at he
  linarith

/-- Transport a centralizer element to the original integral coordinates. -/
lemma inverseConjugate_mem_realStabilizer {n : ℕ} (g : G n) (L : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    slMatrixConjugation g⁻¹ M ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker := by
  rw [mem_commutatorFamily_ker]
  intro γ
  let h : L := ⟨(MulAut.conj g⁻¹)
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val), γ.property⟩
  have hs : h ∈ pointOrbitStabilizer g L := by
    change (MulAut.conj g) h.val ∈ integralGroup n
    refine ⟨γ.val, ?_⟩
    simp only [h, MulAut.conj_apply, inv_inv]
    simp [mul_assoc]
  have he : h.val.val = slMatrixConjugation g
      (rationalMatrixCast (latticeStabilizerMatrix g L γ)) := by
    rw [rationalMatrixCast_latticeStabilizer]
    simp only [h, slMatrixConjugation, MulAut.conj_apply, inv_inv,
      Matrix.SpecialLinearGroup.coe_mul]
  have hcomm := (hM ⟨h, hs⟩).map (slMatrixConjugationHom g⁻¹)
  change Commute (slMatrixConjugation g⁻¹ M)
    (slMatrixConjugation g⁻¹ h.val.val) at hcomm
  rw [he] at hcomm
  simpa only [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] using hcomm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitGenericity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the generic-basepoint condition

A finite invariant measure on a block orbit pushes to an invariant
measure on the lattice space. Diagonal recurrence gives a generic
basepoint almost everywhere. Changing to that basepoint removes the
genericity hypothesis from the prime-degree block-orbit obstruction.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_latticeOrbitPoint {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    Continuous (latticeOrbitPoint g H) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_const.mul continuous_subtype_val)

lemma latticeOrbitPoint_rightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (x : LatticeOrbitQuotient g H) (h : H) :
    latticeOrbitPoint g H (latticeOrbitRightAction g H x h) =
      rightAction (latticeOrbitPoint g H x) h.val := by
  induction x using Quotient.inductionOn with
  | h a =>
    change Quotient.mk _ (g * (a.val * h.val)) = Quotient.mk _ ((g * a.val) * h.val)
    rw [mul_assoc]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitMeasureTransfer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Invariant measures on actual lattice orbits

The quotient by the actual point stabilizer injects into the lattice space.
For a closed matrix subgroup this injection is a Borel embedding, even when
the orbit is not closed. A finite invariant measure concentrated on that
orbit therefore pulls back to a finite invariant measure on the quotient.

This discharges the measure-transfer part of the homogeneous-orbit argument;
it does not assert the existence of a homogeneous orbit supporting a given
measure.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma latticeOrbitPoint_injective {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    Function.Injective (latticeOrbitPoint g H) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      have hab := Quotient.exact hxy
      change QuotientGroup.rightRel (integralGroup n) (g * a.val) (g * b.val) at hab
      change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b
      rw [QuotientGroup.rightRel_apply] at hab ⊢
      change g * (b.val * a.val⁻¹) * g⁻¹ ∈ integralGroup n
      simpa only [_root_.mul_inv_rev, mul_assoc] using hab

private lemma measurableEmbedding_of_continuous_injective_sigmaCompact
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [SigmaCompactSpace α] [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [BorelSpace β] (f : α → β)
    (hf : Continuous f) (hinj : Function.Injective f) : MeasurableEmbedding f := by
  refine ⟨hinj, hf.measurable, ?_⟩
  intro s hs
  have hcover : f '' s = ⋃ k : ℕ, f '' (s ∩ compactCovering α k) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := exists_mem_compactCovering x
      exact mem_iUnion.mpr ⟨k, x, ⟨hx, hk⟩, rfl⟩
    · intro hy
      obtain ⟨k, x, hx, hxy⟩ := mem_iUnion.mp hy
      exact ⟨x, hx.1, hxy⟩
  rw [hcover]
  apply MeasurableSet.iUnion
  intro k
  let C := compactCovering α k
  let : CompactSpace C := (isCompact_iff_compactSpace.mp (isCompact_compactCovering α k))
  let fc : C → β := fun x => f x.val
  have hfc : Topology.IsClosedEmbedding fc :=
    (hf.comp continuous_subtype_val).isClosedEmbedding (hinj.comp Subtype.val_injective)
  have he : f '' (s ∩ C) = fc '' ((↑) ⁻¹' s : Set C) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨⟨x, hx.2⟩, hx.1, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x.val, ⟨hx, x.property⟩, hxy⟩
  rw [he]
  exact hfc.measurableEmbedding.measurableSet_image' (measurable_subtype_coe hs)

lemma latticeOrbitPoint_measurableEmbedding {n : ℕ} (g : G n) (H : Subgroup (G n))
    (hH : IsClosed (H : Set (G n))) : MeasurableEmbedding (latticeOrbitPoint g H) := by
  let : SigmaCompactSpace H := hH.sigmaCompactSpace
  let : SigmaCompactSpace (LatticeOrbitQuotient g H) := by
    apply isSigmaCompact_univ_iff.mp
    have h := isSigmaCompact_range
      (continuous_quotient_mk' : Continuous (fun x : H =>
        (Quotient.mk _ x : LatticeOrbitQuotient g H)))
    change IsSigmaCompact (range (fun x : H =>
      (Quotient.mk _ x : LatticeOrbitQuotient g H))) at h
    rwa [Set.range_eq_univ.mpr Quotient.mk_surjective] at h
  exact measurableEmbedding_of_continuous_injective_sigmaCompact _
    (continuous_latticeOrbitPoint g H) (latticeOrbitPoint_injective g H)

lemma isClosed_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n)) :
    IsClosed (blockMatrixGroup r : Set (G n)) := by
  have he : (blockMatrixGroup r : Set (G n)) =
      ⋂ c : Fin n → ℝ, ⋂ (_hc : c ∈ blockCoordinateAlgebra r),
        {g : G n | slMatrixConjugation g (Matrix.diagonal c) = Matrix.diagonal c} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro _
  apply isClosed_eq _ continuous_const
  unfold slMatrixConjugation
  fun_prop

/-- Pullback through the actual orbit injection recovers the ambient measure
when that measure is concentrated on the orbit. -/
lemma latticeOrbitPoint_map_comap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (hH : IsClosed (H : Set (G n))) (μ : Measure (X n))
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g H)) :
    (μ.comap (latticeOrbitPoint g H)).map (latticeOrbitPoint g H) = μ := by
  rw [(latticeOrbitPoint_measurableEmbedding g H hH).map_comap,
    Measure.restrict_eq_self_of_ae_mem horbit]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MatrixVelocitySpace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual vector space of subgroup velocities

Velocities are derivatives of genuine curves in the subgroup at its
identity. Multiplication adds velocities and a linear reparametrization
scales them. Conjugating the subgroup conjugates this vector space.
No Lie-subgroup or homogeneous-support assertion is assumed here.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma hasDerivAt_matrix_mul_const {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (V B : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, HasDerivAt (fun t => F t i j) (V i j) 0) (i j : Fin n) :
    HasDerivAt (fun t => (F t * B) i j) ((V * B) i j) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun k _ => (hF i k).mul_const (B k j))
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [Matrix.mul_apply, Finset.sum_apply]
  · rfl

private lemma hasDerivAt_const_matrix_mul {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (V B : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, HasDerivAt (fun t => F t i j) (V i j) 0) (i j : Fin n) :
    HasDerivAt (fun t => (B * F t) i j) ((B * V) i j) 0 := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun k _ => (hF k j).const_mul (B i k))
  refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [Matrix.mul_apply, Finset.sum_apply]
  · rfl

lemma HasIdentityMatrixDerivative.conjugate {n : ℕ}
    {γ : ℝ → G n} {V : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasIdentityMatrixDerivative γ V) (a : G n) :
    HasIdentityMatrixDerivative (fun t => a * γ t * a⁻¹)
      (a.val * V * a⁻¹.val) := by
  refine ⟨by simp only [hγ.1, mul_one, mul_inv_cancel], ?_⟩
  intro i j
  have hleft := hasDerivAt_const_matrix_mul (fun t => (γ t).val) V a.val hγ.2
  have hfull := hasDerivAt_matrix_mul_const (fun t => a.val * (γ t).val)
    (a.val * V) a⁻¹.val hleft i j
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using hfull

/-- Conjugation acts on the actual curve-velocity spaces. This is the
covariance needed before applying finite-dimensional recurrence. -/
theorem conjugate_mem_matrixVelocitySpace {n : ℕ}
    (H L : Subgroup (G n)) (a : G n)
    (hconj : ∀ h ∈ H, a * h * a⁻¹ ∈ L)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ matrixVelocitySpace H) :
    a.val * V * a⁻¹.val ∈ matrixVelocitySpace L := by
  obtain ⟨γ, hγ, hd⟩ := hV
  exact ⟨fun t => a * γ t * a⁻¹, fun t => hconj (γ t) (hγ t), hd.conjugate a⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootVelocityRecovery
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recovering an actual root element from a pure root velocity

A curve in a closed subgroup whose velocity is one elementary matrix
produces the corresponding root element by taking growing powers at
reciprocal times. The proof compares those powers with the exact powers
of a transvection. No diagonal normalization of the subgroup is needed.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

lemma hasIdentityMatrixDerivative_rootCurve {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (v : ℝ) :
    HasIdentityMatrixDerivative
      (fun t => Matrix.SpecialLinearGroup.transvection hij (t * v))
      (Matrix.single i j v) := by
  refine ⟨by simp only [zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero], ?_⟩
  intro a b
  have hentry : (fun t =>
      (Matrix.SpecialLinearGroup.transvection hij (t * v)).val a b) =
      fun t => (1 : Matrix (Fin n) (Fin n) ℝ) a b +
        t * (Matrix.single i j v) a b := by
    funext t
    simp only [Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> ring
  rw [hentry]
  convert (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℝ) a b)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const ((Matrix.single i j v) a b)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try (apply Subsingleton.elim)
  · funext t
    rfl
  · simp only [zero_add, one_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_VelocityCommutant
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The commutant of a block-supported actual velocity space

An element of a subgroup always conjugates its own velocity space to
itself. Once that space has the block support found by recurrence and
contains the within-block root directions, its commutant is the block
scalar algebra (when no block is a singleton). This gives the full
normalizer conclusion directly, without assuming that the subgroup is
normalized by the diagonal group or invoking a Lie subgroup theorem.
-/

noncomputable section
open Matrix Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_mem_velocitySpace {n : ℕ}
    (L : Subgroup (G n)) {g : G n} (hg : g ∈ L)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ matrixVelocitySpace L) :
    slMatrixConjugation g V ∈ matrixVelocitySpace L := by
  have hconj : ∀ h ∈ L, g⁻¹ * h * (g⁻¹)⁻¹ ∈ L := by
    intro h hh
    simpa only [inv_inv] using L.mul_mem (L.mul_mem (L.inv_mem hg) hh) hg
  simpa only [slMatrixConjugation, inv_inv] using
    conjugate_mem_matrixVelocitySpace L L g⁻¹ hconj hV

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ActiveBlockProjection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local fixation of a nontrivial block projection

The commutant of the root directions can have a large part on singleton
coordinates. That part does not obstruct local fixation of a nontrivial
block projection: after subtracting the original projection it is an
idempotent tending to zero. A nonzero idempotent has norm at least one.
Thus this local step needs no hypothesis excluding singleton blocks.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Matrix.Norms.Operator Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrix_idempotent_eq_zero_of_norm_lt_one {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M * M = M) (hn : ‖M‖ < 1) : M = 0 := by
  by_contra hne
  have hp : 0 < ‖M‖ := norm_pos_iff.mpr hne
  have hm : ‖M‖ ≤ ‖M‖ * ‖M‖ := by
    calc
      ‖M‖ = ‖M * M‖ := congrArg norm hM.symm
      _ ≤ ‖M‖ * ‖M‖ := norm_mul_le _ _
  nlinarith

lemma matrix_idempotent_eq_of_absorbs {n : ℕ}
    (M P : Matrix (Fin n) (Fin n) ℝ)
    (hM : M * M = M) (hP : P * P = P)
    (hMP : M * P = P) (hPM : P * M = P) (hn : ‖M - P‖ < 1) : M = P := by
  apply sub_eq_zero.mp
  apply matrix_idempotent_eq_zero_of_norm_lt_one _ ?_ hn
  calc
    (M - P) * (M - P) = M * M - M * P - P * M + P * P := by noncomm_ring
    _ = M - P := by rw [hM, hP, hMP, hPM]; abel

lemma commute_single_root_entries {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hM : Commute M (Matrix.single i j (1 : ℝ))) :
    (∀ a, a ≠ i → M a i = 0) ∧
      (∀ b, b ≠ j → M j b = 0) ∧ M i i = M j j := by
  refine ⟨?_, ?_, ?_⟩
  · intro a hai
    have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N a j) hM.eq
    simpa only [Matrix.mul_single_apply_same,
      Matrix.single_mul_apply_of_ne 1 i j a j hai M, mul_one] using he
  · intro b hbj
    have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i b) hM.eq
    simpa only [Matrix.mul_single_apply_of_ne 1 i j i b hbj M,
      Matrix.single_mul_apply_same, one_mul] using he.symm
  · have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) hM.eq
    simpa only [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same,
      mul_one, one_mul] using he

lemma blockProjection_eq_diagonal {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    blockProjection r k = Matrix.diagonal (fun i => if r i k then (1 : ℝ) else 0) := by
  simp only [blockProjection, blockScalarAlgHom_apply, Quotient.eq]

/-- Commutation with the within-block root directions makes the action
on a nontrivial block scalar, even if singleton blocks are present. -/
theorem commutant_mul_nontrivial_blockProjection {n : ℕ}
    (r : Setoid (Fin n)) (k : Fin n) (hk : ∃ l, k ≠ l ∧ r k l)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, i ≠ j → r i j → Commute M (Matrix.single i j (1 : ℝ))) :
    M * blockProjection r k = M k k • blockProjection r k ∧
      blockProjection r k * M = M k k • blockProjection r k := by
  have hpartner (i : Fin n) (hi : r i k) : ∃ j, i ≠ j ∧ r i j := by
    obtain ⟨l, hkl, hrl⟩ := hk
    by_cases hik : i = k
    · subst i; exact ⟨l, hkl, hrl⟩
    · exact ⟨k, hik, hi⟩
  have hrow (i j : Fin n) (hi : r i k) (hij : i ≠ j) : M i j = 0 := by
    obtain ⟨l, hil, hrl⟩ := hpartner i hi
    exact (commute_single_root_entries M l i (hM l i hil.symm (r.symm hrl))).2.1 j hij.symm
  have hcol (i j : Fin n) (hj : r j k) (hij : i ≠ j) : M i j = 0 := by
    obtain ⟨l, hjl, hrl⟩ := hpartner j hj
    exact (commute_single_root_entries M j l (hM j l hjl hrl)).1 i hij
  have hdiag (i : Fin n) (hi : r i k) : M i i = M k k := by
    by_cases hik : i = k
    · subst i; rfl
    · exact (commute_single_root_entries M i k (hM i k hik hi)).2.2
  constructor
  · ext i j
    rw [blockProjection_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : r i k
      · simp only [hi, ite_true, if_true, Matrix.diagonal_apply_eq, smul_eq_mul, mul_one, hdiag i hi]
      · simp only [hi, ite_false, if_false, Matrix.diagonal_apply_eq, smul_eq_mul, mul_zero]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hj : r j k
      · simp only [hj, ite_true, if_true, hcol i j hj hij, mul_one, smul_zero]
      · simp only [hj, ite_false, if_false, mul_zero, smul_zero]
  · ext i j
    rw [blockProjection_eq_diagonal, Matrix.diagonal_mul, Matrix.smul_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : r i k
      · simp only [hi, ite_true, if_true, Matrix.diagonal_apply_eq, smul_eq_mul, mul_one,
          one_mul, hdiag i hi]
      · simp only [hi, ite_false, if_false, Matrix.diagonal_apply_eq, smul_eq_mul, mul_zero, zero_mul]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hi : r i k
      · simp only [hi, ite_true, if_true, hrow i j hi hij, one_mul, smul_zero]
      · simp only [hi, ite_false, if_false, zero_mul, smul_zero]

theorem commutant_idempotent_eq_blockProjection {n : ℕ}
    (r : Setoid (Fin n)) (k : Fin n) (hk : ∃ l, k ≠ l ∧ r k l)
    (M : Matrix (Fin n) (Fin n) ℝ) (hidem : M * M = M)
    (hcomm : ∀ i j, i ≠ j → r i j → Commute M (Matrix.single i j (1 : ℝ)))
    (hkne : M k k ≠ 0) (hn : ‖M - blockProjection r k‖ < 1) :
    M = blockProjection r k := by
  obtain ⟨hMP, hPM⟩ := commutant_mul_nontrivial_blockProjection r k hk M hcomm
  have hPkk : blockProjection r k k k = 1 := by
    rw [blockProjection_eq_diagonal, Matrix.diagonal_apply_eq]
    simp only [r.refl k, ite_true, if_true]
  have hsquare : M k k * M k k = M k k := by
    have he : M * (M * blockProjection r k) = M * blockProjection r k := by
      rw [← Matrix.mul_assoc, hidem]
    rw [hMP, Matrix.mul_smul, hMP, smul_smul] at he
    have hc := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N k k) he
    simpa only [Matrix.smul_apply, smul_eq_mul, hPkk, mul_one] using hc
  have hone : M k k = 1 := by
    apply mul_left_cancel₀ hkne
    simpa only [mul_one] using hsquare
  apply matrix_idempotent_eq_of_absorbs M (blockProjection r k) hidem
    (blockProjection_mul_self r k) ?_ ?_ hn
  · simpa only [hone, one_smul] using hMP
  · simpa only [hone, one_smul] using hPM

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_NormalizerOrbitReduction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From a normalizer orbit to one block orbit

The finite normalizer quotient gives a finite cover by block-group orbits.
Each such orbit is Borel and diagonal invariant. Diagonal ergodicity thus
places the whole measure on one of them. These are direct consequences of
an actual normalizer-orbit support statement, not an assertion that every
root-invariant measure already has that support.
-/

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma latticeOrbitPoint_range_preimage {n : ℕ} (g : G n) (H : Subgroup (G n)) (h : H) :
    (fun x => rightAction x h.val) ⁻¹' range (latticeOrbitPoint g H) =
      range (latticeOrbitPoint g H) := by
  have hmap (a : H) : Set.MapsTo (fun x => rightAction x a.val)
      (range (latticeOrbitPoint g H)) (range (latticeOrbitPoint g H)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨latticeOrbitRightAction g H x a, latticeOrbitPoint_rightAction g H x a⟩
  ext x
  constructor
  · intro hx
    have hi := hmap h⁻¹ hx
    simpa only [Subgroup.coe_inv, rightAction_mul, mul_inv_cancel, rightAction_one] using hi
  · intro hx
    exact hmap h hx

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PairedCoordinateAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational operators scalar on two coordinates

The algebra below consists of concrete real matrices preserving the rational
row space and acting by a common scalar on two specified coordinate
functionals. In prime dimension, the generic-lattice condition forces this
algebra to contain only rational scalar matrices. No diagonal condition is
imposed on the other coordinates. This is the arithmetic form needed when
singleton root blocks are still present.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The generic coordinate functional is faithful on the concrete matrix
algebra: it detects an operator on the rational space, which spans over ℝ. -/
theorem pairedCoordinateEval_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) (i j : Fin n)
    (hzero : ∀ w ∈ W, ∀ k, w k = 0 → w = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤) :
    Function.Injective (pairedCoordinateEval W i j) := by
  intro a b hab
  have heval : a.val.1 = b.val.1 := hab
  let F := Matrix.mulVecLin (a.val.2 - b.val.2)
  have hsub : (W : Set (Fin n → ℝ)) ⊆ F.ker := by
    intro w hw
    have hd : a.val.2 *ᵥ w - b.val.2 *ᵥ w ∈ W :=
      W.sub_mem (a.property.1 w hw) (b.property.1 w hw)
    have hdi : (a.val.2 *ᵥ w - b.val.2 *ᵥ w) i = 0 := by
      simp only [Pi.sub_apply, a.property.2.1, b.property.2.1, heval, sub_self]
    have hz := hzero _ hd i hdi
    change (a.val.2 - b.val.2) *ᵥ w = 0
    simpa only [Matrix.sub_mulVec] using hz
  have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ F.ker := by
    rw [← hspan]
    exact Submodule.span_le.mpr hsub
  apply Subtype.ext
  apply Prod.ext heval
  apply sub_eq_zero.mp
  apply Matrix.mulVec_injective
  funext v
  have hv := hker (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ (Fin n → ℝ)))
  change (a.val.2 - b.val.2) *ᵥ v = 0 at hv
  simpa only [Matrix.zero_mulVec] using hv

theorem pairedCoordinateActionAt_injective {n : ℕ}
    (W : Submodule ℚ (Fin n → ℝ)) (i j : Fin n)
    (hzero : ∀ v ∈ W, ∀ k, v k = 0 → v = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤)
    (w : W) (hw : w ≠ 0) :
    Function.Injective (pairedCoordinateActionAt W i j w) := by
  intro a b hab
  apply pairedCoordinateEval_injective W i j hzero hspan
  have hwi : w.val i ≠ 0 := fun h => hw (Subtype.ext (hzero _ w.property i h))
  have he := congrArg (fun z : W => z.val i) hab
  change (a.val.2 *ᵥ w.val) i = (b.val.2 *ᵥ w.val) i at he
  rw [a.property.2.1, b.property.2.1] at he
  exact mul_right_cancel₀ hwi he

/-- Prime dimension rules out non-scalar operators with two equal coordinate
eigenvalues, even when their action on the remaining coordinates is arbitrary. -/
theorem pairedCoordinateAlgebra_eq_bot {n : ℕ} (hn : n.Prime)
    (W : Submodule ℚ (Fin n → ℝ)) [FiniteDimensional ℚ W]
    (hdim : Module.finrank ℚ W = n)
    (hzero : ∀ v ∈ W, ∀ k, v k = 0 → v = 0)
    (hspan : Submodule.span ℝ (W : Set (Fin n → ℝ)) = ⊤)
    (i j : Fin n) (hij : i ≠ j) : pairedCoordinateAlgebra W i j = ⊥ := by
  let A := pairedCoordinateAlgebra W i j
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [hdim]; exact hn.pos)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have hinj := pairedCoordinateActionAt_injective W i j hzero hspan w hw
  let : FiniteDimensional ℚ A :=
    FiniteDimensional.of_injective (pairedCoordinateActionAt W i j w) hinj
  let : IsDomain A := Function.Injective.isDomain (pairedCoordinateEval W i j)
    (pairedCoordinateEval_injective W i j hzero hspan)
  let algA : Algebra ℚ A := inferInstance
  let : DivisionRing A := divisionRingOfFiniteDimensional ℚ A
  let : Algebra ℚ A := algA
  have hdiv : Module.finrank ℚ A ∣ n := by
    simpa only [hdim] using Module.finrank_dvd_finrank_right ℚ A W
  apply Subalgebra.finrank_eq_one_iff.mp
  rcases (Nat.dvd_prime hn).mp hdiv with h | h
  · exact h
  · have hsurj : Function.Surjective (pairedCoordinateActionAt W i j w) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h.trans hdim.symm)).mp hinj
    let F : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      w.val j • LinearMap.proj i - w.val i • LinearMap.proj j
    have hsub : (W : Set (Fin n → ℝ)) ⊆ F.ker := by
      intro v hv
      obtain ⟨a, ha⟩ := hsurj ⟨v, hv⟩
      have hv' : a.val.2 *ᵥ w.val = v := congrArg Subtype.val ha
      change w.val j * v i - w.val i * v j = 0
      rw [← hv', a.property.2.1, a.property.2.2]
      ring
    have hker : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ F.ker := by
      rw [← hspan]
      exact Submodule.span_le.mpr hsub
    have he := hker (show Pi.single i (1 : ℝ) ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) from trivial)
    have hwj : w.val j ≠ 0 := fun h => hw (Subtype.ext (hzero _ w.property j h))
    exfalso
    apply hwj
    simpa [F, Pi.single_apply, hij, hij.symm] using he

/-- Actual lattice specialization. The rational structure is the row space
of the supplied matrix, not an independent field-action assumption. -/
theorem rationalRowSpace_pairedCoordinateAlgebra_eq_bot {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hzero : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    pairedCoordinateAlgebra (rationalRowSpace g) i j = ⊥ :=
  pairedCoordinateAlgebra_eq_bot hn (rationalRowSpace g)
    (finrank_rationalRowSpace g) (rationalRowSpace_no_coordinate_zero g hzero)
    (real_span_rationalRowSpace g) i j hij

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PairedRootCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The scalar commutant forced by an opposite root pair

The paired-coordinate algebra applies to the rational matrices conjugated
by a lattice representative. The rational structure is
transported through the matrix identity, rather than postulated. A finite
invariant orbit and one opposite root pair then force its rational
stabilizer commutant to consist of scalars.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma transpose_conjugate_rational_preserves_rowSpace {n : ℕ}
    (g : G n) (B : Matrix (Fin n) (Fin n) ℚ) :
    ∀ w ∈ rationalRowSpace g,
      (slMatrixConjugation g (rationalMatrixCast B))ᵀ *ᵥ w ∈ rationalRowSpace g := by
  rintro w ⟨z, rfl⟩
  refine ⟨z ᵥ* B, ?_⟩
  have hg : g.val * g⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hconj : g.val * slMatrixConjugation g (rationalMatrixCast B) =
      rationalMatrixCast B * g.val := by
    simp only [slMatrixConjugation, ← mul_assoc, hg, one_mul]
  have hcast : (fun k => ((z ᵥ* B) k : ℝ)) =
      (fun k => (z k : ℝ)) ᵥ* rationalMatrixCast B := by
    ext k
    simp [Matrix.vecMul, dotProduct, rationalMatrixCast_apply]
  rw [rationalRowMap_apply, Matrix.mulVec_transpose, rationalRowMap_apply, hcast,
    Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul]

lemma transpose_mulVec_coordinate_of_column {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hcol : ∀ a, a ≠ i → M a i = 0) (v : Fin n → ℝ) :
    (Mᵀ *ᵥ v) i = M i i * v i := by
  rw [Matrix.mulVec_transpose]
  change (∑ a, v a * M a i) = _
  rw [Finset.sum_eq_single i]
  · exact mul_comm _ _
  · intro a _ hai
    rw [hcol a hai, mul_zero]
  · simp

lemma equal_diagonal_of_commute_root {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (h : Commute M (Matrix.transvection i j (1 : ℝ))) : M i i = M j j := by
  have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) h.eq
  simp only [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
    one_mul] at he
  exact add_left_cancel he

lemma slMatrixConjugation_smul_one {n : ℕ} (g : G n) (c : ℝ) :
    slMatrixConjugation g (c • (1 : Matrix (Fin n) (Fin n) ℝ)) = c • 1 := by
  simp only [slMatrixConjugation, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

/-- A conjugated rational matrix whose two indicated columns have a common
scalar eigenvalue must itself be a rational scalar matrix. -/
theorem rationalMatrix_scalar_of_opposite_roots {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (B : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) (hij : i ≠ j)
    (hijB : Commute (slMatrixConjugation g (rationalMatrixCast B))
      (Matrix.transvection i j (1 : ℝ)))
    (hjiB : Commute (slMatrixConjugation g (rationalMatrixCast B))
      (Matrix.transvection j i (1 : ℝ))) :
    ∃ q : ℚ, B = q • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  let M := slMatrixConjugation g (rationalMatrixCast B)
  have hcol_i := offColumn_zero_of_commute_root M i j hijB
  have hcol_j := offColumn_zero_of_commute_root M j i hjiB
  have hdiag := equal_diagonal_of_commute_root M i j hijB
  have hmem : (M i i, Mᵀ) ∈ pairedCoordinateAlgebra (rationalRowSpace g) i j := by
    refine ⟨transpose_conjugate_rational_preserves_rowSpace g B, ?_, ?_⟩
    · exact transpose_mulVec_coordinate_of_column M i hcol_i
    · intro v
      rw [transpose_mulVec_coordinate_of_column M j hcol_j, ← hdiag]
  rw [rationalRowSpace_pairedCoordinateAlgebra_eq_bot hn g hgeneric i j hij] at hmem
  obtain ⟨q, hq⟩ := Algebra.mem_bot.mp hmem
  have hmat : M = (q : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have ht : algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q = Mᵀ :=
      congrArg (fun a : ℝ × Matrix (Fin n) (Fin n) ℝ => a.2) hq
    have hscalar : algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q =
        (q : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext a b
      by_cases hab : a = b <;>
        simp [Algebra.algebraMap_eq_smul_one, Rat.smul_def, hab]
    rw [hscalar] at ht
    have ht' := congrArg Matrix.transpose ht
    simpa only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose]
      using ht'.symm
  have hcast : rationalMatrixCast B = (q : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have he := congrArg (slMatrixConjugation g⁻¹) hmat
    have hinverse : slMatrixConjugation g⁻¹ M = rationalMatrixCast B := by
      simpa only [M, inv_inv] using slMatrixConjugation_inverse g⁻¹ (rationalMatrixCast B)
    rw [hinverse, slMatrixConjugation_smul_one] at he
    exact he
  refine ⟨q, ?_⟩
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℚ ℝ)
  change rationalMatrixCast B = rationalMatrixCast (q • (1 : Matrix (Fin n) (Fin n) ℚ))
  rw [hcast]
  ext a b
  by_cases hab : a = b <;> simp [rationalMatrixCast_apply, hab]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ScalarOrbitCommutant
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar real commutants of prime-degree finite root-pair orbits

Rationality of the actual lattice stabilizer's commutant turns the preceding
rational scalar theorem into a real scalar theorem. In particular, no
nontrivial real projection can commute with the orbit group. No orbit
existence is assumed beyond the finite invariant orbit explicitly supplied.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_scalarMatrixSpace_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ scalarMatrixSpace n ↔ ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  constructor
  · rintro ⟨c, hc⟩
    have he : c • (1 : Matrix (Fin n) (Fin n) ℝ) = M := by
      simpa only [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one] using hc
    exact ⟨c, he.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, Algebra.algebraMap_eq_smul_one c⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PairedOrbitSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.compatMatrixBorelSpaceFPF _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.compatMatrixBorelSpacePlucker _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root-invariant finite measures supported on a block orbit

The orbit measure need not be invariant under its entire orbit group.
Only the two opposite root maps preserve it.  Polynomial recurrence is
applied to every rational stabilizer-commutant observable simultaneously;
a generic point then makes that rational commutant scalar.  This reduces
the dynamical target to finding positive mass on a block orbit, rather
than assuming a finite homogeneous invariant measure on that orbit.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma conjugationOrbitMap_map_invariant_element {n : ℕ} (g : G n)
    (L : Subgroup (G n)) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val)
    (μ : Measure (LatticeOrbitQuotient g L)) (h : L)
    (hinv : μ.map (fun x => latticeOrbitRightAction g L x h) = μ) :
    (μ.map (conjugationOrbitMap g L M hM)).map (slMatrixConjugation h.val) =
      μ.map (conjugationOrbitMap g L M hM) := by
  let F := conjugationOrbitMap g L M hM
  have hF : Measurable F := (continuous_conjugationOrbitMap g L M hM).measurable
  calc
    _ = μ.map (slMatrixConjugation h.val ∘ F) :=
      Measure.map_map (continuous_slMatrixConjugation h.val).measurable hF
    _ = μ.map (F ∘ fun x => latticeOrbitRightAction g L x h) := by
      congr 1
      funext x
      exact (conjugationOrbitMap_rightAction g L M hM x h).symm
    _ = (μ.map (fun x => latticeOrbitRightAction g L x h)).map F :=
      (Measure.map_map hF (continuous_latticeOrbitRightAction g L h).measurable).symm
    _ = μ.map F := by rw [hinv]

lemma ae_conjugationOrbitMap_commute_root {n : ℕ}
    (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ]
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L)
    (hinv : μ.map (fun x => latticeOrbitRightAction g L x
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hroot⟩) = μ)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    ∀ᵐ x ∂μ, Commute (conjugationOrbitMap g L M hM x)
      (Matrix.transvection i j (1 : ℝ)) := by
  let F := conjugationOrbitMap g L M hM
  have hF : Measurable F := (continuous_conjugationOrbitMap g L M hM).measurable
  have hr : (μ.map F).map (rootMatrixConjugation i j 1) = μ.map F := by
    rw [← slMatrixConjugation_root i j hij]
    exact conjugationOrbitMap_map_invariant_element g L M hM μ
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hroot⟩ hinv
  exact ae_of_ae_map hF.aemeasurable
    (ae_commute_root_of_conjugation_invariance (μ.map F) i j hij hr)

lemma latticeRational_commutes_pointStabilizer {n : ℕ}
    (g : G n) (L : Subgroup (G n)) (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
    ∀ s : pointOrbitStabilizer g L,
      Commute (slMatrixConjugation g (rationalMatrixCast B)) s.val.val := by
  intro s
  obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g L s
  rw [← hγ]
  exact ((commute_rationalMatrixCast_iff B (latticeStabilizerMatrix g L γ)).mpr
    ((mem_commutatorFamily_ker _ _).mp hB γ)).map (slMatrixConjugationHom g)

/-- Full orbit-group invariance is unnecessary: recurrence for the two
root maps and genericity almost everywhere suffice to make the actual
integral-stabilizer commutant scalar. -/
theorem realStabilizer_scalar_of_root_pair_measure {n : ℕ}
    (hn : n.Prime) (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L)
    (hopposite : Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ) ∈ L)
    (hinv : μ.map (fun x => latticeOrbitRightAction g L x
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hroot⟩) = μ)
    (hopinv : μ.map (fun x => latticeOrbitRightAction g L x
      ⟨Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ), hopposite⟩) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice (latticeOrbitPoint g L x),
      v ≠ 0 → ∀ k, v k ≠ 0)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let : Encodable ℚ := Encodable.ofCountable ℚ
  let : Encodable (Matrix (Fin n) (Fin n) ℚ) :=
    inferInstanceAs (Encodable (Fin n → Fin n → ℚ))
  have hae (B : Matrix (Fin n) (Fin n) ℚ) : ∀ᵐ x ∂μ,
      ∀ hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker,
        Commute (conjugationOrbitMap g L (slMatrixConjugation g (rationalMatrixCast B))
          (latticeRational_commutes_pointStabilizer g L B hB) x)
            (Matrix.transvection i j (1 : ℝ)) ∧
        Commute (conjugationOrbitMap g L (slMatrixConjugation g (rationalMatrixCast B))
          (latticeRational_commutes_pointStabilizer g L B hB) x)
            (Matrix.transvection j i (1 : ℝ)) := by
    by_cases hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker
    · filter_upwards [ae_conjugationOrbitMap_commute_root g L μ i j hij hroot hinv
          _ (latticeRational_commutes_pointStabilizer g L B hB),
        ae_conjugationOrbitMap_commute_root g L μ j i hij.symm hopposite hopinv
          _ (latticeRational_commutes_pointStabilizer g L B hB)] with x hx hy
      intro _
      exact ⟨hx, hy⟩
    · exact Eventually.of_forall fun _ h => (hB h).elim
  have : NeBot (ae μ) := ae_neBot.mpr hμ
  obtain ⟨x, hx, hxgeneric⟩ := ((ae_all_iff.mpr hae).and hgeneric).exists
  have hscalar (B : Matrix (Fin n) (Fin n) ℚ)
      (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
      ∃ q : ℚ, B = q • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    have hxB := hx B hB
    induction x using Quotient.inductionOn with
    | h b =>
      have hg : ∀ v ∈ rowLattice (g * b.val).val, v ≠ 0 → ∀ k, v k ≠ 0 := hxgeneric
      have hpair : Commute (slMatrixConjugation (g * b.val) (rationalMatrixCast B))
          (Matrix.transvection i j (1 : ℝ)) ∧
          Commute (slMatrixConjugation (g * b.val) (rationalMatrixCast B))
            (Matrix.transvection j i (1 : ℝ)) := by
        change Commute (slMatrixConjugation b.val
            (slMatrixConjugation g (rationalMatrixCast B))) _ ∧
          Commute (slMatrixConjugation b.val
            (slMatrixConjugation g (rationalMatrixCast B))) _ at hxB
        simpa only [← slMatrixConjugation_mul] using hxB
      exact rationalMatrix_scalar_of_opposite_roots hn (g * b.val) hg B i j hij
        hpair.1 hpair.2
  apply (mem_scalarMatrixSpace_iff M).mp
  rw [latticeStabilizer_commutant_rational] at hM
  apply (Submodule.span_le.mpr ?_) hM
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨q, rfl⟩ := hscalar B hB
  apply (mem_scalarMatrixSpace_iff _).mpr
  refine ⟨(q : ℝ), ?_⟩
  change (q • (1 : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ) = _
  ext a b
  by_cases hab : a = b <;> simp [hab]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockOrbitMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive mass on a block orbit already gives the prime-degree obstruction

The finite measure is assumed invariant only under the chosen opposite
root pair.  Restricting it to one positive block orbit preserves those
two maps.  The rational commutant argument therefore rules out every
proper block partition, without full invariance under the block group.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma transvection_neg_one_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (i j : Fin n) (hij : i ≠ j) (hr : r i j) :
    Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ blockMatrixGroup r := by
  simpa only [Matrix.SpecialLinearGroup.transvection_inv] using
    (blockMatrixGroup r).inv_mem (transvection_mem_blockMatrixGroup r i j hij hr)

lemma latticeOrbitPoint_comap_invariant_element {n : ℕ}
    (g : G n) (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (μ : Measure (X n)) (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g L))
    (h : L) (hinv : μ.map (fun x => rightAction x h.val) = μ) :
    (μ.comap (latticeOrbitPoint g L)).map
      (fun x => latticeOrbitRightAction g L x h) = μ.comap (latticeOrbitPoint g L) := by
  let F := latticeOrbitPoint g L
  let R := fun x => latticeOrbitRightAction g L x h
  have hF := latticeOrbitPoint_measurableEmbedding g L hL
  have hmap := latticeOrbitPoint_map_comap g L hL μ horbit
  apply hF.map_injective
  calc
    _ = (μ.comap F).map (F ∘ R) :=
      Measure.map_map hF.measurable (continuous_latticeOrbitRightAction g L h).measurable
    _ = (μ.comap F).map ((fun x => rightAction x h.val) ∘ F) := by
      congr 1
      funext x
      exact latticeOrbitPoint_rightAction g L x h
    _ = ((μ.comap F).map F).map (fun x => rightAction x h.val) :=
      (Measure.map_map (continuous_rightAction h.val).measurable hF.measurable).symm
    _ = μ := by rw [hmap, hinv]
    _ = (μ.comap F).map F := hmap.symm

theorem partition_universal_of_root_pair_supported_on_block_orbit {n : ℕ}
    (hn : n.Prime) (g : G n) (r : Setoid (Fin n))
    (i j : Fin n) (hij : i ≠ j) (hr : r i j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (horbit : ∀ᵐ x ∂μ, x ∈ range (latticeOrbitPoint g (blockMatrixGroup r)))
    (hinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ))) = μ)
    (hopinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ))) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0) :
    ∀ a b, r a b := by
  let L := blockMatrixGroup r
  have hL : IsClosed (L : Set (G n)) := isClosed_blockMatrixGroup r
  let ν := μ.comap (latticeOrbitPoint g L)
  have hmap : ν.map (latticeOrbitPoint g L) = μ :=
    latticeOrbitPoint_map_comap g L hL μ horbit
  have hν : ν ≠ 0 := by
    intro hzero
    rw [hzero, Measure.map_zero] at hmap
    exact hμ hmap.symm
  have hroot : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L :=
    transvection_neg_one_mem_blockMatrixGroup r i j hij hr
  have hopposite : Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ) ∈ L :=
    transvection_neg_one_mem_blockMatrixGroup r j i hij.symm (r.symm hr)
  have hνgeneric : ∀ᵐ x ∂ν, ∀ v ∈ pointLattice (latticeOrbitPoint g L x),
      v ≠ 0 → ∀ k, v k ≠ 0 :=
    ae_of_ae_map (continuous_latticeOrbitPoint g L).measurable.aemeasurable
      (by rwa [hmap])
  have hscalar (M : Matrix (Fin n) (Fin n) ℝ)
      (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
      ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    obtain ⟨c, hc⟩ := realStabilizer_scalar_of_root_pair_measure hn g L ν hν
      i j hij hroot hopposite
      (latticeOrbitPoint_comap_invariant_element g L hL μ horbit ⟨_, hroot⟩ hinv)
      (latticeOrbitPoint_comap_invariant_element g L hL μ horbit ⟨_, hopposite⟩ hopinv)
      hνgeneric (slMatrixConjugation g⁻¹ M)
      (inverseConjugate_mem_realStabilizer g L M hM)
    refine ⟨c, ?_⟩
    have he := congrArg (slMatrixConjugation g) hc
    rwa [slMatrixConjugation_inverse, slMatrixConjugation_smul_one] at he
  intro a b
  by_contra hab
  let c : Fin n → ℝ := fun k => if r k a then 1 else 0
  have hc : c ∈ blockCoordinateAlgebra r := by
    intro k l hkl
    have he : r k a ↔ r l a :=
      ⟨fun h => r.trans (r.symm hkl) h, fun h => r.trans hkl h⟩
    simp only [c, he]
  have hM : ∀ s : pointOrbitStabilizer g L, Commute (Matrix.diagonal c) s.val.val :=
    fun s => blockMatrixGroup_commute r s.val c hc
  obtain ⟨t, ht⟩ := hscalar (Matrix.diagonal c) hM
  have ha := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a a) ht
  have hb := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M b b) ht
  have hba : ¬r b a := fun h => hab (r.symm h)
  simp only [Matrix.diagonal_apply_eq, c, r.refl a, ite_true, if_true,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at ha
  simp only [Matrix.diagonal_apply_eq, c, hba, ite_false, if_false,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hb
  exact zero_ne_one (hb.trans ha.symm)

/-- Positive mass, not full support, suffices. The root pair must belong
to the same proposed block, so restriction to that orbit remains invariant. -/
theorem partition_universal_of_positive_block_orbit_mass {n : ℕ}
    (hn : n.Prime) (g : G n) (r : Setoid (Fin n))
    (i j : Fin n) (hij : i ≠ j) (hr : r i j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hpos : μ (range (latticeOrbitPoint g (blockMatrixGroup r))) ≠ 0)
    (hinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ))) = μ)
    (hopinv : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ))) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ k, v k ≠ 0) :
    ∀ a b, r a b := by
  let L := blockMatrixGroup r
  let E := range (latticeOrbitPoint g L)
  have hL : IsClosed (L : Set (G n)) := isClosed_blockMatrixGroup r
  have hE : MeasurableSet E := (latticeOrbitPoint_measurableEmbedding g L hL).measurableSet_range
  have hν : μ.restrict E ≠ 0 := mt Measure.restrict_eq_zero.mp hpos
  have hrestrict (h : L) (hh : μ.map (fun x => rightAction x h.val) = μ) :
      (μ.restrict E).map (fun x => rightAction x h.val) = μ.restrict E := by
    have he := Measure.restrict_map (μ := μ) (continuous_rightAction h.val).measurable hE
    rw [hh, latticeOrbitPoint_range_preimage g L h] at he
    exact he.symm
  exact partition_universal_of_root_pair_supported_on_block_orbit hn g r i j hij hr
    (μ.restrict E) hν (ae_restrict_mem hE)
    (hrestrict ⟨_, transvection_neg_one_mem_blockMatrixGroup r i j hij hr⟩ hinv)
    (hrestrict ⟨_, transvection_neg_one_mem_blockMatrixGroup r j i hij.symm (r.symm hr)⟩ hopinv)
    (ae_restrict_of_ae hgeneric)

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_DenseInvariantFunctions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Almost invariance extends from a dense subgroup

Continuity of the actual pullback representation on lattice L² extends
almost invariance of an observable from a dense subgroup. This does not
turn pointwise invariance into a topological assertion about a measurable
observable; the continuous object is its L² equivalence class.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_function_ae_fixed_of_dense
    {n : ℕ} (H : Subgroup (G n))
    {S : Type*} [Group S] (φ : S →* H) (hdense : DenseRange φ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (f : X n → ℝ) (hf : MemLp f 2 μ)
    (hfix : ∀ s : S, (fun x : X n => f (φ s • x)) =ᵐ[μ] f) :
    ∀ h : H, (fun x : X n => f (h • x)) =ᵐ[μ] f := by
  let : SMulInvariantMeasure H (X n) μ :=
    ⟨fun h B hB => (latticeSubgroup_preserving H μ hH h).measure_preimage
      hB.nullMeasurableSet⟩
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let F : Lp ℝ 2 μ := hf.toLp f
  have hF : (F : X n → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  have hrep (h : H) : (DomMulAct.mk h • F : Lp ℝ 2 μ) =ᵐ[μ]
      (fun x : X n => f (h • x)) := by
    exact (DomMulAct.smul_Lp_ae_eq (DomMulAct.mk h) F).trans
      ((latticeSubgroup_preserving H μ hH h).quasiMeasurePreserving.ae_eq_comp hF)
  have hcont : Continuous (fun h : H => (DomMulAct.mk h • F : Lp ℝ 2 μ)) :=
    DomMulAct.continuous_mk.smul continuous_const
  have hfull (h : H) : (DomMulAct.mk h • F : Lp ℝ 2 μ) = F := by
    exact hdense.induction_on h (isClosed_eq hcont continuous_const)
      (fun s => Lp.ext (((hrep (φ s)).trans (hfix s)).trans hF.symm))
  intro h
  have he := hrep h
  rw [hfull h] at he
  exact he.symm.trans hF

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ExactInvariantSets
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact representatives of invariant measurable sets

An almost invariant set has an exactly invariant representative when
the acting group carries a nonzero finite measure in a translation
invariant measure class. Haar measure supplies such a finite measure.
This is the measure-class step needed to compare the full invariant
sigma algebra with a countable dense subgroup's invariant sigma algebra.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ENNReal

namespace DukePrimeDegree

section MeasurableAction

variable {H Y : Type*} [Group H] [MeasurableSpace H]
  [MeasurableSpace Y] [MulAction H Y]

/-- A finite measure equivalent to a left Haar measure has a measure
class invariant under every right translation. -/
theorem exists_finite_right_quasiInvariant_measure
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0) :
    ∃ ρ : Measure H, IsFiniteMeasure ρ ∧ ρ ≠ 0 ∧
      ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ := by
  obtain ⟨ρ, hfin, hhaarρ, hρhaar⟩ := exists_isFiniteMeasure_absolutelyContinuous haar
  refine ⟨ρ, hfin, ?_, ?_⟩
  · intro hzero
    apply hhaar
    apply Measure.measure_univ_eq_zero.mp
    exact hhaarρ (by rw [hzero]; simp)
  · intro g
    exact (quasiMeasurePreserving_mul_right haar g).mono hρhaar hhaarρ

end MeasurableAction
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ExactInvariantFunctions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Pointwise invariant versions under a Haar measure class

The version is formed by averaging only on orbits where the observable
is almost everywhere constant. Those orbits form an exactly invariant
measurable set. This avoids an intersection of uncountably many conull
sets and does not assume amenability of the acting group.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped ENNReal

namespace DukePrimeDegree

variable {H Y : Type*} [Group H] [MeasurableSpace H]
  [MeasurableSpace Y] [MulAction H Y]

lemma measurable_orbitConstantMean
    (ρ : Measure H) [SFinite ρ]
    (hsmul : Measurable (fun p : Y × H => p.2 • p.1))
    (f : Y → ℝ) (hf : Measurable f) :
    Measurable (orbitConstantMean ρ f) :=
  ((hf.comp hsmul).stronglyMeasurable.integral_prod_right').measurable

lemma measurableSet_orbitConstantSet
    (ρ : Measure H) [SFinite ρ]
    (hsmul : Measurable (fun p : Y × H => p.2 • p.1))
    (f : Y → ℝ) (hf : Measurable f) :
    MeasurableSet (orbitConstantSet ρ f) := by
  have hm := measurable_orbitConstantMean ρ hsmul f hf
  have hbad : MeasurableSet {p : Y × H |
      f (p.2 • p.1) ≠ orbitConstantMean ρ f p.1} :=
    (measurableSet_eq_fun (hf.comp hsmul) (hm.comp measurable_fst)).compl
  have hmass := measurable_measure_prodMk_left (ν := ρ) hbad
  have heq : orbitConstantSet ρ f =
      {x : Y | ρ {h : H | f (h • x) ≠ orbitConstantMean ρ f x} = 0} := by
    ext x
    exact ae_iff
  rw [heq]
  exact measurableSet_eq_fun hmass measurable_const

omit [MeasurableSpace Y] in
lemma orbitConstantMean_smul_of_mem
    (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (f : Y → ℝ) {x : Y} (hx : x ∈ orbitConstantSet ρ f) (g : H) :
    orbitConstantMean ρ f (g • x) = orbitConstantMean ρ f x := by
  apply integral_eq_const
  simpa only [mul_smul] using (hρ g).ae hx

omit [MeasurableSpace Y] in
lemma smul_mem_orbitConstantSet
    (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (f : Y → ℝ) (x : Y) (g : H) :
    g • x ∈ orbitConstantSet ρ f ↔ x ∈ orbitConstantSet ρ f := by
  have himp (y : Y) (a : H) (hy : y ∈ orbitConstantSet ρ f) :
      a • y ∈ orbitConstantSet ρ f := by
    have hmean := orbitConstantMean_smul_of_mem ρ hρ f hy a
    change ∀ᵐ h ∂ρ, f (h • (a • y)) = orbitConstantMean ρ f (a • y)
    rw [hmean]
    simpa only [mul_smul] using (hρ a).ae hy
  exact ⟨fun hx => by simpa only [inv_smul_smul] using himp (g • x) g⁻¹ hx,
    himp x g⟩

/-- A probability in a right-translation invariant measure class gives
an exactly invariant measurable version of an almost invariant real
observable. The observable need not be globally bounded. -/
theorem exists_pointwise_invariant_version_of_probability_class
    (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ)
    (μ : Measure Y) [SFinite μ]
    (hsmul : Measurable (fun p : H × Y => p.1 • p.2))
    (f : Y → ℝ) (hf : Measurable f)
    (hfix : ∀ h : H, (fun x : Y => f (h • x)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[PrimeDegreePackets.actionInvariantSigma H Y] f₀ ∧
      f₀ =ᵐ[μ] f ∧ ∀ (h : H) (x : Y), f₀ (h • x) = f₀ x := by
  let E := orbitConstantSet ρ f
  let c := orbitConstantMean ρ f
  let f₀ := E.indicator c
  have hc : Measurable c := measurable_orbitConstantMean ρ
    (hsmul.comp measurable_swap) f hf
  have hE : MeasurableSet E := measurableSet_orbitConstantSet ρ
    (hsmul.comp measurable_swap) f hf
  have hfixed (h : H) (x : Y) : f₀ (h • x) = f₀ x := by
    by_cases hx : x ∈ E
    · have hhx : h • x ∈ E := (smul_mem_orbitConstantSet ρ hρ f x h).mpr hx
      simpa only [f₀, Set.indicator_of_mem hx, Set.indicator_of_mem hhx] using
        orbitConstantMean_smul_of_mem ρ hρ f hx h
    · have hhx : h • x ∉ E := fun hh => hx ((smul_mem_orbitConstantSet ρ hρ f x h).mp hh)
      simp only [f₀, Set.indicator_of_notMem hx, Set.indicator_of_notMem hhx]
  refine ⟨f₀, PrimeDegreePackets.measurable_actionInvariantSigma
    (hc.indicator hE) hfixed, ?_, hfixed⟩
  have hmeas : MeasurableSet {p : H × Y | f (p.1 • p.2) = f p.2} :=
    measurableSet_eq_fun (hf.comp hsmul) (hf.comp measurable_snd)
  have hboth : ∀ᵐ x ∂μ, ∀ᵐ h ∂ρ, f (h • x) = f x :=
    (Measure.ae_ae_comm hmeas).mp (Eventually.of_forall hfix)
  filter_upwards [hboth] with x hx
  have hcx : c x = f x := integral_eq_const hx
  have hxE : x ∈ E := by
    change ∀ᵐ h ∂ρ, f (h • x) = c x
    rwa [hcx]
  simpa only [f₀, Set.indicator_of_mem hxE] using hcx

/-- Normalize the finite measure previously constructed from Haar.
This is an actual probability measure, not a probability input. -/
theorem exists_probability_right_quasiInvariant_measure
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0) :
    ∃ ρ : Measure H, IsProbabilityMeasure ρ ∧
      ∀ g : H, QuasiMeasurePreserving (fun h : H => h * g) ρ ρ := by
  obtain ⟨ν, hfin, hν, hright⟩ := exists_finite_right_quasiInvariant_measure haar hhaar
  let : IsFiniteMeasure ν := hfin
  let c : ℝ≥0∞ := (ν Set.univ)⁻¹
  refine ⟨c • ν, ⟨?_⟩, fun g => (hright g).smul_measure c⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)

theorem exists_pointwise_invariant_version_of_haar
    [MeasurableMul₂ H] [MeasurableInv H] (haar : Measure H) [SFinite haar]
    [haar.IsMulLeftInvariant] (hhaar : haar ≠ 0)
    (μ : Measure Y) [SFinite μ]
    (hsmul : Measurable (fun p : H × Y => p.1 • p.2))
    (f : Y → ℝ) (hf : Measurable f)
    (hfix : ∀ h : H, (fun x : Y => f (h • x)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[PrimeDegreePackets.actionInvariantSigma H Y] f₀ ∧
      f₀ =ᵐ[μ] f ∧ ∀ (h : H) (x : Y), f₀ (h • x) = f₀ x := by
  obtain ⟨ρ, hprob, hright⟩ := exists_probability_right_quasiInvariant_measure haar hhaar
  let : IsProbabilityMeasure ρ := hprob
  exact exists_pointwise_invariant_version_of_probability_class ρ hright μ hsmul f hf hfix

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_InvariantMeasureGroup
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The closed group preserving a finite measure

The ambient measure stabilizer is closed. Consequently the topological
closure of the invariant root-generated group still preserves the measure.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace PrimeDegreePackets

lemma continuous_integral_rightAction {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (f : CompactlySupportedContinuousMap (X n) ℝ) : Continuous (fun g : G n => ∫ x, f (rightAction x g) ∂μ) := by
  apply continuous_of_dominated
    (bound := fun _ => ‖f.toBoundedContinuousFunction‖)
  · intro g
    exact (f.continuous.comp (continuous_rightAction g)).aestronglyMeasurable
  · intro g
    exact Eventually.of_forall fun x => f.toBoundedContinuousFunction.norm_coe_le_norm _
  · exact integrable_const _
  · apply Eventually.of_forall
    intro x
    apply f.continuous.comp
    induction x using Quotient.inductionOn with
    | h g =>
      exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

lemma invariantRightSubgroup_eq_tests {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    (invariantRightSubgroup μ : Set (G n)) =
      ⋂ f : CompactlySupportedContinuousMap (X n) ℝ, {g | (∫ x, f (rightAction x g) ∂μ) = ∫ x, f x ∂μ} := by
  ext g
  simp only [mem_iInter, mem_ofPred_eq]
  constructor
  · intro hg f
    change μ.map (fun x => rightAction x g) = μ at hg
    have he := integral_map (μ := μ) (φ := fun x => rightAction x g)
      (f := fun x => f x) (continuous_rightAction g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable
    rw [hg] at he
    exact he.symm
  · intro hg
    change μ.map (fun x => rightAction x g) = μ
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := μ) (f := fun x => f x)
      (continuous_rightAction g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact hg f

/-- The stabilizer of a finite measure is a closed subgroup of the real
special linear group. -/
theorem isClosed_invariantRightSubgroup {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    IsClosed (invariantRightSubgroup μ : Set (G n)) := by
  rw [invariantRightSubgroup_eq_tests]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_rightAction μ f) continuous_const

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_LatticeInvariantVersions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact invariant versions for a matrix subgroup

The subgroup itself need not be closed. Its closure preserves the
measure and fixes the same L² vectors. Haar averaging on that closed
subgroup produces a version measurable for the original subgroup's
exact invariant sigma algebra.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_pointwise_invariant_version
    {n : ℕ} (H : Subgroup (G n))
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ)
    (f : X n → ℝ) (hf : Measurable f) (hfLp : MemLp f 2 μ)
    (hfix : ∀ h : H, (fun x : X n => f (h • x)) =ᵐ[μ] f) :
    ∃ f₀ : X n → ℝ, Measurable[actionInvariantSigma H (X n)] f₀ ∧
      f₀ =ᵐ[μ] f ∧ ∀ (h : H) (x : X n), f₀ (h • x) = f₀ x := by
  let K := H.topologicalClosure
  have hK : K ≤ invariantRightSubgroup μ :=
    H.topologicalClosure_minimal hH (isClosed_invariantRightSubgroup μ)
  let φ : H →* K := H.inclusion H.le_topologicalClosure
  have hdφ : DenseRange φ := by
    exact (denseRange_inclusion_iff H.le_topologicalClosure).mpr subset_rfl
  have hfixK : ∀ k : K, (fun x : X n => f (k • x)) =ᵐ[μ] f :=
    lattice_function_ae_fixed_of_dense K φ hdφ μ hK f hfLp hfix
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : SecondCountableTopology K :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace K := H.isClosed_topologicalClosure.locallyCompactSpace
  obtain ⟨f₀, hf₀, heq, hpoint⟩ := exists_pointwise_invariant_version_of_haar
    (Measure.haar : Measure K) (NeZero.ne _) μ continuous_smul.measurable f hf hfixK
  have hmeas : Measurable f₀ :=
    hf₀.mono (actionInvariantSigma_le K (X n)) le_rfl
  have hpointH (h : H) (x : X n) : f₀ (h • x) = f₀ x := hpoint (φ h) x
  exact ⟨f₀, measurable_actionInvariantSigma hmeas hpointH, heq, hpointH⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CanonicalSubgroupComponents
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ergodic components over the full subgroup's invariant sigma algebra

The orbit averages come from a countable dense subgroup. Their L²
limits extend to the full group and have exactly invariant measurable
versions. Consequently the full invariant sigma conditional kernel,
the same kernel used by diagonal covariance, has ergodic components.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lattice_canonical_subgroup_ergodic_decomposition
    {n : ℕ} (H : Subgroup (G n))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hH : H ≤ invariantRightSubgroup μ) :
    condExpKernel μ (actionInvariantSigma H (X n)) ∘ₘ
        μ.trim (actionInvariantSigma_le H (X n)) = μ ∧
      ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
        ErgodicSMul H (X n) (condExpKernel μ (actionInvariantSigma H (X n)) z) := by
  classical
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense H
  let : Countable s := hs.to_subtype
  let S := FreeGroup s
  let φ : S →* H := FreeGroup.lift (fun a : s => (a : H))
  have hdφ : DenseRange φ := hd.mono (by
    intro h hh
    exact ⟨FreeGroup.of ⟨h, hh⟩, FreeGroup.lift_apply_of⟩)
  let : MulAction S (X n) := MulAction.compHom (X n) φ
  have hpS (a : S) : MeasurePreserving (fun x : X n => a • x) μ μ :=
    latticeSubgroup_preserving H μ hH (φ a)
  let m := actionInvariantSigma H (X n)
  let : MeasurableSpace (X n) := xMeasurableSpace n
  have hm : m ≤ xMeasurableSpace n := actionInvariantSigma_le H (X n)
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdec := invariant_kernel_decomposition m μ
    (fun a : S => fun x : X n => a • x) hpS hm (fun a => iInf_le _ (φ a))
  refine ⟨hdec.1, ?_⟩
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet (X n))
  have hCcount : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  let : Countable C := hCcount.to_subtype
  have hCgen : xMeasurableSpace n = MeasurableSpace.generateFrom C := by
    simp only [C, generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
    rfl
  have hCpi : IsPiSystem C := fun _ hA _ hB _ =>
    isSetAlgebra_generateSetAlgebra.inter_mem hA hB
  have hCm (B : C) : MeasurableSet (B : Set (X n)) := by
    change @MeasurableSet (X n) (xMeasurableSpace n) _
    rw [hCgen]
    exact MeasurableSpace.measurableSet_generateFrom B.property
  have hAv (B : C) := exists_invariant_orbit_average_limit μ hpS
    ((memLp_const (1 : ℝ)).indicator (hCm B) :
      MemLp ((B : Set (X n)).indicator (fun _ => (1 : ℝ))) 2 μ)
  choose v hv hvfix F hF hlim using hAv
  have hvLp (B : C) : MemLp (v B) 2 μ := by
    have hb : ∀ᵐ y ∂μ, v B y ∈ Icc (0 : ℝ) 1 := by
      filter_upwards [hlim B] with y hy
      apply isClosed_Icc.mem_of_tendsto hy
      exact Eventually.of_forall fun k => orbitConvexHull_interval
        (fun x => by by_cases hx : x ∈ (B : Set (X n)) <;> simp [hx]) (hF B k) y
    exact memLp_of_bounded hb
      ((hv B).mono (actionInvariantSigma_le S (X n)) le_rfl).aestronglyMeasurable 2
  have hversions (B : C) : ∃ w : X n → ℝ, Measurable[m] w ∧ w =ᵐ[μ] v B := by
    have hfull := lattice_function_ae_fixed_of_dense H φ hdφ μ hH (v B) (hvLp B)
      (fun a => Eventually.of_forall (hvfix B a))
    obtain ⟨w, hw, heq, _⟩ := lattice_pointwise_invariant_version H μ hH (v B)
      ((hv B).mono (actionInvariantSigma_le S (X n)) le_rfl) (hvLp B) hfull
    exact ⟨w, hw, heq⟩
  choose w hw hweq using hversions
  have hlimw (B : C) : ∀ᵐ y ∂μ,
      Tendsto (fun k => F B k y) atTop (𝓝 (w B y)) := by
    filter_upwards [hlim B, hweq B] with y hy he
    rwa [he]
  have hlimfiber (B : C) : ∀ᵐ z ∂τ, ∀ᵐ y ∂κ z,
      Tendsto (fun k => F B k y) atTop (𝓝 (w B y)) := by
    apply Measure.ae_ae_of_ae_comp
    change ∀ᵐ y ∂κ ∘ₘ τ, Tendsto (fun k => F B k y) atTop (𝓝 (w B y))
    rw [show κ ∘ₘ τ = μ from hdec.1]
    exact hlimw B
  have hconst (B : C) : ∀ᵐ z ∂τ, ∀ᵐ y ∂κ z, w B y = w B z :=
    condExpKernel_ae_constant m μ hm (hw B)
  filter_upwards [hdec.2, ae_all_iff.mpr hlimfiber, ae_all_iff.mpr hconst]
    with z hz hzl hzc
  have hpSz (a : S) : MeasurePreserving (fun y : X n => a • y) (κ z) (κ z) :=
    ⟨(hpS a).measurable, hz a⟩
  have hSerg : ErgodicSMul S (X n) (κ z) := by
    apply ergodicSMul_of_orbit_indicator_limits (κ z) hpSz C hCgen hCpi
    intro B hB
    refine ⟨w ⟨B, hB⟩ z, F ⟨B, hB⟩, hF ⟨B, hB⟩, ?_⟩
    filter_upwards [hzl ⟨B, hB⟩, hzc ⟨B, hB⟩] with y hy hwy
    simpa only [hwy] using hy
  let : ErgodicSMul S (X n) (κ z) := hSerg
  have hpHz (h : H) : MeasurePreserving (fun y : X n => h • y) (κ z) (κ z) :=
    preserving_of_dense_action φ hdφ (κ z) hpSz h
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro h B hB
    exact (hpHz h).measure_preimage hB.nullMeasurableSet
  · intro B hB hfix
    apply ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := S) hB
    intro a
    exact hfix (φ a)

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ComponentRootPattern
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The measurable root pattern of actual ergodic components

A split diagonal rescales each real root group by a nonzero scalar.
Thus it preserves the predicate that the whole root group fixes a
measure, even when it moves that measure. For the normalizer-covariant
component kernel this gives an invariant measurable event on the
component base; it does not assert that individual components are fixed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootInvarianceRelation_iff_full_root {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n)) :
    rootInvarianceRelation μ i j ↔ ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
  constructor
  · rintro (he | ⟨_, hroot⟩)
    · exact (hij he).elim
    · exact hroot
  · exact fun hroot => Or.inr ⟨hij, hroot⟩

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

/-- The same block component can be transported by the actual diagonal
action. This concerns covariance of components, not invariance of each
individual component. -/
theorem diagonal_normalizes_singleBlockRootGroup {n : ℕ}
    (S : Set (Fin n)) (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter ell hell t ∈
      Subgroup.normalizer (singleBlockRootGroup S : Set (G n)) := by
  let U : Set (G n) := {g | ∃ (i j : Fin n) (hij : i ≠ j) (a : ℝ),
    i ∈ S ∧ j ∈ S ∧ g = Matrix.SpecialLinearGroup.transvection hij a}
  have hconj (s : ℝ) {g : G n} (hg : g ∈ U) :
      diagonalOneParameter ell hell s * g * diagonalOneParameter ell hell (-s) ∈ U := by
    obtain ⟨i, j, hij, a, hi, hj, rfl⟩ := hg
    exact ⟨i, j, hij, Real.exp ((ell i - ell j) * s) * a, hi, hj,
      diagonal_conjugation_transvection ell hell hij a s⟩
  apply Subgroup.normalizer_le_normalizer_closure U
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  apply subset_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    simpa only [MulAut.conj_apply, ← diagonalOneParameter_neg] using hconj t hg
  · intro g hg
    refine ⟨(MulAut.conj (diagonalOneParameter ell hell t)).symm g, ?_,
      (MulAut.conj (diagonalOneParameter ell hell t)).apply_symm_apply g⟩
    simpa only [MulAut.conj_symm_apply, ← diagonalOneParameter_neg, neg_neg] using hconj (-t) hg

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transverse representatives using only a single root block

On an ergodic component for a single root block, an arbitrary ambient
diagonal correction need not preserve the component measure.  Here the
correction is a product of roots in that block.  It clears the entries
inside the block and equalizes its diagonal, leaving the complementary
coordinates unrestricted.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] singleBlockRootGroup

lemma singleBlockSetoid_off_diagonal {n : ℕ} (S : Set (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    singleBlockSetoid S i j ↔ i ∈ S ∧ j ∈ S := by
  change (i = j ∨ (i ∈ S ∧ j ∈ S)) ↔ _
  simp only [hij, false_or]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockProjection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local preservation of one nontrivial root block

The other root blocks need not preserve the component measure. Only
the roots in the selected block and the vanishing of velocity entries
crossing its boundary are used. This is the local stabilizer statement
needed on a single-block ergodic component.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Operator Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma blockProjection_singleBlock_eq {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S) :
    blockProjection (singleBlockSetoid S) k =
      Matrix.diagonal (fun i => if i ∈ S then (1 : ℝ) else 0) := by
  rw [blockProjection_eq_diagonal]
  congr 1
  funext i
  have he : singleBlockSetoid S i k ↔ i ∈ S := by
    change (i = k ∨ i ∈ S ∧ k ∈ S) ↔ i ∈ S
    constructor
    · rintro (rfl | hi)
      · exact hk
      · exact hi.1
    · exact fun hi => Or.inr ⟨hi, hk⟩
  simp only [he]

lemma commute_singleBlockProjection_of_cross_zero {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : ∀ i j, ¬(i ∈ S ↔ j ∈ S) → V i j = 0) :
    Commute (blockProjection (singleBlockSetoid S) k) V := by
  change _ * V = V * _
  rw [blockProjection_singleBlock_eq S k hk]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp only [hi, hj, ite_true, if_true, one_mul, mul_one]
  · have hz := hV i j (by simp only [hi, hj, true_iff, not_false_eq_true])
    simp only [hi, hj, ite_true, if_true, ite_false, if_false, hz, mul_zero]
  · have hz := hV i j (by simp only [hi, hj, iff_true, not_false_eq_true])
    simp only [hi, hj, ite_true, if_true, ite_false, if_false, hz, mul_zero, zero_mul]
  · simp only [hi, hj, ite_false, if_false, zero_mul, mul_zero]

theorem singleBlockProjection_fixed_near_identity {n : ℕ}
    (L : Subgroup (G n)) (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (hroot : ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hsupport : ∀ V ∈ matrixVelocitySpace L, ∀ i j,
      ¬(i ∈ S ↔ j ∈ S) → V i j = 0) :
    {g : L | slMatrixConjugation g.val (blockProjection (singleBlockSetoid S) k) =
      blockProjection (singleBlockSetoid S) k} ∈ 𝓝 (1 : L) := by
  let r := singleBlockSetoid S
  let P := blockProjection r k
  let M : L → Matrix (Fin n) (Fin n) ℝ := fun g => slMatrixConjugation g.val P
  have hcont : Continuous M := by unfold M slMatrixConjugation; fun_prop
  have hMone : M 1 = P := slMatrixConjugation_one P
  have hPkk : P k k = 1 := by
    dsimp only [P]
    rw [blockProjection_eq_diagonal, Matrix.diagonal_apply_eq]
    simp only [r.refl k, ite_true, if_true]
  have hsmall : {g : L | ‖M g - P‖ < 1} ∈ 𝓝 (1 : L) := by
    apply (isOpen_lt (hcont.sub continuous_const).norm continuous_const).mem_nhds
    change ‖M 1 - P‖ < 1
    simp only [hMone, sub_self, norm_zero, zero_lt_one]
  have hnz : {g : L | M g k k ≠ 0} ∈ 𝓝 (1 : L) := by
    apply (isOpen_ne_fun (hcont.matrix_elem k k) continuous_const).mem_nhds
    change M 1 k k ≠ 0
    rw [hMone, hPkk]
    exact one_ne_zero
  filter_upwards [hsmall, hnz] with g hg hkg
  apply commutant_idempotent_eq_blockProjection r k ⟨l, hkl, Or.inr ⟨hk, hl⟩⟩
    (M g) ?_ ?_ hkg hg
  · change slMatrixConjugationHom g.val P * slMatrixConjugationHom g.val P = _
    rw [← map_mul, blockProjection_mul_self]
    rfl
  · intro i j hij hr
    obtain ⟨hi, hj⟩ := (singleBlockSetoid_off_diagonal S hij).mp hr
    have hE : Matrix.single i j (1 : ℝ) ∈ matrixVelocitySpace L :=
      ⟨fun t => Matrix.SpecialLinearGroup.transvection hij t,
        hroot i hi j hj hij,
        by simpa only [mul_one] using hasIdentityMatrixDerivative_rootCurve hij 1⟩
    have hback := slMatrixConjugation_mem_velocitySpace L (L.inv_mem g.property) hE
    have hcomm := commute_singleBlockProjection_of_cross_zero S k hk _ (hsupport _ hback)
    have he := hcomm.map (slMatrixConjugationHom g.val)
    change Commute (M g)
      (slMatrixConjugation g.val (slMatrixConjugation g.val⁻¹ (Matrix.single i j (1 : ℝ)))) at he
    simpa only [slMatrixConjugation_inverse] using he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockComponents
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual root block and its canonical ergodic components

Ergodicity, diagonal velocity recurrence and the local block-preserving
stabilizer conclusion now refer to the same full-subgroup conditional
kernel. The selected root flow is ergodic on each component by Mautner;
no ergodicity of a selected diagonal element is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_singleBlock_component_ergodic_and_locally_block_preserving
    (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (k l : Fin (d + 1)) (hkl : k ≠ l) (hrkl : r k l) :
    let S : Set (Fin (d + 1)) := {i | r i k}
    let H := singleBlockRootGroup S
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X (d + 1))),
      let ν := condExpKernel μ (actionInvariantSigma H (X (d + 1))) z
      ErgodicSMul H (X (d + 1)) ν ∧
        (letI := rootTranslationAction hkl
         ErgodicSMul (Multiplicative ℝ) (X (d + 1)) ν) ∧
        {g : invariantRightSubgroup ν |
          slMatrixConjugation g.val (blockProjection (singleBlockSetoid S) k) =
            blockProjection (singleBlockSetoid S) k} ∈ 𝓝 (1 : invariantRightSubgroup ν) := by
  let S : Set (Fin (d + 1)) := {i | r i k}
  let H := singleBlockRootGroup S
  have hk : k ∈ S := r.refl k
  have hl : l ∈ S := r.symm hrkl
  have hH : H ≤ invariantRightSubgroup μ := by
    apply singleBlockRootGroup_le_of_roots
    intro i hi j hj hij t
    exact ((rootInvarianceRelation_iff_full_root hij μ).mp
      ((hr i j).mp (r.trans hi (r.symm hj)))) t
  have hAH : ∀ u : LogCoordinates d,
      diagonalFlow u ∈ Subgroup.normalizer (H : Set (G (d + 1))) := by
    intro u
    let ell : Fin (d + 1) → ℝ := Fin.snoc u (-∑ a, u a)
    have hell : ∑ a, ell a = 0 := by simp [ell, Fin.sum_univ_castSucc]
    have ha : diagonalOneParameter ell hell 1 = diagonalFlow u := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      congr 1
      funext a
      simp [ell]
    rw [← ha]
    exact diagonal_normalizes_singleBlockRootGroup S ell hell 1
  have hcomp := (lattice_canonical_subgroup_ergodic_decomposition H μ hH).2
  have hvel := ae_normalized_component_velocity_support d H hAH μ
  filter_upwards [hcomp, hvel] with z hz hVz
  let ν := condExpKernel μ (actionInvariantSigma H (X (d + 1))) z
  let : ErgodicSMul H (X (d + 1)) ν := hz
  have hHν : H ≤ invariantRightSubgroup ν :=
    subgroup_le_invariantRightSubgroup_of_invariant_action H ν
  refine ⟨hz, root_ergodic_of_single_block_ergodic S hkl hk hl ν, ?_⟩
  apply singleBlockProjection_fixed_near_identity (invariantRightSubgroup ν) S k l hkl hk hl
  · intro i hi j hj hij t
    exact hHν (root_mem_singleBlockRootGroup S i hi j hj hij t)
  · intro V hV i j hcross
    apply hVz V hV i j
    intro hij
    have hrij := (hr i j).mpr hij
    apply hcross
    change r i k ↔ r j k
    exact ⟨fun hi => r.trans (r.symm hrij) hi, fun hj => r.trans hrij hj⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TransverseStabilizerLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A transverse diagonal limit lies outside the stabilizer

The previously proved commutator identities give a global statement:
an element of L with nonzero diagonal preserves the maximal root blocks.
Consequently a nonidentity diagonal-conjugation limit with zero
within-block off-diagonal entries cannot belong to L. No additional
"limit outside L" assumption or connectedness assumption is used.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_blockMatrixGroup_of_cross_zero {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (hzero : ∀ i j, ¬ r i j → g.val i j = 0) :
    g ∈ blockMatrixGroup r := by
  have hcomm := (commute_blockScalars_iff r g.val).mpr hzero
  intro c hc
  apply slMatrixConjugation_eq_self
  apply Commute.symm
  apply hcomm
  refine (mem_blockScalarAlgebra_iff r _).mpr ⟨by simp, ?_⟩
  intro i j hij
  simpa only [Matrix.diagonal_apply_eq] using hc i j hij

lemma cross_zero_of_mem_blockMatrixGroup {n : ℕ} (r : Setoid (Fin n))
    (g : G n) (hg : g ∈ blockMatrixGroup r) :
    ∀ i j, ¬ r i j → g.val i j = 0 := by
  apply (commute_blockScalars_iff r g.val).mp
  intro M hM
  exact ((slMatrixConjugation_eq_self_iff g M).mp
    (slMatrixConjugation_eq_self_of_mem_blockMatrixGroup r g hg M hM)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SingleBlockLocalStabilizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From the velocity projection to actual local block preservation

Fixing the selected coordinate projection is exactly preservation of
that block and its complement. This translates the proved velocity
argument into the local subgroup statement used to choose a transverse
shearing shell.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem singleBlockProjection_fixed_iff {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S) (g : G n) :
    slMatrixConjugation g (blockProjection (singleBlockSetoid S) k) =
        blockProjection (singleBlockSetoid S) k ↔
      g ∈ blockMatrixGroup (blockComplementSetoid S) := by
  rw [slMatrixConjugation_eq_self_iff]
  constructor
  · intro hcomm
    apply mem_blockMatrixGroup_of_cross_zero
    intro i j hij
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hcomm.eq
    rw [blockProjection_singleBlock_eq S k hk, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    change ¬(i ∈ S ↔ j ∈ S) at hij
    by_cases hi : i ∈ S
    · have hj : j ∉ S := fun hj => hij ⟨fun _ => hj, fun _ => hi⟩
      simpa only [ite_eq_left hi, ite_eq_right hj, one_mul, mul_zero] using he
    · have hj : j ∈ S := by
        by_contra hj
        exact hij ⟨fun h => (hi h).elim, fun h => (hj h).elim⟩
      simpa only [ite_eq_right hi, ite_eq_left hj, zero_mul, mul_one] using he.symm
  · intro hg
    exact commute_singleBlockProjection_of_cross_zero S k hk g.val
      (cross_zero_of_mem_blockMatrixGroup (blockComplementSetoid S) g hg)

theorem local_singleBlock_of_fixed_projection {n : ℕ}
    (L : Subgroup (G n)) (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S)
    (hlocal : {g : L | slMatrixConjugation g.val (blockProjection (singleBlockSetoid S) k) =
      blockProjection (singleBlockSetoid S) k} ∈ 𝓝 (1 : L)) :
    {g : L | g.val ∈ blockMatrixGroup (blockComplementSetoid S)} ∈ 𝓝 (1 : L) := by
  filter_upwards [hlocal] with g hg
  exact (singleBlockProjection_fixed_iff S k hk g.val).mp hg

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PrimeSingleBlockHaar
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-degree Haar rigidity from a nontrivial invariant-root partition

The canonical component is genuinely ergodic for its chosen root block.
The shearing argument constructs a positive-mass block orbit, and the
rational stabilizer argument forces that block to be the full coordinate
set.  The root partition is supplied explicitly here: producing its
symmetry and nontriviality from positive entropy is the separate entropy
step, not a hidden homogeneous-orbit hypothesis.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem singleBlock_eq_univ_of_generic_local_stabilizer {n : ℕ}
    (hn : n.Prime) (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup S) (X n) μ]
    (hlocal : {g : invariantRightSubgroup μ |
      g.val ∈ blockMatrixGroup (blockComplementSetoid S)} ∈
        𝓝 (1 : invariantRightSubgroup μ))
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0) :
    S = univ := by
  classical
  let Sf := Finset.univ.filter (fun i => i ∈ S)
  have hSf : (↑Sf : Set (Fin n)) = S := by ext i; simp [Sf]
  have hSfE : ErgodicSMul (singleBlockRootGroup (Sf : Set (Fin n))) (X n) μ := by
    rw [hSf]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let := hSfE
  obtain ⟨g, hmass⟩ := exists_positive_singleBlock_orbit Sf k l hkl
    (by simpa only [← hSf, Finset.mem_coe] using hk)
    (by simpa only [← hSf, Finset.mem_coe] using hl) μ
    (by simpa only [hSf] using hlocal)
  rw [hSf] at hmass
  have hH : singleBlockRootGroup S ≤ invariantRightSubgroup μ :=
    subgroup_le_invariantRightSubgroup_of_invariant_action _ μ
  have hpair : blockComplementSetoid S k l := ⟨fun _ => hl, fun _ => hk⟩
  have hall := partition_universal_of_positive_block_orbit_mass hn g
    (blockComplementSetoid S) k l hkl hpair μ hmass
    (hH (root_mem_singleBlockRootGroup S k hk l hl hkl (-1)))
    (hH (root_mem_singleBlockRootGroup S l hl k hk hkl.symm (-1))) hgeneric
  apply Set.eq_univ_of_forall
  intro i
  exact (hall i k).mpr hk

/-- The orbit-existence conclusion is proved inside the argument. The
only remaining dynamical premise is the actual equivalence relation of
invariant roots with at least one nontrivial class. -/
theorem isHaar_of_prime_nontrivial_root_partition
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (r : Setoid (Fin (d + 1)))
    (hr : ∀ i j, r i j ↔ rootInvarianceRelation μ i j)
    (hnontrivial : ∃ k l, k ≠ l ∧ r k l) :
    IsHaarProbability μ := by
  obtain ⟨k, l, hkl, hrkl⟩ := hnontrivial
  let S : Set (Fin (d + 1)) := {i | r i k}
  let H := singleBlockRootGroup S
  have hk : k ∈ S := r.refl k
  have hl : l ∈ S := r.symm hrkl
  have hH : H ≤ invariantRightSubgroup μ := by
    apply singleBlockRootGroup_le_of_roots
    intro i hi j hj hij t
    exact ((rootInvarianceRelation_iff_full_root hij μ).mp
      ((hr i j).mp (r.trans hi (r.symm hj)))) t
  let m := actionInvariantSigma H (X (d + 1))
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  have hm : m ≤ xMeasurableSpace (d + 1) := actionInvariantSigma_le H _
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdec : κ ∘ₘ τ = μ := (lattice_canonical_subgroup_ergodic_decomposition H μ hH).1
  have hA (u : LogCoordinates d) :
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hgen : ∀ᵐ z ∂τ, ∀ᵐ x ∂κ z,
      ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0 := by
    apply Measure.ae_ae_of_ae_comp
    rw [hdec]
    exact ae_no_coordinate_zero d μ hA
  have hcomp := ae_singleBlock_component_ergodic_and_locally_block_preserving
    d μ r hr k l hkl hrkl
  let : @IsProbabilityMeasure (X (d + 1)) m τ := by
    constructor
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_univ
  obtain ⟨z, hz, hzg⟩ := (hcomp.and hgen).exists
  let : ErgodicSMul H (X (d + 1)) (κ z) := hz.1
  have hlocal := local_singleBlock_of_fixed_projection (invariantRightSubgroup (κ z))
    S k hk hz.2.2
  have hSuniv : S = univ := singleBlock_eq_univ_of_generic_local_stabilizer
    hprime S k l hkl hk hl (κ z) hlocal hzg
  have hall (i j : Fin (d + 1)) : r i j := by
    have hi : i ∈ S := by rw [hSuniv]; trivial
    have hj : j ∈ S := by rw [hSuniv]; trivial
    exact r.trans hi (r.symm hj)
  refine ⟨(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)), right_invariant_of_all_roots (by have := hprime.two_le; omega) μ ?_⟩
  intro i j hij t
  exact ((rootInvarianceRelation_iff_full_root hij μ).mp ((hr i j).mp (hall i j))) t

/-- The geometric application requires symmetry of the actual root
invariance relation. Reflexivity and transitivity are already proved
from the concrete root group identities. -/
theorem isHaar_of_prime_symmetric_invariant_roots_oai
    (d : ℕ) (hprime : (d + 1).Prime)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hsymm : Std.Symm (rootInvarianceRelation μ))
    (hroot : ∃ i j, i ≠ j ∧ rootInvarianceRelation μ i j) :
    IsHaarProbability μ := by
  let r : Setoid (Fin (d + 1)) :=
    { r := rootInvarianceRelation μ
      iseqv := {
        refl := fun _ => Or.inl rfl
        symm := fun {i j} h => hsymm.symm i j h
        trans := fun {_ _ _} hij hjk => rootInvarianceRelation_trans μ hij hjk } }
  exact isHaar_of_prime_nontrivial_root_partition d hprime μ r
    (fun _ _ => Iff.rfl) hroot

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.isHaar_of_prime_symmetric_invariant_roots_oai := @OAI.DukePrimeDegree.isHaar_of_prime_symmetric_invariant_roots_oai
