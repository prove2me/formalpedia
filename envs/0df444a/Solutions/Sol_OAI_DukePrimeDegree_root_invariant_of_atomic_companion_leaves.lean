-- Prove2me | solution 1 for OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:58.959104+00:00
-- url     : https://prove2.me/submissions/8b3a5df4-3ade-46eb-9328-933278a415e5

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
import Mathlib.MeasureTheory.Measure.Support
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
import Definitions.Def_OAIQ244Duke035
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_exists_distinct_equal_leaf_horospherical_pair
import Theorems.Thm_OAI_DukePrimeDegree_exists_nullset_atomic_root_limit
import Theorems.Thm_OAI_DukePrimeDegree_rootBox_leaf_separates_fibers_outside_nullset

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HorosphereIsolatingFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a peripheral root of the shearing horosphere

Each noncentral row or column coordinate can be left unchanged by a
trace-zero diagonal flow which contracts all other horospherical
coordinates. The resulting conjugates converge to that single root.
-/

noncomputable section
open Matrix Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rowIsolatingRaw_equal {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hkj : k ≠ j) : rowIsolatingRaw i j k i = rowIsolatingRaw i j k k := by
  simp [rowIsolatingRaw, hij, hkj]

lemma columnIsolatingRaw_equal {n : ℕ} {i j k : Fin n}
    (hji : j ≠ i) (hki : k ≠ i) : columnIsolatingRaw i j k k = columnIsolatingRaw i j k j := by
  simp [columnIsolatingRaw, hji, hki]

lemma rowIsolatingRaw_negative {n : ℕ} {i j k r s : Fin n}
    (hij : i ≠ j) (hkj : k ≠ j)
    (hrs : r ≠ s) (hshape : r = i ∨ s = j) (hne : ¬ (r = i ∧ s = k)) :
    rowIsolatingRaw i j k r - rowIsolatingRaw i j k s < 0 := by
  rcases hshape with hri | hsj
  · subst r
    have hsi : s ≠ i := Ne.symm hrs
    have hsk : s ≠ k := fun h => hne ⟨rfl, h⟩
    by_cases hsj : s = j
    · subst s; simp [rowIsolatingRaw, hij]
    · simp [rowIsolatingRaw, hij, hsj, hsi, hsk]
  · subst s
    have hrj : r ≠ j := hrs
    by_cases hri : r = i <;> by_cases hrk : r = k <;>
      simp [rowIsolatingRaw, hij, hkj, hrj, hri, hrk]

lemma columnIsolatingRaw_negative {n : ℕ} {i j k r s : Fin n}
    (hij : i ≠ j) (hki : k ≠ i)
    (hrs : r ≠ s) (hshape : r = i ∨ s = j) (hne : ¬ (r = k ∧ s = j)) :
    columnIsolatingRaw i j k r - columnIsolatingRaw i j k s < 0 := by
  rcases hshape with hri | hsj
  · subst r
    have hsi : s ≠ i := Ne.symm hrs
    by_cases hsj : s = j <;> by_cases hsk : s = k <;>
      simp [columnIsolatingRaw, hij.symm, hki, hsi, hsj, hsk]
  · subst s
    have hrj : r ≠ j := hrs
    have hrk : r ≠ k := fun h => hne ⟨h, rfl⟩
    by_cases hri : r = i
    · subst r; simp [columnIsolatingRaw, hij.symm]
    · simp [columnIsolatingRaw, hij.symm, hri, hrj, hrk]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootOrbitSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root-orbit separation outside one null set

Countably many long root boxes cover every finite segment of every free
root orbit. Removing their exceptional sets turns the chartwise
separation theorem into separation for all root translations at once.
This proves the one-dimensional part of EKL Lemma 4.4(2), without a
pointwise rebasing assumption.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_root_orbit_leaf_separation
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) ∉ N →
      intrinsicRootLeaf hij μ x =
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) →
      t = 0 := by
  let C := fun (k : Fin (d + 1)) (m : ℕ) => rootLongBoxFamily hij k 1 m
  let (k : Fin (d + 1)) (m : ℕ) : Countable (C k m) :=
    (rootLongBoxFamily_countable hij k 1 m).to_subtype
  let I := Σ k : Fin (d + 1), Σ m : ℕ, C k m
  let box := fun q : I => q.2.2.val
  have htime (q : I) : (box q).time ⊆ rootLeafWindow (1 + (q.2.1 : ℝ)) 0 := by
    rw [rootLongBoxFamily_time hij q.1 1 q.2.1 (box q) q.2.2.property]
    simp only [rootLeafWindow, Nat.cast_zero, add_zero, subset_refl]
  have hlocal (q : I) := rootBox_leaf_separates_fibers_outside_nullset
    d hij μ hnot (box q) (1 + (q.2.1 : ℝ)) (htime q)
  choose N hN hzero hsep using hlocal
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨M, hbad, hM, hMzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hfree)
  let E := M ∪ ⋃ q : I, N q
  have hEzero : μ E = 0 := measure_union_null hMzero (measure_iUnion_null hzero)
  refine ⟨E, hM.union (MeasurableSet.iUnion hN), hEzero, ?_⟩
  intro x hx t hy heq
  have hxfree : ∀ u : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij u) = x → u = 0 := by
    by_contra h
    exact hx (Or.inl (hbad h))
  obtain ⟨k, B, z, hz⟩ := exists_rootBox_at hij x
  let s := z.val.1
  let v := z.val.2
  have hxparam : rootQuotientParametrization hij (s, v) = x := hz
  have hyparam : rootQuotientParametrization hij (s, v + t) =
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) := by
    rw [rootQuotientParametrization_add, hxparam]
  have hsfree := root_time_injective_of_free hij s v (by rwa [hxparam])
  obtain ⟨m, hm⟩ := exists_nat_gt (max |v| |v + t|)
  have hv : v ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_left _ _) hm).trans (by linarith)
  have hvt : v + t ∈ rootLeafWindow 1 m := by
    apply abs_lt.mp
    exact (lt_of_le_of_lt (le_max_right _ _) hm).trans (by linarith)
  obtain ⟨D, hD, hsD⟩ := rootLongBoxFamily_covers hij k 1 m s hsfree
  let q : I := ⟨k, m, ⟨D, hD⟩⟩
  have htD : D.time = rootLeafWindow 1 m := rootLongBoxFamily_time hij k 1 m D hD
  have hzD : (s, v) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hv⟩
  have hwD : (s, v + t) ∈ (box q).domain := ⟨hsD, htD.symm ▸ hvt⟩
  have hNx : rootQuotientParametrization hij (s, v) ∉ N q := by
    rw [hxparam]
    exact fun h => hx (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have hNy : rootQuotientParametrization hij (s, v + t) ∉ N q := by
    rw [hyparam]
    exact fun h => hy (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
  have hzw := hsep q (s, v) hzD (s, v + t) hwD hNx hNy rfl (by
    rwa [hxparam, hyparam])
  have hvv := congrArg Prod.snd hzw
  dsimp only at hvv
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HorosphereSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Horospherical support and leaf separation

The horospherical support property of EKL (2006), Lemma 4.4(1), together
with separation along a root orbit gives Lemma 4.4(2). The support
property follows from the root product theorem, Proposition 8.3 of
Einsiedler--Katok (2003).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_horospherical_leaf_separation_of_root_support
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (hsupport : ∀ x ∉ N, ∀ h : G (d + 1), RootHorosphereShape i j h →
      rightAction x h ∉ N → ∃ t : ℝ,
        rightAction x h = rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) :
    ∃ M : Set (X (d + 1)), MeasurableSet M ∧ μ M = 0 ∧ ∀ x ∉ M,
      ∀ h : G (d + 1), RootHorosphereShape i j h → rightAction x h ∉ M →
        intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ (rightAction x h) →
        rightAction x h = x := by
  obtain ⟨E, hE, hEzero, hsep⟩ := exists_nullset_root_orbit_leaf_separation d hij μ hnot
  refine ⟨N ∪ E, hN.union hE, measure_union_null hNzero hEzero, ?_⟩
  intro x hx h hshape hy heq
  have hxN : x ∉ N := fun he => hx (Or.inl he)
  have hxE : x ∉ E := fun he => hx (Or.inr he)
  have hyN : rightAction x h ∉ N := fun he => hy (Or.inl he)
  have hyE : rightAction x h ∉ E := fun he => hy (Or.inr he)
  obtain ⟨t, ht⟩ := hsupport x hxN h hshape hyN
  have hzero := hsep x hxE t (by rwa [← ht]) (by rwa [← ht])
  simpa [hzero] using ht

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LowEntropySupportReduction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reduction of root invariance to the published support lemma

For the integer-lattice quotient, exclusion of exceptional neutral
returns and the shearing argument give root invariance from the support
conclusion of EKL (2006), Lemma 4.4(1).
-/

noncomputable section
open Set Filter MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem root_invariant_of_horospherical_root_support
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (hsupport : ∀ x ∉ N, ∀ h : G (d + 1), RootHorosphereShape i j h →
      rightAction x h ∉ N → ∃ t : ℝ,
        rightAction x h = rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) :
    ∀ a : ℝ, μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  by_contra hnot
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨M, hM, hMzero, hsep⟩ :=
    exists_horospherical_leaf_separation_of_root_support d hij μ hnot N hN hNzero hsupport
  obtain ⟨x, hx, h, hshape, hy, hne, heq⟩ :=
    exists_distinct_equal_leaf_horospherical_pair d hd hij μ hA hnontrivial M hM hMzero
  exact hne (hsep x hx h hshape hy heq)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HorosphereIsolatedLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Peripheral root limits of diagonal conjugates

The isolating flows send any shearing-horosphere element to the
transvection whose parameter is the selected matrix entry.
-/

noncomputable section
open Matrix Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem horosphere_isolated_root_limit
    (d : ℕ) {i j a b : Fin (d + 1)} (hab : a ≠ b)
    (w : Fin (d + 1) → ℝ) (hw : w a = w b)
    (hdecay : ∀ r s, r ≠ s → (r = i ∨ s = j) → ¬ (r = a ∧ s = b) →
      w r - w s < 0)
    (g : G (d + 1)) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ => diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) t *
      g * diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hab (g.val a b))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have he (t : ℝ) :
      (diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) t *
        g * diagonalOneParameter (centerWeights d w) (centerWeights_sum d w) (-t)).val r s =
      Real.exp ((w r - w s) * t) * g.val r s := by
    rw [conjugation_entry, centerWeights_sub]
  simp_rw [he]
  by_cases hrs : r = s
  · subst s
    have hd := hg r r (Or.inr rfl)
    simp only [sub_self, zero_mul, Real.exp_zero, one_mul, hd]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) r r) atTop (𝓝 _)) using 1
    all_goals try with_reducible_and_instances rfl
    by_cases hra : r = a
    · subst r
      simp [Matrix.SpecialLinearGroup.transvection_coe, hab.symm]
    · simp [Matrix.SpecialLinearGroup.transvection_coe, Ne.symm hra]
  by_cases hrab : r = a ∧ s = b
  · rcases hrab with ⟨hra, hsb⟩
    subst r
    subst s
    simp only [hw, sub_self, zero_mul, Real.exp_zero, one_mul]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => g.val a b) atTop (𝓝 _)) using 1
    all_goals try with_reducible_and_instances rfl
    simp [Matrix.SpecialLinearGroup.transvection_coe, hab]
  have htarget : (Matrix.SpecialLinearGroup.transvection hab (g.val a b)).val r s = 0 := by
    simp_all [Matrix.SpecialLinearGroup.transvection_coe, eq_comm]
  rw [htarget]
  by_cases hshape : r = i ∨ s = j
  · have hneg := hdecay r s hrs hshape hrab
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (by linarith : 0 < w s - w r) tendsto_id)
    have hlim := ht.mul_const (g.val r s)
    have heq (t : ℝ) : -((w s - w r) * t) = (w r - w s) * t := by ring
    simpa only [Function.comp_def, id_eq, heq, zero_mul] using hlim
  · have hzero : g.val r s = 0 := by
      have hri : r ≠ i := fun h => hshape (Or.inl h)
      have hsj : s ≠ j := fun h => hshape (Or.inr h)
      simpa only [Matrix.one_apply, hrs, ite_false, if_false] using hg r s (Or.inl ⟨hri, hsj⟩)
    simp only [hzero, mul_zero]
    exact tendsto_const_nhds

theorem horosphere_row_root_limit
    (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (g : G (d + 1)) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ =>
      diagonalOneParameter (centerWeights d (rowIsolatingRaw i j k))
        (centerWeights_sum d _) t * g *
      diagonalOneParameter (centerWeights d (rowIsolatingRaw i j k))
        (centerWeights_sum d _) (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hik (g.val i k))) :=
  horosphere_isolated_root_limit d hik _ (rowIsolatingRaw_equal hij hkj)
    (fun _ _ => rowIsolatingRaw_negative hij hkj) g hg

theorem horosphere_column_root_limit
    (d : ℕ) {i j k : Fin (d + 1)} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (g : G (d + 1)) (hg : RootHorosphereShape i j g) :
    Tendsto (fun t : ℝ =>
      diagonalOneParameter (centerWeights d (columnIsolatingRaw i j k))
        (centerWeights_sum d _) t * g *
      diagonalOneParameter (centerWeights d (columnIsolatingRaw i j k))
        (centerWeights_sum d _) (-t))
      atTop (𝓝 (Matrix.SpecialLinearGroup.transvection hkj (g.val k j))) :=
  horosphere_isolated_root_limit d hkj _ (columnIsolatingRaw_equal hij.symm hki)
    (fun _ _ => columnIsolatingRaw_negative hij hki) g hg

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HorosphereRootExtraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A horospherical element with no peripheral entries is a root element
-/

noncomputable section
open Matrix

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootHorosphere_eq_transvection_of_peripheral_zero
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : RootHorosphereShape i j g)
    (hrow : ∀ k, k ≠ i → k ≠ j → g.val i k = 0)
    (hcol : ∀ k, k ≠ i → k ≠ j → g.val k j = 0) :
    g = Matrix.SpecialLinearGroup.transvection hij (g.val i j) := by
  apply Subtype.ext
  ext r s
  by_cases hrs : r = s
  · subst s
    have hd := hg r r (Or.inr rfl)
    by_cases hri : r = i
    · subst r
      simpa [Matrix.SpecialLinearGroup.transvection_coe, hij.symm] using hd
    · simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Ne.symm hri] using hd
  by_cases hri : r = i
  · subst r
    by_cases hsj : s = j
    · subst s
      simp [Matrix.SpecialLinearGroup.transvection_coe, hij]
    · have hz := hrow s (Ne.symm hrs) hsj
      simp [Matrix.SpecialLinearGroup.transvection_coe, hrs, Ne.symm hsj, hz]
  · by_cases hsj : s = j
    · subst s
      have hz := hcol r hri hrs
      simp [Matrix.SpecialLinearGroup.transvection_coe, hrs, Ne.symm hri, hz]
    · have hz : g.val r s = 0 := by
        simpa only [Matrix.one_apply, hrs, ite_false, if_false] using hg r s (Or.inl ⟨hri, hsj⟩)
      simp [Matrix.SpecialLinearGroup.transvection_coe, hrs, Ne.symm hri, hz]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_HorosphereAtomicSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The atomic horospherical support theorem

This proves the support conclusion used in EKL (2006), Lemma 4.4(1).
For each peripheral root, an explicit diagonal flow isolates its matrix
entry. Atomicity and compact recurrence force that entry to vanish.
Thus only the distinguished root remains. This argument establishes the
needed consequence directly, without assuming the general product
formula of Einsiedler–Katok (2003), Proposition 8.3.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_horospherical_root_support
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hrow : ∀ (k : Fin (d + 1)) (hki : k ≠ i), k ≠ j →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hki.symm μ x = Measure.dirac 0)
    (hcol : ∀ k : Fin (d + 1), k ≠ i → (hkj : k ≠ j) →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hkj μ x = Measure.dirac 0) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ g : G (d + 1), RootHorosphereShape i j g → rightAction x g ∉ N →
        g = Matrix.SpecialLinearGroup.transvection hij (g.val i j) := by
  let I := {k : Fin (d + 1) // k ≠ i ∧ k ≠ j}
  have hr (k : I) := exists_nullset_atomic_root_limit d k.prop.1.symm μ hA
    (hrow k.val k.prop.1 k.prop.2) (centerWeights d (rowIsolatingRaw i j k.val))
    (centerWeights_sum d _)
  have hc (k : I) := exists_nullset_atomic_root_limit d k.prop.2 μ hA
    (hcol k.val k.prop.1 k.prop.2) (centerWeights d (columnIsolatingRaw i j k.val))
    (centerWeights_sum d _)
  choose R hR hRzero hRlimit using hr
  choose C hC hCzero hClimit using hc
  let N := (⋃ k : I, R k) ∪ ⋃ k : I, C k
  refine ⟨N, (MeasurableSet.iUnion hR).union (MeasurableSet.iUnion hC),
    measure_union_null (measure_iUnion_null hRzero) (measure_iUnion_null hCzero), ?_⟩
  intro x hx g hg hxg
  apply rootHorosphere_eq_transvection_of_peripheral_zero hij g hg
  · intro k hki hkj
    let q : I := ⟨k, hki, hkj⟩
    have hxR : x ∉ R q := fun h => hx (Or.inl (mem_iUnion.mpr ⟨q, h⟩))
    have hyR : rightAction x g ∉ R q := fun h => hxg (Or.inl (mem_iUnion.mpr ⟨q, h⟩))
    exact hRlimit q x hxR (rightAction x g) hyR g rfl (g.val i k)
      (horosphere_row_root_limit d hij hki.symm hkj g hg)
  · intro k hki hkj
    let q : I := ⟨k, hki, hkj⟩
    have hxC : x ∉ C q := fun h => hx (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
    have hyC : rightAction x g ∉ C q := fun h => hxg (Or.inr (mem_iUnion.mpr ⟨q, h⟩))
    exact hClimit q x hxC (rightAction x g) hyC g rfl (g.val k j)
      (horosphere_column_root_limit d hij hki hkj g hg)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LowEntropyInvariant
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unconditional low-entropy root invariance

For the integer-lattice quotient, a nontrivial distinguished root leaf
and atomic companion leaves force invariance under the distinguished
root subgroup. All support, recurrence, and shearing steps are proved.
This is the low-entropy alternative in EKL (2006), Theorem 2.3, specialized
to the quotient used by the prime-degree packet theorem.
-/

noncomputable section
open Set Filter MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem root_invariant_of_atomic_companion_leaves_oai
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnontrivial : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x ≠ Measure.dirac 0)
    (hrow : ∀ (k : Fin (d + 1)) (hki : k ≠ i), k ≠ j →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hki.symm μ x = Measure.dirac 0)
    (hcol : ∀ k : Fin (d + 1), k ≠ i → (hkj : k ≠ j) →
      ∀ᵐ x ∂μ, intrinsicRootLeaf hkj μ x = Measure.dirac 0) :
    ∀ a : ℝ, μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨N, hN, hNzero, hs⟩ := exists_nullset_horospherical_root_support d hij μ hA hrow hcol
  apply root_invariant_of_horospherical_root_support d hd hij μ hnontrivial N hN hNzero
  intro x hx g hg hy
  exact ⟨g.val i j, congrArg (rightAction x) (hs x hx g hg hy)⟩

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves_oai := @OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves_oai
