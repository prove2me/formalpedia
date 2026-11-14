-- Prove2me | solution 1 for OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:59.964258+00:00
-- url     : https://prove2.me/submissions/bf04d992-9d65-4172-8fba-dc248775d8fe

import Mathlib
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial shearing along a root subgroup

The exact matrix formula is the algebraic part of the low-entropy
argument: conjugation by a root unipotent is quadratic in its parameter.
The exceptional case is precisely the centralizer, and commuting with a
single nonzero root element already characterizes that case.
-/

open scoped BigOperators Classical
open Filter

namespace DukePrimeDegree

open PrimeDegreePackets

/-- The quadratic root-shearing formula, for arbitrary matrix indices. -/
theorem root_conjugation_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s =
      g.1 r s + (if r = i then t * g.1 j s else 0) -
        (if s = j then t * g.1 r i else 0) -
        (if r = i ∧ s = j then t ^ 2 * g.1 j i else 0) := by
  rw [root_mul_entry, root_left_mul_entry, root_left_mul_entry]
  by_cases hr : r = i <;> by_cases hs : s = j
  all_goals simp only [hr, hs, ite_true, if_true, ite_false, if_false, true_and, false_and]
  all_goals ring

/-- The centralizer of a root element at parameter one is the
centralizer of the full real root subgroup. -/
theorem commutes_root_one_iff_all {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g ↔
      ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
        Matrix.SpecialLinearGroup.transvection hij t * g := by
  constructor
  · intro h t
    obtain ⟨hcol, hrow, hdiag⟩ := (commutes_root_one_iff hij g).mp h
    ext r s
    simp only [root_mul_entry, root_left_mul_entry]
    by_cases hr : r = i <;> by_cases hs : s = j
    · subst r
      subst s
      simp only [ite_true, if_true, hdiag, mul_comm]
    · subst r
      simp [hs, hrow s hs]
    · subst s
      simp [hr, hcol r hr]
    · simp [hr, hs]
  · exact fun h => h 1

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingScale
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A first scale for noncentral root shearing

Every matrix outside a root centralizer has a finite positive first time
at which its conjugation displacement reaches a prescribed size. Before
that time all matrix entries remain uniformly controlled. This is the
stopping-time normalization used for the polynomial shearing argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma entry_sub_le_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) (r s : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      rootShearSize hij g t := by
  have hs : |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      ∑ u : Fin n, |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u| :=
    Finset.single_le_sum (f := fun u : Fin n =>
      |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u|)
      (fun u _ => abs_nonneg _) (Finset.mem_univ s)
  apply hs.trans
  exact Finset.single_le_sum (f := fun u : Fin n => ∑ v : Fin n,
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 u v - g.1 u v|)
    (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
    (Finset.mem_univ r)

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centralizer limits of normalized shearing trajectories

Uniform control before the first shearing time bounds the quadratic
coefficient. Since the shearing times diverge, the diagonal disturbance
vanishes. Every convergent terminal matrix therefore lies in the root
centralizer. These conclusions use actual special-linear matrices.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma root_conjugation_pivot {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 i j - g.1 i j =
      t * (g.1 j j - g.1 i i) - t ^ 2 * g.1 j i := by
  rw [root_conjugation_entry]
  simp only [ite_true, if_true, and_self]
  ring

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCompactness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A nontrivial limit of normalized shearing

The normalized first shearing intervals provide bounded terminal
matrices. Finite-dimensional compactness supplies a convergent
subsequence, whose limit is nontrivial and centralizes the root group.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma continuous_slMatrixDifference {n : ℕ} :
    Continuous (fun z : G n × G n => slMatrixDifference z.1 z.2) := by
  unfold slMatrixDifference
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  have hentry : Continuous (fun g : G n => g.1 r s) := by fun_prop
  exact ((hentry.comp continuous_fst).sub (hentry.comp continuous_snd)).abs

lemma slMatrixDifference_self {n : ℕ} (g : G n) : slMatrixDifference g g = 0 := by
  simp [slMatrixDifference]

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingHorosphere
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The horospherical shape of a normalized shearing limit

The limiting matrix differs from the identity only in the chosen row
and column, with unchanged diagonal. Its displacement is nilpotent of
order at most three. This is the precise horospherical direction used
in EKL (2006), Section 4.2, equations (4.6)--(4.8).
-/

noncomputable section
open Set Filter Matrix
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma root_conjugation_pivot_trace {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).val i i +
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).val j j = g.val i i + g.val j j := by
  rw [root_conjugation_entry, root_conjugation_entry]
  simp only [hij, hij.symm, ite_true, if_true, ite_false, if_false, false_and,
    and_false, sub_zero, add_zero]
  ring

/-- The off-root entries remain unchanged, and centrality forces the two
pivot diagonal limits to equal one. -/
theorem rootShearLimit_horospherical {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) (t : ℕ → ℝ)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-t m)) atTop (𝓝 h))
    (hcentral : h * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * h) : RootHorosphereShape i j h := by
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.val r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).val r s) atTop
      (𝓝 ((1 : G n).val r s)) := (hcont r s).tendsto 1 |>.comp hg
  have hhentry (r s : Fin n) : Tendsto (fun m =>
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).val r s)
      atTop (𝓝 (h.val r s)) := (hcont r s).tendsto h |>.comp hlim
  have hoff (r s : Fin n) (hr : r ≠ i) (hs : s ≠ j) :
      h.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s := by
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).val r s) =
        (fun m => (g m).val r s) := by
      funext m
      simp [root_conjugation_entry, hr, hs]
    exact tendsto_nhds_unique (he ▸ hhentry r s) (hgentry r s)
  have htrace : h.val i i + h.val j j = 2 := by
    have he : (fun m =>
        (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).val i i +
        (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).val j j) =
        (fun m => (g m).val i i + (g m).val j j) :=
      funext fun m => root_conjugation_pivot_trace hij (g m) (t m)
    have hgtrace : Tendsto (fun m => (g m).val i i + (g m).val j j) atTop (𝓝 (2 : ℝ)) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq,
        show (1 + 1 : ℝ) = 2 by norm_num] using (hgentry i i).add (hgentry j j)
    exact tendsto_nhds_unique (he ▸ (hhentry i i).add (hhentry j j)) hgtrace
  have heq : h.val i i = h.val j j := ((commutes_root_one_iff hij h).mp hcentral).2.2
  intro r s hrs
  rcases hrs with hrs | rfl
  · exact hoff r s hrs.1 hrs.2
  · by_cases hri : r = i
    · subst r
      simp only [Matrix.one_apply_eq]
      linarith
    · by_cases hrj : r = j
      · subst r
        simp only [Matrix.one_apply_eq]
        linarith
      · exact hoff r r hri hrj

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCollision
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactness for pairs with equal leaf data

The last limiting step of the low-entropy argument: equal continuous
leaf data on a compact set survive a normalized shearing limit. This
isolates the compactness step from the return-time selection and the
horospherical separation argument in EKL (2006), Section 4.2.
-/

noncomputable section
open Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem compact_equal_data_orbit_limit
    {n : ℕ} {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (H : ℕ → G n) (h : G n)
    (hx : ∀ m, x m ∈ K) (hy : ∀ m, rightAction (x m) (H m) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m) (H m)))
    (hH : Tendsto H atTop (𝓝 h)) :
    ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  obtain ⟨z, hz, φ, hφ, hlim⟩ := hK.isSeqCompact hx
  have hxlim : Tendsto (x ∘ φ) atTop (𝓝 z) := hlim
  have hylim : Tendsto (fun m => rightAction (x (φ m)) (H (φ m)))
      atTop (𝓝 (rightAction z h)) :=
    (continuous_rightAction_uncurry n).continuousAt.tendsto.comp
      (hxlim.prodMk_nhds (hH.comp hφ.tendsto_atTop))
  have hzy : rightAction z h ∈ K := hK.isClosed.mem_of_tendsto hylim
    (Eventually.of_forall fun m => hy (φ m))
  have hFx : Tendsto (fun m => F (x (φ m))) atTop (𝓝 (F z)) :=
    (hF z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Eventually.of_forall fun m => hx (φ m)⟩)
  have hFy : Tendsto (fun m => F (rightAction (x (φ m)) (H (φ m))))
      atTop (𝓝 (F (rightAction z h))) :=
    (hF _ hzy).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hylim, Eventually.of_forall fun m => hy (φ m)⟩)
  have heq' : (fun m => F (x (φ m))) =
      (fun m => F (rightAction (x (φ m)) (H (φ m)))) := funext fun m => heq (φ m)
  exact ⟨z, hz, hzy, tendsto_nhds_unique hFx (heq' ▸ hFy)⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSignedCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits for shearing times of either sign

Annular return selection can produce positive or negative root times.
Bounds on the symmetric interval and divergence of the absolute times
suffice for the centralizer conclusion, without a sign assumption.
-/

noncomputable section
open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma signed_root_shearing_quadratic_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t a : ℝ)
    (hsmall : ∀ u : ℝ, |u| ≤ |t| → rootShearSize hij g u ≤ a) :
    |t ^ 2 * g.val j i| ≤ 6 * a := by
  let f : ℝ → ℝ := fun u =>
    (Matrix.SpecialLinearGroup.transvection hij u * g *
      Matrix.SpecialLinearGroup.transvection hij (-u)).val i j - g.val i j
  have h1 : |f t| ≤ a :=
    (entry_sub_le_rootShearSize hij g t i j).trans (hsmall t le_rfl)
  have hh : |t / 2| ≤ |t| := by
    rw [abs_div]
    norm_num
  have h2 : |f (t / 2)| ≤ a :=
    (entry_sub_le_rootShearSize hij g (t / 2) i j).trans (hsmall (t / 2) hh)
  have he : t ^ 2 * g.val j i = 4 * f (t / 2) - 2 * f t := by
    have hf (u : ℝ) : f u = u * (g.val j j - g.val i i) - u ^ 2 * g.val j i :=
      root_conjugation_pivot hij g u
    rw [hf, hf]
    ring
  rw [he]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma signed_root_shearing_linear_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t a : ℝ) (ht : t ≠ 0)
    (hsmall : ∀ u : ℝ, |u| ≤ |t| → rootShearSize hij g u ≤ a) :
    |t * g.val j i| ≤ 6 * a / |t| := by
  apply (le_div_iff₀ (abs_pos.mpr ht)).mpr
  have he : |t * g.val j i| * |t| = |t ^ 2 * g.val j i| := by
    simp only [abs_mul, abs_pow]
    ring
  rw [he]
  exact signed_root_shearing_quadratic_bound hij g t a hsmall

lemma tendsto_signed_root_shearing_linear_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop) (a : ℝ)
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ a) :
    Tendsto (fun m => t m * (g m).val j i) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro m
    simpa only [Real.norm_eq_abs] using
      signed_root_shearing_linear_bound hij (g m) (t m) a (ht m) (hsmall m)
  · exact tendsto_const_nhds.div_atTop htop

theorem rootShearLimit_signed_centralizes {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a : ℝ) (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ a)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-t m)) atTop (𝓝 h)) :
    ∀ u : ℝ, h * Matrix.SpecialLinearGroup.transvection hij u =
      Matrix.SpecialLinearGroup.transvection hij u * h := by
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.1 r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).1 r s) atTop
      (𝓝 ((1 : G n).1 r s)) :=
    (hcont r s).tendsto _ |>.comp hg
  have hhentry (r s : Fin n) : Tendsto (fun m =>
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 r s) atTop (𝓝 (h.1 r s)) :=
    (hcont r s).tendsto _ |>.comp hlim
  have hlinear := tendsto_signed_root_shearing_linear_zero hij g t ht htop a hsmall
  apply (commutes_root_one_iff_all hij h).mp
  apply (commutes_root_one_iff hij h).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 r i) =
        (fun m => (g m).1 r i) := by
      funext m
      simp [root_conjugation_entry, hr, hij]
    have hzero : Tendsto (fun m => (g m).1 r i) atTop (𝓝 0) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hr] using hgentry r i
    exact tendsto_nhds_unique (he ▸ hhentry r i) hzero
  · intro s hs
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).1 j s) =
        (fun m => (g m).1 j s) := by
      funext m
      simp [root_conjugation_entry, hs, hij.symm]
    have hzero : Tendsto (fun m => (g m).1 j s) atTop (𝓝 0) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (Ne.symm hs)] using hgentry j s
    exact tendsto_nhds_unique (he ▸ hhentry j s) hzero
  · have hdiag_i : h.1 i i = 1 := by
      have hconv := (hgentry i i).add hlinear
      have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).1 i i) =
          (fun m => (g m).1 i i + t m * (g m).1 j i) := by
        funext m
        simp [root_conjugation_entry, hij]
      have hone : Tendsto (fun m => (g m).1 i i + t m * (g m).1 j i) atTop (𝓝 1) := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, add_zero] using hconv
      exact tendsto_nhds_unique (he ▸ hhentry i i) hone
    have hdiag_j : h.1 j j = 1 := by
      have hconv := (hgentry j j).sub hlinear
      have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).1 j j) =
          (fun m => (g m).1 j j - t m * (g m).1 j i) := by
        funext m
        simp [root_conjugation_entry, hij.symm]
      have hone : Tendsto (fun m => (g m).1 j j - t m * (g m).1 j i) atTop (𝓝 1) := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, sub_zero] using hconv
      exact tendsto_nhds_unique (he ▸ hhentry j j) hone
    exact hdiag_i.trans hdiag_j.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSignedLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded shearing intervals with signed return times

Selected annular returns may have either sign. A positive lower
terminal displacement and a bound on the symmetric interval produce a
nontrivial horospherical limit.
-/

noncomputable section
open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_signed_bounded_horospherical_rootShearLimit
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a B : ℝ) (ha : 0 < a)
    (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧
      a ≤ slMatrixDifference h 1 ∧ slMatrixDifference h 1 ≤ B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) atTop (𝓝 h) := by
  let H : ℕ → G n := fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
    Matrix.SpecialLinearGroup.transvection hij (-t m)
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.1 r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).1 r s) atTop
      (𝓝 ((1 : G n).1 r s)) :=
    (hcont r s).tendsto _ |>.comp hg
  have hgsmall : ∀ᶠ m : ℕ in atTop, ∀ r s : Fin n, |(g m).1 r s| ≤ 2 := by
    apply Filter.eventually_all.mpr
    intro r
    apply Filter.eventually_all.mpr
    intro s
    have hval : |(1 : G n).1 r s| < (2 : ℝ) := by
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
      split_ifs <;> norm_num
    exact ((hgentry r s).abs.eventually (gt_mem_nhds hval)).mono fun _ hm => hm.le
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | ∀ r s, |M r s| ≤ B + 2}
  have hK : IsCompact K := by
    have hbox : IsCompact {M : Matrix (Fin n) (Fin n) ℝ |
        ∀ r s, M r s ∈ Icc (-(B + 2)) (B + 2)} :=
      isCompact_pi_infinite fun _ : Fin n =>
      isCompact_pi_infinite fun _ : Fin n =>
        (isCompact_Icc : IsCompact (Icc (-(B + 2)) (B + 2)))
    simpa only [K, mem_Icc, abs_le] using hbox
  have hHK : ∀ᶠ m : ℕ in atTop, (H m).1 ∈ K := by
    filter_upwards [hgsmall] with m hm
    intro r s
    calc
      |(H m).1 r s| = |((H m).1 r s - (g m).1 r s) + (g m).1 r s| :=
        by rw [sub_add_cancel]
      _ ≤ |(H m).1 r s - (g m).1 r s| + |(g m).1 r s| := abs_add_le _ _
      _ ≤ B + 2 := add_le_add
        ((entry_sub_le_rootShearSize hij (g m) (t m) r s).trans
          (hsmall m (t m) le_rfl)) (hm r s)
  obtain ⟨M, _, φ, hφ, hM⟩ := hK.tendsto_subseq' hHK.frequently
  have hdet : M.det = 1 := by
    apply (isClosed_eq continuous_id.matrix_det continuous_const).mem_of_tendsto hM
    exact Filter.Eventually.of_forall fun m => (H (φ m)).property
  let h : G n := ⟨M, hdet⟩
  have hH : Tendsto (H ∘ φ) atTop (𝓝 h) := by
    apply tendsto_subtype_rng.mpr
    exact hM
  have hgp : Tendsto (g ∘ φ) atTop (𝓝 1) := hg.comp hφ.tendsto_atTop
  have hD := continuous_slMatrixDifference.continuousAt.tendsto.comp (hH.prodMk_nhds hgp)
  have hD' : Tendsto (fun m => slMatrixDifference (H (φ m)) (g (φ m)))
      atTop (𝓝 (slMatrixDifference h 1)) := by
    simpa only [Function.comp_def] using hD
  have hlow : a ≤ slMatrixDifference h 1 :=
    ge_of_tendsto hD' (Eventually.of_forall fun m => hsize (φ m))
  have hupp : slMatrixDifference h 1 ≤ B :=
    le_of_tendsto hD' (Eventually.of_forall fun m =>
      hsmall (φ m) (t (φ m)) le_rfl)
  have hcentral := rootShearLimit_signed_centralizes hij (g ∘ φ) hgp (t ∘ φ)
    (fun m => ht (φ m)) (htop.comp hφ.tendsto_atTop) B
    (fun m => hsmall (φ m)) h hH
  have hshape := rootShearLimit_horospherical hij (g ∘ φ) hgp (t ∘ φ) h hH (hcentral 1)
  have hne : h ≠ 1 := by
    intro he
    rw [he, slMatrixDifference_self] at hlow
    exact ha.not_ge hlow
  exact ⟨h, hne, hshape, hlow, hupp, φ, hφ, hH⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingSignedCollision
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact collisions at signed annular return times

Equal leaf data on compact simultaneous returns survive the signed
bounded shearing limit. A uniform horospherical separation property then
excludes such sequences.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem signed_shearing_forces_horospherical_collision_oai
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a B : ℝ) (ha : 0 < a)
    (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B)
    (hx : ∀ m, x m ∈ K)
    (hy : ∀ m, rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧
      a ≤ slMatrixDifference h 1 ∧ slMatrixDifference h 1 ≤ B ∧
      ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  obtain ⟨h, hne, hshape, hlow, hupp, φ, hφ, hlim⟩ :=
    exists_signed_bounded_horospherical_rootShearLimit hij g hg t ht htop a B ha hsize hsmall
  obtain ⟨z, hz, hzh, heqz⟩ := compact_equal_data_orbit_limit K hK F hF (x ∘ φ)
    (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
      Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) h
    (fun m => hx (φ m)) (fun m => hy (φ m)) (fun m => heq (φ m)) hlim
  exact ⟨h, hne, hshape, hlow, hupp, z, hz, hzh, heqz⟩

end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision_oai.{u_1} := @OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision_oai.{u_1}
