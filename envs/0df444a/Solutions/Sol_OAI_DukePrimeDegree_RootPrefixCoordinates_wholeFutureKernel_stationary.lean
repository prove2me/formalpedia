-- Prove2me | solution 1 for OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureKernel_stationary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:47:10.170715+00:00
-- url     : https://prove2.me/submissions/aea2a99b-af8b-48e3-b958-4a866d04a6ec

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
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
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke035
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_DukePrimeDegree_RootPrefixBox_ae_normalized_uncentered_eq_regularLeaf

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_GenericLatticeStabilizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.conditionalKernel_markov _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A generic lattice stabilizer cannot have an identity column -/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem stabilizer_trivial_of_identity_column {n : ℕ} (x : X n)
    (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (g : G n) (hfix : rightAction x g = x) (k : Fin n)
    (hcol : ∀ r, g.val r k = (1 : Matrix (Fin n) (Fin n) ℝ) r k) : g = 1 := by
  have hvec (v : Fin n → ℝ) (hv : v ∈ pointLattice x) : v ᵥ* g.val = v := by
    let w := v ᵥ* g.val - v
    have hw : w ∈ pointLattice x := by
      apply Submodule.sub_mem _ _ hv
      simpa only [hfix] using vecMul_mem_pointLattice_rightAction x g v hv
    have he : (v ᵥ* g.val) k = v k := by
      calc
        _ = (v ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ)) k := by
          change (∑ r, v r * g.val r k) = ∑ r, v r * (1 : Matrix (Fin n) (Fin n) ℝ) r k
          simp_rw [hcol]
        _ = _ := by rw [Matrix.vecMul_one]
    have hwk : w k = 0 := by change (v ᵥ* g.val) k - v k = 0; exact sub_eq_zero.mpr he
    have hw0 : w = 0 := by
      by_contra h
      exact hx w hw h k hwk
    exact sub_eq_zero.mp hw0
  induction x using Quotient.inductionOn with
  | h q =>
    have hm : q.val * g.val = q.val := by
      ext r s
      have hmem : q.val r ∈ pointLattice (Quotient.mk _ q) := by
        rw [pointLattice_mk, ← integerRowMap_range]
        refine ⟨Pi.single r 1, ?_⟩
        ext j
        simp [integerRowMap_apply, Matrix.vecMul, dotProduct, Pi.single_apply]
      exact congrFun (hvec (q.val r) hmem) s
    have hgroup : q * g = q := Subtype.ext hm
    exact mul_left_cancel (hgroup.trans (mul_one q).symm)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_UnipotentFreeness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Freeness of the full positive unipotent action

At the generic lattices already supplied by diagonal recurrence, no
nonzero lattice vector has a zero coordinate. A stabilizer element with
one identity column must therefore fix every lattice vector, so is the
identity. In particular all positive-root groups act freely there,
simultaneously.
-/

noncomputable section
open Matrix MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem positiveRootPattern_stabilizer_trivial {d : ℕ}
    (x : X (d + 1)) (hx : ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0)
    (S : Finset (Fin (d + 1) × Fin (d + 1))) (hpos : ∀ p ∈ S, p.1 < p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) (hfix : rightAction x g = x) :
    g = 1 := by
  apply stabilizer_trivial_of_identity_column x hx g hfix 0
  intro r
  apply hg r 0
  intro h
  exact (Fin.not_lt_zero r) (hpos (r, 0) h)

theorem ae_positiveRootPattern_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ (S : Finset (Fin (d + 1) × Fin (d + 1))),
      (∀ p ∈ S, p.1 < p.2) → ∀ g : G (d + 1),
        PositiveRootPattern S g → rightAction x g = x → g = 1 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx S hpos g hg hfix
  exact positiveRootPattern_stabilizer_trivial x hx S hpos g hg hfix

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditioningFiniteLabels
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioning a leaf kernel on a finite observed label

Adding a finite label to the transverse coordinate restricts the actual
conditional leaf to the corresponding label fiber and normalizes it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

omit [StandardBorelSpace T] [Nonempty T] in
lemma finiteLabelLift_measurable {N : ℕ} {Q : S × T → Fin N} (hQ : Measurable Q) :
    Measurable (finiteLabelLift Q) :=
  (measurable_fst.prodMk hQ).prodMk measurable_snd

omit [StandardBorelSpace T] [Nonempty T] in
lemma finiteLabelLift_restrict {N : ℕ} (ρ : Measure (S × T))
    {Q : S × T → Fin N} (hQ : Measurable Q) (b : Fin N) :
    (ρ.map (finiteLabelLift Q)).restrict ({s : S × Fin N | s.2=b} ×ˢ univ) =
      (ρ.restrict {z | Q z=b}).map (fun z : S × T => ((z.1,b),z.2)) := by
  rw [Measure.restrict_map (finiteLabelLift_measurable hQ)
    ((measurableSet_eq_fun measurable_snd measurable_const).prod MeasurableSet.univ)]
  have he : finiteLabelLift Q ⁻¹' ({s : S × Fin N | s.2=b} ×ˢ univ) = {z | Q z=b} := by
    ext z
    simp [finiteLabelLift]
  rw [he]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_eq_fun hQ measurable_const)] with z hz
  simp only [finiteLabelLift,hz]

theorem finiteLabelLift_condKernel_on_label {N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {Q : S × T → Fin N} (hQ : Measurable Q) (b : Fin N) :
    ∀ᵐ s ∂(ρ.restrict {z | Q z=b}).fst,
      (ρ.map (finiteLabelLift Q)).condKernel (s,b) =
        ((ρ.restrict {z | Q z=b}).condKernel s) := by
  let σ := ρ.map (finiteLabelLift Q)
  let U : Set (S × Fin N) := {s | s.2=b}
  let ρb := ρ.restrict {z | Q z=b}
  have hU : MeasurableSet U := measurableSet_eq_fun measurable_snd measurable_const
  have hs : σ.restrict (U ×ˢ univ) =
      ρb.map (fun z : S × T => ((z.1,b),z.2)) := finiteLabelLift_restrict ρ hQ b
  have hm : (σ.restrict (U ×ˢ univ)).fst = σ.fst.restrict U := by
    rw [restricted_conditional_marginal σ hU MeasurableSet.univ]
    simp only [measure_univ,withDensity_const,one_smul]
  have hmap : (σ.restrict (U ×ˢ univ)).fst = ρb.fst.map (fun s : S => (s,b)) := by
    rw [hs]
    exact fst_map_fibers_of_measurable ρb
      (fun s : S => (s,b)) (measurable_id.prodMk measurable_const) Prod.snd measurable_snd
  have hrestr := restricted_conditional_kernel σ hU MeasurableSet.univ
  simp only [measure_univ,one_smul,Measure.restrict_univ] at hrestr
  rw [←hm,hmap] at hrestr
  have hrestr' := ae_of_ae_map (measurable_id.prodMk measurable_const).aemeasurable hrestr
  have hfixed := conditional_map_fibers_leftInverse ρb
    (fun s : S => (s,b)) (measurable_id.prodMk measurable_const)
    Prod.fst measurable_fst (fun _ => rfl) Prod.snd measurable_snd
  filter_upwards [hrestr',hfixed] with s hs' hf
  simp only [hs,id_eq] at hs'
  change _ = (ρb.condKernel s).map id at hf
  rw [Measure.map_id] at hf
  exact hs'.symm.trans hf

theorem finiteLabelLift_condKernel {N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {Q : S × T → Fin N} (hQ : Measurable Q) :
    ∀ᵐ z ∂ρ,
      ρ.condKernel z.1 {t | Q (z.1,t)=Q z} ≠ 0 ∧
      (ρ.map (finiteLabelLift Q)).condKernel (z.1,Q z) =
        (anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=Q z}).restrict
          {t | Q (z.1,t)=Q z} := by
  have H (b : Fin N) : ∀ᵐ z ∂ρ.restrict {z | Q z=b},
      ρ.condKernel z.1 {t | Q (z.1,t)=b} ≠ 0 ∧
      (ρ.map (finiteLabelLift Q)).condKernel (z.1,b) =
        (anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=b}).restrict
          {t | Q (z.1,t)=b} := by
    have hb := (finiteLabelLift_condKernel_on_label ρ hQ b).and
      (conditional_restrict_normalized ρ {z | Q z=b} (measurableSet_eq_fun hQ measurable_const))
    have hb' := ae_of_ae_map measurable_fst.aemeasurable hb
    filter_upwards [hb'] with z hz
    exact ⟨hz.2.1,hz.1.trans hz.2.2⟩
  have H' (b : Fin N) : ∀ᵐ z ∂ρ, Q z=b →
      ρ.condKernel z.1 {t | Q (z.1,t)=b} ≠ 0 ∧
      (ρ.map (finiteLabelLift Q)).condKernel (z.1,b) =
        (anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=b}).restrict
          {t | Q (z.1,t)=b} :=
    (ae_restrict_iff' (measurableSet_eq_fun hQ measurable_const)).mp (H b)
  filter_upwards [ae_all_iff.mpr H'] with z hz
  exact hz (Q z) rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FiniteLabelEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional entropy after recording a transverse coordinate and label -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

lemma condExp_transverse_label_probability {M N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {P : S × T → Fin M} (hP : Measurable P)
    {Q : S × T → Fin N} (hQ : Measurable Q) (a : Fin M) :
    ρ[({z | P z=a}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap (fun z => (z.1,Q z))
          (inferInstance : MeasurableSpace (S × Fin N))] =ᵐ[ρ]
      fun z => ((ρ.map (finiteLabelLift Q)).condKernel (z.1,Q z)).real
        {t | P (z.1,t)=a} := by
  let f : (S × Fin N) × T → ℝ :=
    {z | P (z.1.1,z.2)=a}.indicator (fun _ => 1)
  have hf : Integrable f (ρ.map (finiteLabelLift Q)) := by
    apply (integrable_const (1:ℝ)).indicator
    exact measurableSet_eq_fun (hP.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have H := condExp_prod_ae_eq_integral_condDistrib'
    (μ := ρ) (X := fun z : S × T => (z.1,Q z)) (Y := Prod.snd)
    (measurable_fst.prodMk hQ) measurable_snd.aemeasurable hf
  have hκ : condDistrib (Prod.snd : S × T → T) (fun z => (z.1,Q z)) ρ =
      (ρ.map (finiteLabelLift Q)).condKernel := by
    rw [condDistrib]
    rfl
  rw [hκ] at H
  have hI (s : S × Fin N) : (∫ t, f (s,t) ∂(ρ.map (finiteLabelLift Q)).condKernel s) =
      ((ρ.map (finiteLabelLift Q)).condKernel s).real {t | P (s.1,t)=a} := by
    change (∫ t, {t | P (s.1,t)=a}.indicator (fun _ => (1:ℝ)) t
      ∂(ρ.map (finiteLabelLift Q)).condKernel s) = _
    have hs : MeasurableSet {t : T | P (s.1,t)=a} :=
      (hP (measurableSet_singleton a)).preimage measurable_prodMk_left
    rw [integral_indicator_const (1:ℝ) hs]
    simp only [smul_eq_mul,mul_one]
  have heq : (fun z : S × T => f ((z.1,Q z),z.2)) =
      {z | P z=a}.indicator (fun _ => (1:ℝ)) := by
    funext z
    rfl
  simpa only [heq,hI] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedRestrictionLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy limits for decreasing positive-mass conditioning cells -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_real {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hB : MeasurableSet B) :
    ((anchorNormalize ν A).restrict A).real B = ν.real (B ∩ A) / ν.real A := by
  rw [measureReal_def,Measure.restrict_apply hB,anchorNormalize,Measure.smul_apply]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,measureReal_def,
    div_eq_mul_inv,mul_comm]

theorem normalized_restriction_probability_tendsto {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n)) (hdec : Antitone A)
    (hpos : ν (⋂ n, A n) ≠ 0) (B : Set Y) (hB : MeasurableSet B) :
    Tendsto (fun n => ((anchorNormalize ν (A n)).restrict (A n)).real B) atTop
      (𝓝 (((anchorNormalize ν (⋂ n, A n)).restrict (⋂ n, A n)).real B)) := by
  have hden := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hA n).nullMeasurableSet)
    hdec ⟨0,measure_ne_top _ _⟩
  have hnum := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hB.inter (hA n)).nullMeasurableSet)
    (show Antitone (fun n => B ∩ A n) from fun n m hnm => inter_subset_inter subset_rfl (hdec hnm))
    ⟨0,measure_ne_top _ _⟩
  have he : (⋂ n, B ∩ A n) = B ∩ ⋂ n, A n := by
    ext y
    simp only [mem_iInter,mem_inter_iff]
    exact ⟨fun h => ⟨(h 0).1, fun i => (h i).2⟩,fun h i => ⟨h.1,h.2 i⟩⟩
  rw [he] at hnum
  have htden := (ENNReal.tendsto_toReal (measure_ne_top ν (⋂ n, A n))).comp hden
  have htnum := (ENNReal.tendsto_toReal (measure_ne_top ν (B ∩ ⋂ n, A n))).comp hnum
  have hd : ν.real (⋂ n, A n) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top _ _⟩
  have H := htnum.div htden hd
  change Tendsto (fun n => (ν (B ∩ A n)).toReal / (ν (A n)).toReal) atTop
    (𝓝 ((ν (B ∩ ⋂ n, A n)).toReal / (ν (⋂ n, A n)).toReal)) at H
  simpa only [Function.comp_def,normalized_restriction_real ν _ B hB,
    measureReal_def] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureCodes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite codes converging to the future of a countable observation

Both the time interval and the clipping level increase. The limiting atom
records every future value of the original countable observation.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

lemma truncate_countableFutureCode {Y : Type*} {m n : ℕ} (T : Y → Y) (Q : Y → ℕ)
    (hmn : m ≤ n) (y : Y) :
    truncateCountableFutureCode hmn (countableFutureCode T Q n y) =
      countableFutureCode T Q m y := by
  simp only [truncateCountableFutureCode,countableFutureCode,Equiv.symm_apply_apply]
  apply congrArg (Fintype.equivFin (Fin m → Fin (m+1)))
  funext i
  apply Fin.ext
  change min (min (Q (T^[i.val+1] y)) n) m = min (Q (T^[i.val+1] y)) m
  omega

lemma countableFutureCode_eq_of_longer {Y : Type*} {m n : ℕ}
    (T : Y → Y) (Q : Y → ℕ) (hmn : m ≤ n) {x y : Y}
    (h : countableFutureCode T Q n x=countableFutureCode T Q n y) :
    countableFutureCode T Q m x=countableFutureCode T Q m y := by
  have H := congrArg (truncateCountableFutureCode hmn) h
  simpa only [truncate_countableFutureCode] using H

lemma all_countableFutureCode_eq_iff {Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (x y : Y) :
    (∀ m, countableFutureCode T Q m x=countableFutureCode T Q m y) ↔
      ∀ k : ℕ, Q (T^[k+1] x)=Q (T^[k+1] y) := by
  constructor
  · intro h k
    let m := max k (max (Q (T^[k+1] x)) (Q (T^[k+1] y)))+1
    have hk : k < m := by dsimp only [m]; omega
    have hx : Q (T^[k+1] x) < m := by dsimp only [m]; omega
    have hy : Q (T^[k+1] y) < m := by dsimp only [m]; omega
    have he := congrArg (fun v =>
      ((Fintype.equivFin (Fin m → Fin (m+1))).symm v ⟨k,hk⟩).val) (h m)
    simp only [countableFutureCode,Equiv.symm_apply_apply] at he
    change min (Q (T^[k+1] x)) m=min (Q (T^[k+1] y)) m at he
    omega
  · intro h m
    apply congrArg (Fintype.equivFin (Fin m → Fin (m+1)))
    funext i
    apply Fin.ext
    change min (Q (T^[i.val+1] x)) m=min (Q (T^[i.val+1] y)) m
    rw [h i.val]

lemma transverse_countableFutureCode_monotone
    {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) :
    Monotone (fun m => transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) := by
  intro m n hmn A hA
  obtain ⟨B,hB,rfl⟩ := hA
  let f : S × Fin (Fintype.card (Fin n → Fin (n+1))) →
      S × Fin (Fintype.card (Fin m → Fin (m+1))) :=
    fun z => (z.1,truncateCountableFutureCode hmn z.2)
  have hf : Measurable f := measurable_fst.prodMk
    ((measurable_of_finite (truncateCountableFutureCode hmn)).comp measurable_snd)
  refine ⟨f ⁻¹' B,hf hB,?_⟩
  ext z
  simp only [Set.mem_preimage,f,truncate_countableFutureCode]

lemma countableFutureCode_fibers_antitone {S V Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) (z : S × V) :
    Antitone (fun m => labelFiber (fun z => countableFutureCode T Q m (F z)) z) := by
  intro m n hmn t ht
  exact countableFutureCode_eq_of_longer T Q hmn ht

lemma countableFutureFiber_eq_iInter {S V Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y) (z : S × V) :
    countableFutureFiber T Q F z =
      ⋂ m, labelFiber (fun z => countableFutureCode T Q m (F z)) z := by
  ext t
  simp only [countableFutureFiber,labelFiber,mem_iInter,mem_ofPred_eq]
  exact (all_countableFutureCode_eq_iff T Q (F (z.1,t)) (F z)).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CountableFutureMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire future as a measurable sequence

This representation makes future-measurable events constant on each
complete future fiber. It is used to restrict local disintegrations to
saturated events when gluing them.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The event that a complete future fiber has no mass outside a fixed
time domain is measurable using only the transverse coordinate and the
future name. -/
theorem measurableSet_future_mass_contained {S V Y : Type*}
    [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]
    (κ : Kernel S V) [IsSFiniteKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (B : Set V) (hB : MeasurableSet B) :
    MeasurableSet[⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))]
      {z | κ z.1 (countableFutureFiber T Q F z \ B) = 0} := by
  have hm := measurable_countableFuture_mass κ hT hQ hF
    (Prod.snd ⁻¹' Bᶜ) (hB.compl.preimage measurable_snd)
  have he := measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ≥0∞)))
  change MeasurableSet[⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))]
    {z | κ z.1 (Bᶜ ∩ countableFutureFiber T Q F z) = 0} at he
  simpa only [Set.sdiff_eq, Set.inter_comm] using he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureRestrictionNull
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a box restriction with only a null-set exception

For future-kernel gluing it suffices that the future measure outside a
box vanishes. Literal containment of every point in the fiber is stronger
than necessary.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem normalized_restriction_of_null_diff {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hB₀ : ν B ≠ 0) (hBtop : ν B ≠ ∞) (hnull : ν (A \ B) = 0) :
    (anchorNormalize ((anchorNormalize ν B).restrict B) A).restrict A =
      (anchorNormalize ν A).restrict A := by
  have hmem : ∀ᵐ y ∂ν.restrict A, y ∈ B := by
    rw [ae_iff]
    change ν.restrict A Bᶜ = 0
    rw [Measure.restrict_apply hB.compl]
    simpa only [Set.sdiff_eq, Set.inter_comm] using hnull
  have heq : (ν.restrict B).restrict A = ν.restrict A := by
    calc
      (ν.restrict B).restrict A = (ν.restrict A).restrict B := by
        rw [Measure.restrict_restrict hA, Measure.restrict_restrict hB, Set.inter_comm]
      _ = ν.restrict A := Measure.restrict_eq_self_of_ae_mem hmem
  have hmass : ν.restrict B A = ν A := by
    have h := congrArg (fun ρ : Measure Y => ρ univ) heq
    simpa only [Measure.restrict_apply_univ] using h
  have hscale : (anchorNormalize ν B).restrict B = (ν B)⁻¹ • ν.restrict B := by
    rw [anchorNormalize, Measure.restrict_smul]
  rw [hscale, anchorNormalize_smul _ _ _ (ENNReal.inv_ne_zero.mpr hBtop)
    (ENNReal.inv_ne_top.mpr hB₀)]
  simp only [anchorNormalize, Measure.restrict_smul, hmass, heq]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_InfiniteLabelProbability
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional probabilities on decreasing positive-mass fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExp_infinite_label_probability
    {S T : Type*} [mS : MeasurableSpace S] [mT : MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {M : ℕ} {P : S × T → Fin M} (hP : Measurable P)
    {k : ℕ → ℕ} (Q : ∀ n, S × T → Fin (k n)) (hQ : ∀ n, Measurable (Q n))
    (hmono : Monotone (fun n => transverseLabelSigma (Q n)))
    (hdec : ∀ z, Antitone (fun n => labelFiber (Q n) z))
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (⋂ n, labelFiber (Q n) z) ≠ 0)
    (a : Fin M) :
    ρ[({z | P z=a}.indicator (fun _ => (1:ℝ))) | ⨆ n, transverseLabelSigma (Q n)] =ᵐ[ρ]
      fun z => ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
        (⋂ n, labelFiber (Q n) z)).real {t | P (z.1,t)=a} := by
  let g : S × T → ℝ := {z | P z=a}.indicator (fun _ => 1)
  let ℱ : Filtration ℕ (mS.prod mT) :=
    ⟨fun n => transverseLabelSigma (Q n),hmono,
      fun n => (measurable_fst.prodMk (hQ n)).comap_le⟩
  have hmart := MeasureTheory.tendsto_ae_condExp (μ := ρ) (ℱ := ℱ) g
  have heq n : ρ[g | ℱ n] =ᵐ[ρ] fun z =>
      ((anchorNormalize (ρ.condKernel z.1) (labelFiber (Q n) z)).restrict
        (labelFiber (Q n) z)).real {t | P (z.1,t)=a} := by
    filter_upwards [condExp_transverse_label_probability ρ hP (hQ n) a,
      finiteLabelLift_condKernel ρ (hQ n)] with z hz hk
    exact hz.trans (congrArg (fun ν => ν.real {t | P (z.1,t)=a}) hk.2)
  filter_upwards [hmart,ae_all_iff.mpr heq,hpos] with z hm he hp
  have ht := normalized_restriction_probability_tendsto (ρ.condKernel z.1)
    (fun n => labelFiber (Q n) z)
    (fun n => measurableSet_eq_fun ((hQ n).comp measurable_prodMk_left) measurable_const)
    (hdec z) hp {t | P (z.1,t)=a}
    ((hP.comp measurable_prodMk_left) (measurableSet_singleton a))
  have hm' : Tendsto
      (fun n => ((anchorNormalize (ρ.condKernel z.1) (labelFiber (Q n) z)).restrict
        (labelFiber (Q n) z)).real {t | P (z.1,t)=a}) atTop
      (𝓝 ((ρ[g | ⨆ n, ℱ n]) z)) := by
    simpa only [he] using hm
  exact tendsto_nhds_unique hm' ht

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_InfiniteFutureStationarity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preservation of mass by conditioning on the entire future

The actual normalized restrictions supplied by the increasing finite-label
conditionings preserve the original measure when integrated over samples.
This is a local disintegration identity, before any gluing of root boxes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V : Type*} [mS : MeasurableSpace S] [mV : MeasurableSpace V]
    [StandardBorelSpace V] [Nonempty V]

/-- The disintegration identity remains valid on any event determined
by the whole future and the transverse coordinate. This is the local
restriction identity needed when gluing boxes along future events. -/
theorem setIntegral_infinite_label_conditional_probability
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {k : ℕ → ℕ} (Q : ∀ n, S × V → Fin (k n)) (hQ : ∀ n, Measurable (Q n))
    (hmono : Monotone (fun n => transverseLabelSigma (Q n)))
    (hdec : ∀ z, Antitone (fun n => labelFiber (Q n) z))
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (⋂ n, labelFiber (Q n) z) ≠ 0)
    (A : Set (S × V)) (hA : MeasurableSet A)
    (E : Set (S × V)) (hE : MeasurableSet[⨆ n, transverseLabelSigma (Q n)] E) :
    (∫ z in E,
      ((anchorNormalize (ρ.condKernel z.1) (⋂ n, labelFiber (Q n) z)).restrict
        (⋂ n, labelFiber (Q n) z)).real {t | (z.1,t) ∈ A} ∂ρ) = ρ.real (A ∩ E) := by
  let P : S × V → Fin 2 := fun z => if z ∈ A then 0 else 1
  have hP : Measurable P := measurable_const.piecewise hA measurable_const
  have hp (z : S × V) : P z = 0 ↔ z ∈ A := by simp [P]
  have heq : {z | P z = 0} = A := by ext z; exact hp z
  have heval (z : S × V) : {t | P (z.1,t)=0} = {t | (z.1,t) ∈ A} := by
    ext t
    exact hp (z.1,t)
  have hcond := condExp_infinite_label_probability ρ hP Q hQ hmono hdec hpos 0
  simp only [heq,heval] at hcond
  have hm : (⨆ n, transverseLabelSigma (Q n)) ≤ mS.prod mV := by
    apply iSup_le
    intro n
    exact (measurable_fst.prodMk (hQ n)).comap_le
  calc
    _ = ∫ z in E, ρ[A.indicator (fun _ => (1 : ℝ)) |
        ⨆ n, transverseLabelSigma (Q n)] z ∂ρ :=
      integral_congr_ae (ae_restrict_of_ae (Filter.EventuallyEq.symm hcond))
    _ = ∫ z in E, A.indicator (fun _ => (1 : ℝ)) z ∂ρ :=
      setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hA) hE
    _ = ρ.real (A ∩ E) := by
      simpa only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply hA] using
        (integral_indicator_const (μ := ρ.restrict E) (1 : ℝ) hA)

theorem setIntegral_countableFuture_conditional_probability
    {Y : Type*} [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0)
    (A : Set (S × V)) (hA : MeasurableSet A)
    (E : Set (S × V))
    (hE : MeasurableSet[⨆ m,
      transverseLabelSigma (fun z => countableFutureCode T Q m (F z))] E) :
    (∫ z in E,
      ((anchorNormalize (ρ.condKernel z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A} ∂ρ) = ρ.real (A ∩ E) := by
  simpa only [countableFutureFiber_eq_iInter] using
    setIntegral_infinite_label_conditional_probability ρ
      (fun m z => countableFutureCode T Q m (F z))
      (fun m => (countableFutureCode_measurable hT hQ m).comp hF)
      (transverse_countableFutureCode_monotone T Q F)
      (countableFutureCode_fibers_antitone T Q F)
      (by simpa only [countableFutureFiber_eq_iInter] using hpos) A hA E hE

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootLongBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Long boxes for the full positive-root group

The ordered root word is injective. Generic arithmetic lattices have
free upper unipotent orbits, so every compact set of full root times
fits into one actual quotient box containing the chosen basepoint.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem ae_upperRoot_stabilizer_trivial
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∀ g ∈ positiveRootGeneratedGroup (allPositiveRoots (d + 1)),
      rightAction x g = x → g = 1 := by
  filter_upwards [ae_positiveRootPattern_stabilizer_trivial d μ hA] with x hx g hg hfix
  exact hx (allPositiveRoots (d + 1)) (fun p hp => (Finset.mem_filter.mp hp).2) g
    (positiveRootGeneratedGroup_pattern _ (allPositiveRoots_closed _) hg) hfix

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient restrictions and null sets in the remaining-root quotient boxes -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem map_restricted_coordinates (B : RootPrefixBox C c hP hfinal g)
    (μ : Measure (X n)) (S : Set ((UpperRootTransverse n × T) × c.Time))
    (hS : MeasurableSet S) (hSB : S ⊆ B.domain) :
    ((B.coordinateMeasure μ).restrict S).map (C.timeParam c hP hfinal g) =
      μ.restrict (C.timeParam c hP hfinal g '' S) := by
  let V : Set B.domain := Subtype.val ⁻¹' S
  have hV : MeasurableSet V := measurable_subtype_coe hS
  have hv : MeasurableEmbedding (Subtype.val : B.domain → (UpperRootTransverse n × T) × c.Time) :=
    MeasurableEmbedding.subtype_coe (B.transverse_open.prod B.time_open).measurableSet
  have he := B.embedding.measurableEmbedding
  have hm := he.restrict_map (μ.comap B.param) (B.param '' V)
  rw [he.injective.preimage_image] at hm
  have hset : B.param '' V = C.timeParam c hP hfinal g '' S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hSB hz⟩,hz,rfl⟩
  have hsub : B.param '' V ⊆ B.range := image_subset_range _ _
  rw [he.map_comap,Measure.restrict_restrict (he.measurableSet_image.mpr hV)] at hm
  change μ.restrict ((B.param '' V) ∩ B.range) = ((μ.comap B.param).restrict V).map B.param at hm
  rw [inter_eq_left.mpr hsub] at hm
  rw [coordinateMeasure,hv.restrict_map,Measure.map_map]
  · change ((μ.comap B.param).restrict V).map B.param = _
    exact hm.symm.trans (congrArg (fun A => μ.restrict A) hset)
  · exact (C.timeParam_localHomeomorph c hP hfinal g).continuous.measurable
  · exact measurable_subtype_coe

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of support membership in a second-countable fiber -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology

namespace PrimeDegreePackets

lemma measurableSet_kernel_support_secondCountable
    {S T : Type*} [MeasurableSpace S] [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] [SecondCountableTopology T] (κ : Kernel S T) :
    MeasurableSet {z : S × T | z.2 ∈ (κ z.1).support} := by
  have hmem (s : S) (t : T) : t ∈ (κ s).support ↔
      ∀ U : countableBasis T, t ∈ U.val → 0 < κ s U.val := by
    simpa only [Subtype.forall, and_imp] using
      ((isBasis_countableBasis T).nhds_hasBasis (a := t)).mem_measureSupport (μ := κ s)
  have heq : {z : S × T | z.2 ∈ (κ z.1).support} =
      ⋂ U : countableBasis T, {z | z.2 ∈ U.val → 0 < κ z.1 U.val} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, hmem]
  rw [heq]
  apply MeasurableSet.iInter
  intro U
  have hU : MeasurableSet U.val := (isOpen_of_mem_countableBasis U.prop).measurableSet
  exact (measurable_snd hU).imp
    (measurableSet_lt measurable_const ((κ.measurable_coe hU).comp measurable_fst))

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing full upper-root coordinates at their current group point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootWord_zero (n : ℕ) :
    upperRootWordHomeomorph n (completeRootChain n).zeroTime = 1 := by
  apply Subtype.ext
  exact (completeRootChain n).word_zeroTime

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing a remaining-subgroup leaf at its current coordinate -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma remainingRebase_word (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t u : c.Time) :
    c.remainingWordHomeomorph hP hfinal (c.remainingRebase hP hfinal t u) =
      (c.remainingWordHomeomorph hP hfinal t)⁻¹ * c.remainingWordHomeomorph hP hfinal u :=
  (c.remainingWordHomeomorph hP hfinal).apply_symm_apply _

lemma remainingWord_zero (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    c.remainingWordHomeomorph hP hfinal c.zeroTime = 1 := by
  apply Subtype.ext
  exact c.word_zeroTime

lemma remainingRebase_self (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    c.remainingRebase hP hfinal t t = c.zeroTime := by
  apply (c.remainingWordHomeomorph hP hfinal).injective
  rw [c.remainingRebase_word,inv_mul_cancel,c.remainingWord_zero hP hfinal]

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixLeafKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable remaining-subgroup leaf kernels

The chosen leaf measure is measurable almost everywhere because its
restrictions to the countable exhausting windows are actual normalized
conditional kernels. This supplies a measurable kernel for integration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

lemma ae_leafKernel_eq (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.leafKernel R hAR μ hfree s = A.leafMeasure R μ s :=
  (A.aemeasurable_leafMeasure R hAR μ hfree).ae_eq_mk.symm


end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixRegularKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Everywhere locally finite versions of remaining-subgroup kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma locallyFinite_of_finite_remainingCubes (c : EliminationChain P D) (ν : Measure (c.Time))
    (hν : ∀ m : ℕ, ν (c.closedCube m) < ∞) : IsLocallyFiniteMeasure ν := by
  constructor
  intro t
  obtain ⟨m,hm⟩ := c.mem_cube_exists 0 t
  simp only [zero_add] at hm
  exact ⟨c.cube m, (c.cube_open m).mem_nhds hm,
    (measure_mono (c.cube_subset_closedCube m)).trans_lt (hν m)⟩

lemma locallyFiniteRemainingVersion_eq {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) (s : S) [IsLocallyFiniteMeasure (κ s)] :
    locallyFiniteRemainingVersion c κ s = κ s := by
  apply ite_eq_left
  intro m
  exact (c.closedCube_compact m).measure_lt_top

instance locallyFiniteRemainingVersion_locallyFinite {S : Type*} [MeasurableSpace S]
    (c : EliminationChain P D) (κ : Kernel S (c.Time)) (s : S) :
    IsLocallyFiniteMeasure (locallyFiniteRemainingVersion c κ s) := by
  change IsLocallyFiniteMeasure (if s ∈ finiteRemainingCubes c κ then κ s else 0)
  split_ifs with hs
  · exact locallyFinite_of_finite_remainingCubes c (κ s) hs
  · infer_instance

instance locallyFiniteRemainingVersion_sFinite {S : Type*} [MeasurableSpace S]
    (c : EliminationChain P D) (κ : Kernel S (c.Time)) :
    IsSFiniteKernel (locallyFiniteRemainingVersion c κ) := by
  apply isSFiniteKernel_of_finite_exhaustion _ (c.remainingWindow 0)
    (fun m => (c.remainingWindow_open 0 m).measurableSet) (c.remainingWindow_cover 0)
  intro s m
  have hsub : c.remainingWindow 0 m ⊆ c.closedCube m := by
    simpa only [EliminationChain.remainingWindow, zero_add] using c.cube_subset_closedCube m
  exact (measure_mono hsub).trans_lt (c.closedCube_compact m).measure_lt_top

namespace RootPrefixBox
variable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

instance regularLeafKernel_locallyFinite (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) (s : (UpperRootTransverse n × T)) :
    IsLocallyFiniteMeasure (A.regularLeafKernel R hAR μ hfree s) :=
  locallyFiniteRemainingVersion_locallyFinite _ _ _

instance regularLeafKernel_sFinite (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) : IsSFiniteKernel (A.regularLeafKernel R hAR μ hfree) :=
  locallyFiniteRemainingVersion_sFinite _ _

lemma ae_regularLeafKernel_eq (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.regularLeafKernel R hAR μ hfree s = A.leafMeasure R μ s := by
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree, A.ae_leafKernel_eq R hAR μ hfree]
    with s hs he
  have : IsLocallyFiniteMeasure (A.leafKernel R hAR μ hfree s) := he.symm ▸ hs.1
  exact (locallyFiniteRemainingVersion_eq _ _ s).trans he

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixBasedMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable remaining-subgroup leaves based at the sampled point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]

lemma timeParam_rebased (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (g : G n) (s : UpperRootTransverse n × T) (t u : c.Time) :
    C.timeParam c hP hfinal g (s,u) =
      rightAction (C.timeParam c hP hfinal g (s,t))
        (c.word (c.remainingRebase hP hfinal t u)) := by
  rw [C.timeParam_eq_action,C.timeParam_eq_action,rightAction_mul]
  congr 1
  have he := congrArg Subtype.val (c.remainingRebase_word hP hfinal t u)
  change c.word (c.remainingRebase hP hfinal t u) = (c.word t)⁻¹ * c.word u at he
  rw [he,mul_inv_cancel_left]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixFutureFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive future fibers for the remaining-root product charts -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma continuous_fullRootTime (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) : Continuous (c.fullRootTime hP hf) :=
  (upperRootWordHomeomorph n).symm.continuous.comp
    ((continuous_subtype_val.comp (c.remainingWordHomeomorph hP hf).continuous).subtype_mk _)

lemma fullRootTime_zero (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) :
    c.fullRootTime hP hf c.zeroTime = (completeRootChain n).zeroTime := by
  apply (upperRootWordHomeomorph n).injective
  rw [fullRootTime,Homeomorph.apply_symm_apply,upperRootWord_zero]
  apply Subtype.ext
  exact c.word_zeroTime

lemma word_fullRootTime (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    (completeRootChain n).word (c.fullRootTime hP hf t) = c.word t :=
  congrArg Subtype.val ((upperRootWordHomeomorph n).apply_symm_apply _)

end EliminationChain

namespace RootPrefixBox
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  {C : RootPrefixCoordinates n P₀ V} {c : EliminationChain P₀ D}
  {hP₀ : InitialRootPattern P₀} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

omit [SecondCountableTopology V] in
theorem ae_mem_conditionalKernel_support (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ z ∂B.coordinateMeasure μ, z.2 ∈ (B.conditionalKernel μ z.1).support := by
  have H : ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ (B.conditionalKernel μ s).support :=
    ae_of_all _ fun s => (B.conditionalKernel μ s).support_mem_ae
  have H' := Measure.ae_compProd_of_ae_ae
    (measurableSet_kernel_support_secondCountable (B.conditionalKernel μ)) H
  simpa only [conditionalKernel,Measure.disintegrate] using H'

end RootPrefixBox

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CountableRootPrefixAtoms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive leaf mass of countable whole-future atoms

The argument uses support of the actual conditional leaf kernel. No finite
entropy of the countable observation is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V A : Type*} [TopologicalSpace V]

theorem wholeFutureAtom_mem_nhds (C : RootPrefixCoordinates n P₀ V)
    (c : EliminationChain P₀ D) (hP₀ : InitialRootPattern P₀)
    (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    (T : X n → X n) (Q : X n → A)
    (z : (UpperRootTransverse n × V) × c.Time)
    (hgood : ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction (C.timeParam c hP₀ hf g z) ((completeRootChain n).word v))) =
        Q (T^[k] (C.timeParam c hP₀ hf g z))) :
    {t | ∀ k : ℕ, Q (T^[k] (C.timeParam c hP₀ hf g (z.1,t))) =
      Q (T^[k] (C.timeParam c hP₀ hf g z))} ∈ 𝓝 z.2 := by
  have hc : Tendsto (c.fullRootTime hP₀ hf ∘ c.remainingRebase hP₀ hf z.2)
      (𝓝 z.2) (𝓝 (completeRootChain n).zeroTime) := by
    have H := ((c.continuous_fullRootTime hP₀ hf).comp
      (c.remainingRebase hP₀ hf z.2).continuous).tendsto z.2
    simpa only [Function.comp_apply,c.remainingRebase_self,c.fullRootTime_zero] using H
  filter_upwards [hc.eventually hgood] with t ht
  intro k
  rw [Function.comp_apply,c.word_fullRootTime] at ht
  rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
  exact ht k

end RootPrefixCoordinates

namespace RootPrefixBox
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V A : Type*} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  {C : RootPrefixCoordinates n P₀ V} {c : EliminationChain P₀ D}
  {hP₀ : InitialRootPattern P₀} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

omit [SecondCountableTopology V] in
theorem ae_wholeFutureAtom_pos (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (T : X n → X n) (Q : X n → A)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain n).word v))) = Q (T^[k] x)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, 0 < B.conditionalKernel μ z.1
      {t | ∀ k : ℕ, Q (T^[k] (C.timeParam c hP₀ hf g (z.1,t))) =
        Q (T^[k] (C.timeParam c hP₀ hf g z))} := by
  filter_upwards [B.ae_coordinate_of_ambient μ hgood,B.ae_mem_conditionalKernel_support μ]
    with z hz hs
  apply ((B.conditionalKernel μ z.1).mem_support_iff_forall z.2).mp hs
  exact C.wholeFutureAtom_mem_nhds c hP₀ hf g T Q z hz

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixIntrinsicCandidates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From intrinsic long-box leaves to an actual regional conditional kernel -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n)

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
theorem timeParam_injective_of_free_at_coordinate
    (z : (UpperRootTransverse n × T) × c.Time)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (C.timeParam c hP hf g z) v = C.timeParam c hP hf g z → v = 1) :
    Function.Injective (fun t => C.timeParam c hP hf g (z.1,t)) := by
  apply C.timeParam_injective_of_free c hP hf g z.1
  apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots n))
    (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) (c.word z.2)
    (positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hf z.2))
  simpa only [C.timeParam_eq_action] using hfree

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixFutureMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing the actual intrinsic masses in a root box -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma uncenteredIntrinsicProduct_eq_rebase_map
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    B.uncenteredIntrinsicProduct μ z =
      (c.remainingTimeProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map
        (c.remainingRebase hP₀ hf z.2).symm := by
  let W := c.remainingWordHomeomorph hP₀ hf
  let E := c.remainingRebase hP₀ hf z.2
  change ((c.remainingIntrinsicProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map
    (Homeomorph.mulLeft (W z.2))).map W.symm =
    ((c.remainingIntrinsicProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map W.symm).map E.symm
  rw [Measure.map_map W.symm.measurable (Homeomorph.mulLeft (W z.2)).measurable,
    Measure.map_map E.symm.measurable W.symm.measurable]
  congr 1
  funext v
  apply E.injective
  rw [Function.comp_apply, Function.comp_apply, E.apply_symm_apply]
  apply W.injective
  rw [c.remainingRebase_word hP₀ hf, W.apply_symm_apply, W.apply_symm_apply]
  exact inv_mul_cancel_left (W z.2) v

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma rebase_image_futureFiber
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (m : ℕ) (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    (c.remainingRebase hP₀ hf z.2) ''
      {t | ∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g (z.1,t))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g z))} =
      c.remainingFutureAtom ell hell Q m (C.timeParam c hP₀ hf g z) := by
  let E := c.remainingRebase hP₀ hf z.2
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩ k
    rw [← C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
    exact ht k
  · intro hu
    refine ⟨E.symm u, ?_, E.apply_symm_apply u⟩
    intro k
    rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 (E.symm u)]
    change Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
      (rightAction (C.timeParam c hP₀ hf g z) (c.word (E (E.symm u))))) = _
    rw [E.apply_symm_apply]
    exact hu k

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixAmbientFuture
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matching box future conditionals with ambient root-orbit measures -/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_map_equiv {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (e : Y ≃ᵐ Z) (A : Set Y) :
    ((anchorNormalize ν A).restrict A).map e =
      (anchorNormalize (ν.map e) (e '' A)).restrict (e '' A) := by
  rw [anchorNormalize_map_equiv, e.measurableEmbedding.restrict_map,
    e.preimage_image]

namespace RootPrefixBox
variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
/-- The box expression, once unrestricted, is exactly the intrinsic
whole-future measure pushed along the actual root orbit through its sample. -/
lemma map_uncentered_future_eq_ambient
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (m : ℕ) (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP₀ hf g
    let A := {t | ∀ k : ℕ, Q (T^[k+m] (F (z.1,t)))=Q (T^[k+m] (F z))}
    ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) A).restrict A).map
        (fun t => F (z.1,t)) =
      ((anchorNormalize (c.remainingTimeProduct hP₀ hf μ (F z))
        (c.remainingFutureAtom ell hell Q m (F z))).restrict
        (c.remainingFutureAtom ell hell Q m (F z))).map
        (fun u => rightAction (F z) (c.word u)) := by
  let F := C.timeParam c hP₀ hf g
  let E := (c.remainingRebase hP₀ hf z.2).toMeasurableEquiv
  let A := {t | ∀ k : ℕ,
    Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m] (F (z.1,t))) =
    Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m] (F z))}
  let W := fun u => rightAction (F z) (c.word u)
  have hW : Measurable W :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hF : (fun t => F (z.1,t)) = W ∘ E := by
    funext t
    exact C.timeParam_rebased c hP₀ hf g z.1 z.2 t
  have hM : (B.uncenteredIntrinsicProduct μ z).map E =
      c.remainingTimeProduct hP₀ hf μ (F z) := by
    rw [B.uncenteredIntrinsicProduct_eq_rebase_map μ z]
    exact E.map_map_symm
  change ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) A).restrict A).map
    (fun t => F (z.1,t)) = _
  rw [hF, ←Measure.map_map hW E.measurable,
    normalized_restriction_map_equiv, hM]
  rw [show E '' A = c.remainingFutureAtom ell hell Q m (F z) from
    rebase_image_futureFiber ell hell Q m z]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureCountableCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable family of boxes containing complete future fibers

The family is chosen before the sample. Bounded future fibers, transported
to the sampled coordinates, fit into one member of this fixed family.
This is the countability needed for gluing the local future laws.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]

theorem exists_countable_box_containing_futureFiber
    (C : RootPrefixCoordinates n P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    (s : UpperRootTransverse n × V) (t : c.Time)
    (hinj : Function.Injective (fun u => C.timeParam c hP hf g (s,u)))
    (T : X n → X n) (Q : X n → ℕ) (m : ℕ) (R : ℝ)
    (hbound : ∀ v : c.Time,
      (∀ k : ℕ, Q (T^[k+m] (rightAction (C.timeParam c hP hf g (s,t)) (c.word v))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))) → v ∈ c.cube R) :
    ∃ B ∈ C.wholeFutureBoxFamily c hP hf g,
      s ∈ B.transverse ∧ t ∈ B.time ∧
      ∃ j : ℕ, B.time = c.cube (1+j) ∧
      {u | ∀ k : ℕ, Q (T^[k+m] (C.timeParam c hP hf g (s,u))) =
        Q (T^[k+m] (C.timeParam c hP hf g (s,t)))} ⊆ B.time := by
  let E := c.remainingRebase hP hf t
  let K : Set c.Time := {t} ∪ E.symm '' c.closedCube R
  have hK : IsCompact K := isCompact_singleton.union
    ((c.closedCube_compact R).image E.symm.continuous)
  obtain ⟨j,hj⟩ := hK.elim_directed_cover (c.remainingWindow 1)
    (c.remainingWindow_open 1) (by rw [c.remainingWindow_cover]; exact subset_univ K)
    (c.remainingWindow_mono 1).directed_le
  obtain ⟨B,hB,hs⟩ := C.longBoxFamily_covers c hP hf g 1 j s hinj
  have htime := C.longBoxFamily_time c hP hf g 1 j B hB
  refine ⟨B, mem_iUnion.mpr ⟨j,hB⟩, hs, ?_, j, htime, ?_⟩
  · rw [htime]
    exact hj (Or.inl rfl)
  · intro u hu
    rw [htime]
    apply hj
    have hv : E u ∈ c.cube R := by
      apply hbound
      intro k
      rw [← C.timeParam_rebased c hP hf g s t u]
      exact hu k
    exact Or.inr ⟨E u,c.cube_subset_closedCube R hv,E.symm_apply_apply u⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixCountableAtlas
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.regularLeafKernel_locallyFinite _root_.OAI.DukePrimeDegree.RootPrefixBox.regularLeafKernel_sFinite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.locallyFiniteRemainingVersion_locallyFinite _root_.OAI.DukePrimeDegree.locallyFiniteRemainingVersion_sFinite _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countably many translated root charts cover the quotient -/

noncomputable section
open Set TopologicalSpace

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V]

theorem exists_countable_translates_cover (C : RootPrefixCoordinates n P V)
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n)
    (z₀ : (UpperRootTransverse n × V) × c.Time) :
    ∃ S : Set (G n), S.Countable ∧
      (⋃ g ∈ S, range (C.timeParam c hP hf g)) = univ := by
  have hopen g : IsOpen (range (C.timeParam c hP hf g)) :=
    (C.timeParam_localHomeomorph c hP hf g).isOpenMap.isOpen_range
  obtain ⟨S,_,hS,heq⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => range (C.timeParam c hP hf g)) (fun g _ => hopen g)
  refine ⟨S,hS,heq.trans ?_⟩
  apply eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | _ a =>
    let b := C.groupParam (z₀.1.1,(z₀.1.2,c.remainingWordHomeomorph hP hf z₀.2))
    refine mem_iUnion.mpr ⟨a*b⁻¹,mem_iUnion.mpr ⟨mem_univ _,z₀,?_⟩⟩
    change Quotient.mk _ ((a*b⁻¹)*b) = Quotient.mk _ a
    simp only [inv_mul_cancel_right]

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixNullStationarity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Future stationarity on measurable mass-containment events

A box restriction can be removed when the transverse leaf measure of
the future outside that box vanishes. This event belongs to the future
sigma algebra; no literal containment of the full fiber is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

theorem setIntegral_regularLeaf_wholeFuture_probability
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v))) = Q (T^[k] x))
    (E : Set ((UpperRootTransverse (d+1) × V) × c.Time))
    (hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (C.timeParam c hP hf g z))] E)
    (hnull : ∀ᵐ z ∂(B.coordinateMeasure μ).restrict E,
      B.regularLeafKernel R hBR μ hfree z.1
        (countableFutureFiber T Q (C.timeParam c hP hf g) z \ B.time) = 0)
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    (∫ z in E,
      ((anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1)
        (countableFutureFiber T Q (C.timeParam c hP hf g) z)).restrict
        (countableFutureFiber T Q (C.timeParam c hP hf g) z)).real
          {t | (z.1,t) ∈ A} ∂B.coordinateMeasure μ) =
      (B.coordinateMeasure μ).real (A ∩ E) := by
  let F := C.timeParam c hP hf g
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hpos : ∀ᵐ z ∂B.coordinateMeasure μ,
      (B.coordinateMeasure μ).condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    exact ne_of_gt (hz.trans_le (measure_mono (fun t ht k => ht (k+1))))
  have H := setIntegral_countableFuture_conditional_probability
    (B.coordinateMeasure μ) hQ hT hF hpos A hA E hE
  have hs := ae_of_ae_map measurable_fst.aemeasurable (B.ae_leafMeasure_spec R hBR μ hfree)
  have hk := ae_of_ae_map measurable_fst.aemeasurable (B.ae_regularLeafKernel_eq R hBR μ hfree)
  refine (integral_congr_ae ?_).trans H
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_of_ae hk, hnull] with z hs hk hn
  have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
    simp only [countableFutureFiber, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_eq_fun
      (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
  have htime : MeasurableSet B.time := B.time_open.measurableSet
  have hmass : B.regularLeafKernel R hBR μ hfree z.1 B.time = 1 := by
    rw [hk]
    exact hs.2.1
  have hc : (B.coordinateMeasure μ).condKernel z.1 =
      (anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1) B.time).restrict B.time := by
    change B.conditionalKernel μ z.1 = _
    rw [hk]
    simpa only [anchorNormalize, hs.2.1, inv_one, one_smul] using hs.2.2.1.symm
  rw [hc, normalized_restriction_of_null_diff _ _ _ hfuture htime
    (by rw [hmass]; exact one_ne_zero) (by rw [hmass]; exact ENNReal.one_ne_top) hn]

/-- Apply the local law directly on its canonical mass-containment
event. Its measurability and the null-outside-box premise are proved. -/
theorem setIntegral_massContained_wholeFuture_probability
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v))) = Q (T^[k] x))
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    let F := C.timeParam c hP hf g
    let κ := B.regularLeafKernel R hBR μ hfree
    let E := {z | κ z.1 (countableFutureFiber T Q F z \ B.time) = 0}
    (∫ z in E,
      ((anchorNormalize (κ z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A} ∂B.coordinateMeasure μ) =
      (B.coordinateMeasure μ).real (A ∩ E) := by
  let F := C.timeParam c hP hf g
  let κ := B.regularLeafKernel R hBR μ hfree
  let E := {z | κ z.1 (countableFutureFiber T Q F z \ B.time) = 0}
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E :=
    measurableSet_future_mass_contained κ hT hQ hF B.time B.time_open.measurableSet
  have hEle : (⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))) ≤
        (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
    apply iSup_le
    intro m
    exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
  exact B.setIntegral_regularLeaf_wholeFuture_probability R hBR μ hfree hQ hT hgood E hE
    (ae_restrict_mem (hEle E hE)) A hA

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_StationaryRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

private lemma bind_kernel_mono (κ : Kernel Y Y) {μ ν : Measure Y} (h : μ ≤ ν) :
    μ.bind κ ≤ ν.bind κ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA κ.measurable.aemeasurable,
    Measure.bind_apply hA κ.measurable.aemeasurable]
  exact lintegral_mono' h le_rfl

private lemma bind_kernel_add (κ : Kernel Y Y) (μ ν : Measure Y) :
    (μ+ν).bind κ = μ.bind κ + ν.bind κ := by
  ext A hA
  simp only [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.add_apply,
    lintegral_add_measure]

private lemma bind_kernel_univ (κ : Kernel Y Y) [IsMarkovKernel κ] (μ : Measure Y) :
    μ.bind κ univ = μ univ := by
  rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]
  simp only [measure_univ, lintegral_const, one_mul]

theorem bind_kernel_real (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) (A : Set Y) (hA : MeasurableSet A) :
    (μ.bind κ).real A = ∫ y, (κ y).real A ∂μ := by
  rw [Measure.real, Measure.bind_apply hA κ.measurable.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Filter.Eventually.of_forall fun y => measure_lt_top (κ y) A)).symm

theorem bind_eq_of_real_integrals (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (h : ∀ A, MeasurableSet A → (∫ y, (κ y).real A ∂μ) = μ.real A) :
    μ.bind κ = μ := by
  let : IsFiniteMeasure (μ.bind κ) :=
    ⟨by rw [bind_kernel_univ]; exact measure_lt_top μ univ⟩
  ext A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.bind κ).real A = μ.real A
  rw [bind_kernel_real κ μ A hA]
  exact h A hA

theorem stationary_restrict_inter (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (E F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hsE : (μ.restrict E).bind κ = μ.restrict E)
    (hsF : (μ.restrict F).bind κ = μ.restrict F) :
    (μ.restrict (E ∩ F)).bind κ = μ.restrict (E ∩ F) := by
  let ν := (μ.restrict (E ∩ F)).bind κ
  have hνE : ν ≤ μ.restrict E := by
    simpa only [ν, hsE] using bind_kernel_mono κ
      (Measure.restrict_mono_set μ (inter_subset_left : E ∩ F ⊆ E))
  have hνF : ν ≤ μ.restrict F := by
    simpa only [ν, hsF] using bind_kernel_mono κ
      (Measure.restrict_mono_set μ (inter_subset_right : E ∩ F ⊆ F))
  have hmem : ∀ᵐ y ∂ν, y ∈ E ∩ F := by
    filter_upwards [(ae_mono hνE) (ae_restrict_mem hE),
      (ae_mono hνF) (ae_restrict_mem hF)] with y hyE hyF
    exact ⟨hyE,hyF⟩
  have hν : ν ≤ μ.restrict (E ∩ F) := by
    have H := Measure.restrict_mono_measure (hνE.trans Measure.restrict_le_self) (E ∩ F)
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at H
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le (μ.restrict (E ∩ F)) hν
  exact Measure.eq_of_le_of_measure_univ_eq hν (bind_kernel_univ κ _)

theorem stationary_restrict_union (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (E F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hsE : (μ.restrict E).bind κ = μ.restrict E)
    (hsF : (μ.restrict F).bind κ = μ.restrict F) :
    (μ.restrict (E ∪ F)).bind κ = μ.restrict (E ∪ F) := by
  have hsI := stationary_restrict_inter κ μ E F hE hF hsE hsF
  have hsum := Measure.restrict_union_add_inter (μ := μ) E hF
  have H := congrArg (fun ν : Measure Y => ν.bind κ) hsum
  rw [bind_kernel_add, bind_kernel_add, hsI, hsE, hsF] at H
  have H' : μ.restrict (E ∩ F) + (μ.restrict (E ∪ F)).bind κ =
      μ.restrict (E ∩ F) + μ.restrict (E ∪ F) := by
    simpa only [add_comm] using H.trans hsum.symm
  exact le_antisymm (Measure.le_of_add_le_add_left H'.le)
    (Measure.le_of_add_le_add_left H'.ge)

theorem stationary_restrict_iUnion_of_monotone (κ : Kernel Y Y)
    (μ : Measure Y) (E : ℕ → Set Y) (hE : ∀ n, MeasurableSet (E n)) (hm : Monotone E)
    (hs : ∀ n, (μ.restrict (E n)).bind κ = μ.restrict (E n)) :
    (μ.restrict (⋃ n, E n)).bind κ = μ.restrict (⋃ n, E n) := by
  ext A hA
  let f := fun n => (E n).indicator (fun y => κ y A)
  have hf n : Measurable (f n) := (κ.measurable_coe hA).indicator (hE n)
  have hfm : Monotone f := by
    intro i j hij y
    exact Set.indicator_le_indicator_of_subset (hm hij) (fun _ => bot_le) y
  have he : (fun y => ⨆ n, f n y) = (⋃ n, E n).indicator (fun y => κ y A) := by
    funext y
    by_cases hy : y ∈ ⋃ n, E n
    · rw [Set.indicator_of_mem hy]
      apply le_antisymm
      · exact iSup_le fun n => Set.indicator_le_self (E n) (fun y => κ y A) y
      · obtain ⟨n,hn⟩ := mem_iUnion.mp hy
        exact le_iSup_of_le n (by dsimp only [f]; rw [Set.indicator_of_mem hn])
    · have hy' n : y ∉ E n := fun hn => hy (mem_iUnion.mpr ⟨n,hn⟩)
      have hz n : f n y = 0 := by
        dsimp only [f]
        rw [Set.indicator_of_notMem (hy' n)]
      simp only [hz, iSup_const, Set.indicator_of_notMem hy]
  rw [Measure.bind_apply hA κ.measurable.aemeasurable,
    ←lintegral_indicator (MeasurableSet.iUnion hE), ←he, lintegral_iSup hf hfm]
  simp only [f, lintegral_indicator (hE _),
    ←Measure.bind_apply hA κ.measurable.aemeasurable, hs]
  exact (Measure.restrict_iUnion_apply_eq_iSup hm.directed_le hA).symm

/-- The local restrictions must use the same actual Markov kernel.
No global stationarity hypothesis is used. -/
theorem stationary_of_countable_restrictions (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (E : ℕ → Set Y) (hE : ∀ n, MeasurableSet (E n))
    (hcover : ∀ᵐ y ∂μ, y ∈ ⋃ n, E n)
    (hs : ∀ n, (μ.restrict (E n)).bind κ = μ.restrict (E n)) :
    μ.bind κ = μ := by
  have hpartial n : MeasurableSet (partialSups E n) ∧
      (μ.restrict (partialSups E n)).bind κ = μ.restrict (partialSups E n) := by
    induction n with
    | zero => simpa only [partialSups_zero] using And.intro (hE 0) (hs 0)
    | succ n ih =>
      rw [partialSups_add_one]
      exact ⟨ih.1.union (hE (n+1)),
        stationary_restrict_union κ μ _ _ ih.1 (hE (n+1)) ih.2 (hs (n+1))⟩
  have H := stationary_restrict_iUnion_of_monotone κ μ (partialSups E)
    (fun n => (hpartial n).1) (partialSups_monotone E) (fun n => (hpartial n).2)
  have he : (⋃ n, partialSups E n) = ⋃ n, E n := iSup_partialSups_eq E
  rw [he, Measure.restrict_eq_self_of_ae_mem hcover] at H
  exact H

/-- The cover may use any countable index type, including a countable
family of quotient charts with different coordinate domains. -/
theorem stationary_of_countable_indexed_restrictions {ι : Type*} [Countable ι]
    (κ : Kernel Y Y) [IsMarkovKernel κ] (μ : Measure Y) [IsFiniteMeasure μ]
    (E : ι → Set Y) (hE : ∀ i, MeasurableSet (E i))
    (hcover : ∀ᵐ y ∂μ, y ∈ ⋃ i, E i)
    (hs : ∀ i, (μ.restrict (E i)).bind κ = μ.restrict (E i)) :
    μ.bind κ = μ := by
  let := Encodable.ofCountable ι
  let F := fun n => ⋃ i ∈ Encodable.decode₂ ι n, E i
  have hF n : MeasurableSet (F n) ∧
      (μ.restrict (F n)).bind κ = μ.restrict (F n) := by
    exact Encodable.iUnion_decode₂_cases
      (C := fun S => MeasurableSet S ∧ (μ.restrict S).bind κ = μ.restrict S)
      (by simp) (fun i => ⟨hE i,hs i⟩)
  apply stationary_of_countable_restrictions κ μ F (fun n => (hF n).1) _
    (fun n => (hF n).2)
  simpa only [F, Encodable.iUnion_decode₂] using hcover

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixStationaryImages
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.regularLeafKernel_locallyFinite _root_.OAI.DukePrimeDegree.RootPrefixBox.regularLeafKernel_sFinite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.locallyFiniteRemainingVersion_locallyFinite _root_.OAI.DukePrimeDegree.locallyFiniteRemainingVersion_sFinite _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring local stationarity through actual quotient boxes

The image restriction is the pushforward of the coordinate restriction.
Consequently a local integral identity for one ambient Markov kernel gives
a stationary restriction of the original ambient measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates n P V} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem measurableSet_param_image
    (B : RootPrefixBox C c hP hf g)
    (S : Set ((UpperRootTransverse n × V) × c.Time))
    (hS : MeasurableSet S) (hSB : S ⊆ B.domain) :
    MeasurableSet (C.timeParam c hP hf g '' S) := by
  have he : B.param '' (Subtype.val ⁻¹' S) = C.timeParam c hP hf g '' S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hSB hz⟩,hz,rfl⟩
  rw [←he]
  exact B.embedding.measurableEmbedding.measurableSet_image.mpr
    (hS.preimage measurable_subtype_coe)

theorem stationary_image_of_local_integrals
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (κ : Kernel (X n) (X n)) [IsMarkovKernel κ]
    (S : Set ((UpperRootTransverse n × V) × c.Time))
    (hS : MeasurableSet S) (hSB : S ⊆ B.domain)
    (h : ∀ A, MeasurableSet A →
      (∫ z in S, (κ (C.timeParam c hP hf g z)).real A ∂B.coordinateMeasure μ) =
        (B.coordinateMeasure μ).real ((C.timeParam c hP hf g ⁻¹' A) ∩ S)) :
    (μ.restrict (C.timeParam c hP hf g '' S)).bind κ =
      μ.restrict (C.timeParam c hP hf g '' S) := by
  let F := C.timeParam c hP hf g
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hm := B.map_restricted_coordinates μ S hS hSB
  apply bind_eq_of_real_integrals κ
  intro A hA
  rw [← hm]
  change (∫ y, (κ y).real A ∂((B.coordinateMeasure μ).restrict S).map F) = _
  rw [integral_map hF.aemeasurable (f := fun y => (κ y).real A)
    (κ.measurable_coe hA).ennreal_toReal.aestronglyMeasurable]
  change (∫ z in S, (κ (F z)).real A ∂B.coordinateMeasure μ) = _
  rw [h A hA]
  exact congrArg ENNReal.toReal
    (Measure.map_apply hF hA |>.trans (Measure.restrict_apply (hA.preimage hF))).symm

theorem stationary_image_of_local_event
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (κ : Kernel (X n) (X n)) [IsMarkovKernel κ]
    (E : Set ((UpperRootTransverse n × V) × c.Time)) (hE : MeasurableSet E)
    (h : ∀ A, MeasurableSet A →
      (∫ z in E, (κ (C.timeParam c hP hf g z)).real A ∂B.coordinateMeasure μ) =
        (B.coordinateMeasure μ).real ((C.timeParam c hP hf g ⁻¹' A) ∩ E)) :
    (μ.restrict (C.timeParam c hP hf g '' (E ∩ B.domain))).bind κ =
      μ.restrict (C.timeParam c hP hf g '' (E ∩ B.domain)) := by
  have hdom := B.coordinateMeasure_ae_domain μ
  have heq : (B.coordinateMeasure μ).restrict (E ∩ B.domain) =
      (B.coordinateMeasure μ).restrict E := by
    apply Measure.restrict_congr_set
    filter_upwards [hdom] with z hz
    exact propext ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩
  apply B.stationary_image_of_local_integrals μ κ (E ∩ B.domain)
    (hE.inter (B.transverse_open.prod B.time_open).measurableSet) inter_subset_right
  intro A hA
  rw [heq]
  rw [h A hA]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hdom] with z hz
  exact propext ⟨fun h => ⟨h.1, h.2, hz⟩, fun h => ⟨h.1, h.2.1⟩⟩

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixNullAmbient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient stationarity on local mass-containment events -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

theorem stationary_image_massContained
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hκ : ∀ᵐ x ∂μ, κ x =
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP hf g
    let E := {z | B.regularLeafKernel R hBR μ hfree z.1
      (countableFutureFiber T Q F z \ B.time) = 0}
    (μ.restrict (F '' (E ∩ B.domain))).bind κ =
      μ.restrict (F '' (E ∩ B.domain)) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP hf g
  let K := B.regularLeafKernel R hBR μ hfree
  let E := {z | K z.1 (countableFutureFiber T Q F z \ B.time) = 0}
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hE : MeasurableSet E := by
    have he := measurableSet_future_mass_contained K hT hQ hF B.time
      B.time_open.measurableSet
    have hle : (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) ≤
        (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
      apply iSup_le
      intro m
      exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
    exact hle E he
  apply B.stationary_image_of_local_event μ κ E hE
  intro A hA
  have H := B.setIntegral_massContained_wholeFuture_probability R hBR μ hfree hQ hT
    hgood (F ⁻¹' A) (hA.preimage hF)
  refine (integral_congr_ae ?_).trans H
  have hka := B.ae_coordinate_of_ambient μ hκ
  have hnorm := B.ae_normalized_uncentered_eq_regularLeaf R hBR μ hfree
  filter_upwards [ae_restrict_of_ae hka, ae_restrict_of_ae hnorm] with z hz hn
  rw [hz, ← B.map_uncentered_future_eq_ambient μ ell hell Q 1 z]
  change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
    (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).map
      (fun t => F (z.1,t))).real A = _
  rw [hn]
  exact congrArg ENNReal.toReal (Measure.map_apply
    (show Measurable (fun t => F (z.1,t)) from hF.comp measurable_prodMk_left) hA)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureStationarity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global stationarity of the actual whole-future kernel

The countable family of genuine quotient boxes covers each bounded
future fiber. Local mass-containment events therefore cover almost every
point, and their stationary restrictions glue to the ambient measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]

theorem wholeFutureKernel_stationary_oai
    (C : RootPrefixCoordinates (d+1) P V) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots (d+1))
    (z₀ : (UpperRootTransverse (d+1) × V) × c.Time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (hbound : ∀ᵐ x ∂μ, ∃ R : ℝ, ∀ v : c.Time,
      (∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1]
          (rightAction x (c.word v))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+1] x)) →
      v ∈ c.cube R)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hκ : ∀ᵐ x ∂μ, κ x =
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    μ.bind κ = μ := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hfree := ae_upperRoot_stabilizer_trivial d μ hA
  obtain ⟨S,hS,hcover⟩ := C.exists_countable_translates_cover c hP hf z₀
  let : Countable S := hS.to_subtype
  let (g : S) (j : ℕ) : Countable
      {B : RootPrefixBox C c hP hf g.val // B ∈ C.longBoxFamily c hP hf g.val 1 j} :=
    (C.longBoxFamily_countable c hP hf g.val 1 j).to_subtype
  let I := Σ g : S, Σ j : ℕ,
    {B : RootPrefixBox C c hP hf g.val // B ∈ C.longBoxFamily c hP hf g.val 1 j}
  let B (i : I) := i.2.2.val
  let F (i : I) := C.timeParam c hP hf i.1.val
  have hBR (i : I) : (B i).time ⊆ c.remainingWindow (1+i.2.1) 0 := by
    rw [C.longBoxFamily_time c hP hf i.1.val 1 i.2.1 (B i) i.2.2.prop]
    simp only [EliminationChain.remainingWindow, Nat.cast_zero, add_zero, subset_refl]
  let K (i : I) := (B i).regularLeafKernel (1+i.2.1) (hBR i) μ hfree
  let E (i : I) := {z | K i z.1 (countableFutureFiber T Q (F i) z \ (B i).time) = 0}
  let A (i : I) := F i '' (E i ∩ (B i).domain)
  have hE (i : I) : MeasurableSet (E i) := by
    have hF : Measurable (F i) :=
      (C.timeParam_localHomeomorph c hP hf i.1.val).continuous.measurable
    have he := measurableSet_future_mass_contained (K i) hT hQ hF (B i).time
      (B i).time_open.measurableSet
    have hle : (⨆ m, transverseLabelSigma
        (fun z => countableFutureCode T Q m (F i z))) ≤
        (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
      apply iSup_le
      intro m
      exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
    exact hle (E i) he
  apply stationary_of_countable_indexed_restrictions κ μ A
  · intro i
    exact (B i).measurableSet_param_image _
      ((hE i).inter ((B i).transverse_open.prod (B i).time_open).measurableSet)
      inter_subset_right
  · filter_upwards [hfree,hbound] with x hx hb
    have hc : x ∈ ⋃ g ∈ S, range (C.timeParam c hP hf g) := by rw [hcover]; trivial
    obtain ⟨g,hg,z,hz⟩ := by simpa only [mem_iUnion,mem_range] using hc
    have hi := C.timeParam_injective_of_free_at_coordinate c hP hf g z (by simpa [hz] using hx)
    obtain ⟨R,hR⟩ := hb
    obtain ⟨B',hB',hs,ht,j,hj,hfuture⟩ :=
      C.exists_countable_box_containing_futureFiber c hP hf g z.1 z.2 hi T Q 1 R
        (by simpa [T,hz] using hR)
    obtain ⟨j',hj'⟩ := mem_iUnion.mp hB'
    let i : I := ⟨⟨g,hg⟩,j',⟨B',hj'⟩⟩
    apply mem_iUnion.mpr ⟨i,?_⟩
    refine ⟨z,⟨?_,hs,ht⟩,hz⟩
    change K i z.1 (countableFutureFiber T Q (C.timeParam c hP hf g) z \ B'.time) = 0
    have hsub : countableFutureFiber T Q (C.timeParam c hP hf g) z ⊆ B'.time := hfuture
    rw [sdiff_eq_empty.mpr hsub,measure_empty]
  · intro i
    exact (B i).stationary_image_massContained (1+i.2.1) (hBR i) μ hfree ell hell Q hQ
      hgood κ hκ

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureKernel_stationary_oai.{u_1} := @OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureKernel_stationary_oai.{u_1}
