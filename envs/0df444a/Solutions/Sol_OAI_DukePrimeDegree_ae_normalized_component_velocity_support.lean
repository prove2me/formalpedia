-- Prove2me | solution 1 for OAI.DukePrimeDegree.ae_normalized_component_velocity_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:30.791491+00:00
-- url     : https://prove2.me/submissions/e2589e08-933a-447c-8287-cd3c3f24f521

import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.GramMatrix
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
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
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
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_DiagonalRecurrence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing of expanding scalar coordinates in a finite invariant law

This is the scalar step in diagonal recurrence on projective or
Grassmannian coordinates. Bounded monotone truncation avoids assuming
that the original coordinate is integrable. It will be applied to ratios
of unequal diagonal weights; no stabilizer or orbit conclusion is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree

lemma boundedAbsCoordinate_nonneg (x : ℝ) : 0 ≤ boundedAbsCoordinate x :=
  div_nonneg (abs_nonneg x) (by positivity)

lemma boundedAbsCoordinate_le_one (x : ℝ) : boundedAbsCoordinate x ≤ 1 := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + |x|)).mpr
  nlinarith [abs_nonneg x]

lemma boundedAbsCoordinate_mono {x y : ℝ} (h : |x| ≤ |y|) :
    boundedAbsCoordinate x ≤ boundedAbsCoordinate y := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + |x|)
    (by positivity : 0 < 1 + |y|)).mpr
  nlinarith

lemma boundedAbsCoordinate_strictMono {x y : ℝ} (h : |x| < |y|) :
    boundedAbsCoordinate x < boundedAbsCoordinate y := by
  apply (div_lt_div_iff₀ (by positivity : 0 < 1 + |x|)
    (by positivity : 0 < 1 + |y|)).mpr
  nlinarith

/-- An a.e. expanding scalar coordinate must vanish under a finite
invariant measure. The scalar coordinate itself need not be integrable. -/
theorem ae_eq_zero_of_expanding_covariance
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (f : Y → ℝ) (hf : Measurable f) (c : ℝ) (hc : 1 < c)
    (hcov : (fun x => f (T x)) =ᵐ[μ] fun x => c * f x) :
    f =ᵐ[μ] 0 := by
  let g : Y → ℝ := fun x => boundedAbsCoordinate (f x)
  have hc0 : 0 < c := zero_lt_one.trans hc
  have habs : Measurable (fun x => |f x|) := continuous_abs.measurable.comp hf
  have hgm : Measurable g := habs.div (measurable_const.add habs)
  have hglp : MemLp g 1 μ :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (boundedAbsCoordinate_nonneg _)]
      exact boundedAbsCoordinate_le_one _)
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hglp
  have hle : g ≤ᵐ[μ] fun x => g (T x) := by
    filter_upwards [hcov] with x hx
    change boundedAbsCoordinate (f x) ≤ boundedAbsCoordinate (f (T x))
    rw [hx]
    apply boundedAbsCoordinate_mono
    rw [abs_mul, abs_of_pos hc0]
    nlinarith [abs_nonneg (f x)]
  have hi : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
    have he := integral_map hT.measurable.aemeasurable
      (show AEStronglyMeasurable g (μ.map T) from by
        rw [hT.map_eq]
        exact hgm.aestronglyMeasurable)
    rw [hT.map_eq] at he
    exact he.symm
  have hgTi : Integrable (fun x => g (T x)) μ :=
    memLp_one_iff_integrable.mp (hglp.comp_measurePreserving hT)
  have he := (integral_eq_iff_of_ae_le hgi hgTi hle).mp hi.symm
  filter_upwards [he, hcov] with x hx hxcov
  change f x = 0
  by_contra hne
  have hlt : boundedAbsCoordinate (f x) < boundedAbsCoordinate (f (T x)) := by
    rw [hxcov]
    apply boundedAbsCoordinate_strictMono
    rw [abs_mul, abs_of_pos hc0]
    nlinarith [abs_pos.mpr hne]
  exact (ne_of_lt hlt) hx

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_DiagonalProjectiveRecurrence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite invariant projective laws of a positive diagonal map

This is a coordinate form of diagonal recurrence. A measurable nonzero
representative may change by an arbitrary nonzero scalar under the
dynamics. Ratios cancel that scalar. Unequal positive diagonal weights
cannot both occur in the support of a representative almost everywhere.
The conclusion is an actual eigenline statement, not an orbit hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree

lemma ratio_of_common_nonzero_scalar
    (r a b u v : ℝ) (hr : r ≠ 0) (hb : b ≠ 0) :
    (r * a * u) / (r * b * v) = (a / b) * (u / v) := by
  by_cases hv : v = 0
  · simp only [hv, mul_zero, div_zero]
  · field_simp [hr, hb, hv]

theorem ae_coordinate_zero_or_zero_of_diagonal_weights
    {Y I : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (w : Y → I → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (r : Y → ℝ) (hr : ∀ᵐ x ∂μ, r x ≠ 0)
    (hcov : ∀ i, (fun x => w (T x) i) =ᵐ[μ] fun x => r x * a i * w x i)
    (i j : I) (hij : a j < a i) :
    ∀ᵐ x ∂μ, w x i = 0 ∨ w x j = 0 := by
  have he : (fun x => w (T x) i / w (T x) j) =ᵐ[μ]
      fun x => (a i / a j) * (w x i / w x j) := by
    filter_upwards [hr, hcov i, hcov j] with x hx hi hj
    rw [hi, hj]
    exact ratio_of_common_nonzero_scalar (r x) (a i) (a j)
      (w x i) (w x j) hx (ne_of_gt (ha j))
  have hz := ae_eq_zero_of_expanding_covariance μ T hT
    (fun x => w x i / w x j) ((hw i).div (hw j)) (a i / a j)
    ((one_lt_div (ha j)).mpr hij) he
  filter_upwards [hz] with x hx
  exact div_eq_zero_iff.mp hx

/-- Unequal weights do not coexist in a nonzero projective coordinate
representative. Only countably many coordinates are needed. -/
theorem ae_diagonal_projective_single_weight
    {Y I : Type*} [MeasurableSpace Y] [Countable I]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (w : Y → I → ℝ) (hw : ∀ i, Measurable (fun x => w x i))
    (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (r : Y → ℝ) (hr : ∀ᵐ x ∂μ, r x ≠ 0)
    (hcov : ∀ i, (fun x => w (T x) i) =ᵐ[μ] fun x => r x * a i * w x i) :
    ∀ᵐ x ∂μ, ∀ i j, a i ≠ a j → w x i = 0 ∨ w x j = 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : a i = a j
  · exact Eventually.of_forall (fun _ h => (h hij).elim)
  · rcases lt_or_gt_of_ne hij with h | h
    · exact (ae_coordinate_zero_or_zero_of_diagonal_weights μ T hT w hw a ha r hr
        hcov j i h).mono fun x hx _ => hx.symm
    · exact (ae_coordinate_zero_or_zero_of_diagonal_weights μ T hT w hw a ha r hr
        hcov i j h).mono fun _ hx _ => hx

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingMeasureLimits
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

omit [LocallyCompactSpace X] [T2Space X] [MetrizableSpace X] [SigmaCompactSpace X]
  [NeBot l] in
/-- The group element and the probability measure can both vary: the
integral error from replacing the group element by its limit vanishes. -/
lemma integral_compact_observable_varying_smul
    (μ : I → ProbabilityMeasure X)
    (f : CompactlySupportedContinuousMap X ℝ)
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g)) :
    Tendsto (fun i => (∫ x, f (a i • x) ∂(μ i : Measure X)) -
      ∫ x, f (g • x) ∂(μ i : Measure X)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [compact_observable_varying_smul f f.continuous f.hasCompactSupport a g ha
    (ε / 2) hhalf] with i hi
  have hia : Integrable (fun x => f (a i • x)) (μ i : Measure X) :=
    (f.toBoundedContinuousFunction.compContinuous
      ⟨fun x => a i • x, continuous_const_smul (a i)⟩).integrable (μ := (μ i : Measure X))
  have hig : Integrable (fun x => f (g • x)) (μ i : Measure X) :=
    (f.toBoundedContinuousFunction.compContinuous
      ⟨fun x => g • x, continuous_const_smul g⟩).integrable (μ := (μ i : Measure X))
  rw [Real.dist_eq, sub_zero, ← integral_sub hia hig]
  have hb := norm_integral_le_of_norm_le_const (μ := (μ i : Measure X))
    (f := fun x => f (a i • x) - f (g • x))
    (C := ε / 2) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (hi x).le))
  have he : (μ i : Measure X).real univ = 1 := by simp
  rw [he, mul_one, Real.norm_eq_abs] at hb
  exact hb.trans_lt (by linarith)

/-- A limiting shear belongs to the actual stabilizer of the limiting
probability measure. The hypotheses are weak limits and an exact
translation relation between approximating measures. -/
theorem map_eq_of_converging_translated_probabilities
    (μ ν : I → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (hμ : Tendsto μ l (𝓝 ρ)) (hν : Tendsto ν l (𝓝 ρ))
    (a : I → G) (g : G) (ha : Tendsto a l (𝓝 g))
    (htranslate : ∀ᶠ i in l,
      (μ i : Measure X).map (fun x => a i • x) = (ν i : Measure X)) :
    (ρ : Measure X).map (fun x => g • x) = (ρ : Measure X) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfixed := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (f.toBoundedContinuousFunction.compContinuous
      ⟨fun x => g • x, continuous_const_smul g⟩)
  have htarget := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν
    f.toBoundedContinuousFunction
  have hvary := integral_compact_observable_varying_smul μ f a g ha
  have hsame : Tendsto (fun i => ∫ x, f (a i • x) ∂(μ i : Measure X)) l
      (𝓝 (∫ x, f x ∂(ρ : Measure X))) := by
    apply htarget.congr'
    filter_upwards [htranslate] with i hi
    change (∫ x, f x ∂(ν i : Measure X)) = _
    rw [← hi, integral_map (f := fun x => f x)
      (continuous_const_smul (a i)).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
  have hzero := hsame.sub hfixed
  have he : (∫ x, f x ∂(ρ : Measure X)) -
      (∫ x, f (g • x) ∂(ρ : Measure X)) = 0 := tendsto_nhds_unique hzero hvary
  rw [integral_map (f := fun x => f x) (continuous_const_smul g).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact (sub_eq_zero.mp he).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_StabilizerClosedGraph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed graph of the actual probability stabilizer

The probability measure and the group element may both vary. Uniform
translation control of compact observables shows that invariance passes
to the simultaneous limit. This is the topological input for constructing
measurable data from the component stabilizers.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem isClosed_probability_smul_stabilizer
    {H Y : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [WeaklyLocallyCompactSpace H] [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] [MetrizableSpace Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [MulAction H Y] [ContinuousSMul H Y] :
    IsClosed {p : ProbabilityMeasure Y × H |
      (p.1 : Measure Y).map (fun y => p.2 • y) = (p.1 : Measure Y)} := by
  apply isClosed_iff_forall_filter.mpr
  intro p F hF hset hlim
  let : F.NeBot := hF
  have hμ : Tendsto (fun q : ProbabilityMeasure Y × H => q.1) F (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hg : Tendsto (fun q : ProbabilityMeasure Y × H => q.2) F (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  exact map_eq_of_converging_translated_probabilities
    (fun q : ProbabilityMeasure Y × H => q.1) (fun q => q.1) p.1 hμ hμ
    (fun q => q.2) p.2 hg (Filter.le_principal_iff.mp hset)

/-- The actual right stabilizer on the row-lattice quotient has closed
graph in the weak probability topology times the real matrix group. -/
theorem isClosed_probability_right_stabilizer (n : ℕ) :
    IsClosed {p : ProbabilityMeasure (X n) × G n |
      p.2 ∈ invariantRightSubgroup (p.1 : Measure (X n))} := by
  let : MulAction (G n) (X n) :=
    { smul := fun g x => rightAction x g⁻¹
      one_smul := fun x => by
        change rightAction x (1 : G n)⁻¹ = x
        simp only [inv_one, rightAction_one]
      mul_smul := fun a b x => by
        change rightAction x (a * b)⁻¹ = rightAction (rightAction x b⁻¹) a⁻¹
        rw [mul_inv_rev, rightAction_mul] }
  let : ContinuousSMul (G n) (X n) :=
    ⟨(continuous_rightAction_uncurry n).comp
      (continuous_snd.prodMk continuous_fst.inv)⟩
  have h := isClosed_probability_smul_stabilizer (H := G n) (Y := X n)
  have hc : Continuous (fun p : ProbabilityMeasure (X n) × G n => (p.1, p.2⁻¹)) :=
    continuous_fst.prodMk continuous_snd.inv
  convert h.preimage hc using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  change ((p.1 : Measure (X n)).map (fun x => rightAction x p.2) = p.1) ↔
    ((p.1 : Measure (X n)).map (fun x => rightAction x (p.2⁻¹)⁻¹) = p.1)
  rw [inv_inv]

/-- Passing from an SL element to its actual matrix preserves the
closed stabilizer graph because the determinant-one inclusion is a
closed embedding. -/
theorem isClosed_probability_matrix_stabilizer (n : ℕ) :
    IsClosed {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
      ∃ g : G n, g ∈ invariantRightSubgroup (p.1 : Measure (X n)) ∧ g.val = p.2} := by
  have hc : Topology.IsClosedEmbedding
      (fun p : ProbabilityMeasure (X n) × G n => (p.1, p.2.val)) :=
    Topology.IsClosedEmbedding.id.prodMap Matrix.SpecialLinearGroup.isClosedEmbedding_val
  have h := hc.isClosedMap _ (isClosed_probability_right_stabilizer n)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨g, hg, he⟩
    exact ⟨(p.1, g), hg, Prod.ext rfl he⟩
  · rintro ⟨q, hq, he⟩
    obtain ⟨hμ, hmat⟩ := Prod.mk.inj he
    exact ⟨q.2, hμ ▸ hq, hmat⟩

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_KernelStabilizerMeasurable
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable invariance events for the actual component measures

Equality of finite kernel values is detected by countably many half-line
tests after a measurable embedding in the real line. Consequently both
invariance under one lattice translation and invariance under an entire
root flow are measurable events in the component parameter. The latter
uses rational times and the closedness of the actual measure stabilizer.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurableSet_finite_kernel_eq
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [StandardBorelSpace Y] (κ η : Kernel Z Y)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {z | κ z = η z} := by
  let f := embeddingReal Y
  have hf : MeasurableEmbedding f := measurableEmbedding_embeddingReal Y
  let K := κ.map f
  let E := η.map f
  have he (z : Z) : κ z = η z ↔
      K z univ = E z univ ∧ ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ)) := by
    constructor
    · intro hz
      have hz' : K z = E z := by
        simp only [K, E, Kernel.map_apply _ hf.measurable, hz]
      rw [hz']
      exact ⟨rfl, fun _ => rfl⟩
    · rintro ⟨huniv, hq⟩
      apply hf.map_injective
      rw [← Kernel.map_apply κ hf.measurable, ← Kernel.map_apply η hf.measurable]
      change K z = E z
      apply ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat
        Real.isPiSystem_Iic_rat
      · intro s hs
        simp only [mem_iUnion, mem_singleton_iff] at hs
        obtain ⟨q, rfl⟩ := hs
        exact hq q
      · exact huniv
  have huniv : MeasurableSet {z | K z univ = E z univ} :=
    measurableSet_eq_fun (Kernel.measurable_coe K MeasurableSet.univ)
      (Kernel.measurable_coe E MeasurableSet.univ)
  have hhalf : MeasurableSet {z | ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ))} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter (fun q : ℚ =>
      measurableSet_eq_fun (Kernel.measurable_coe K (measurableSet_Iic (a := (q : ℝ))))
        (Kernel.measurable_coe E (measurableSet_Iic (a := (q : ℝ)))))
  have hset : {z | κ z = η z} =
      {z | K z univ = E z univ} ∩
        {z | ∀ q : ℚ, K z (Iic (q : ℝ)) = E z (Iic (q : ℝ))} := by
    ext z
    exact he z
  rw [hset]
  exact huniv.inter hhalf

lemma measurableSet_kernel_translation_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (κ : Kernel Z (X n)) [IsFiniteKernel κ] (g : G n) :
    MeasurableSet {z | g ∈ invariantRightSubgroup (κ z)} := by
  change MeasurableSet {z | (κ z).map (fun x => rightAction x g) = κ z}
  have h := measurableSet_finite_kernel_eq
    (κ.map (fun x => rightAction x g)) κ
  simpa only [Kernel.map_apply _ (continuous_rightAction g).measurable] using h

lemma all_root_mem_iff_rational_root_mem {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ) ↔
      ∀ q : ℚ, Matrix.SpecialLinearGroup.transvection hij (q : ℝ) ∈
        invariantRightSubgroup μ := by
  constructor
  · exact fun h q => h q
  · intro h t
    exact Rat.denseRange_cast.induction_on t
      ((isClosed_invariantRightSubgroup μ).preimage (continuous_rootTransvection hij)) h

/-- Full real-root invariance is a measurable event, without replacing
the real root by a discrete-time action. -/
lemma measurableSet_kernel_root_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (κ : Kernel Z (X n)) [IsFiniteKernel κ] :
    MeasurableSet {z | ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)} := by
  have he : {z | ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)} =
      ⋂ q : ℚ, {z | Matrix.SpecialLinearGroup.transvection hij (q : ℝ) ∈
        invariantRightSubgroup (κ z)} := by
    ext z
    simp only [mem_iInter, Set.mem_ofPred_eq]
    exact all_root_mem_iff_rational_root_mem hij (κ z)
  rw [he]
  exact MeasurableSet.iInter fun q =>
    measurableSet_kernel_translation_invariant κ _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootCurveExtraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extracting a root from a differentiable curve

A diagonal with a unique maximal root rescales a curve at the identity.
Its limit is the elementary matrix given by that root component of the
velocity. Closedness then puts this actual root element in the subgroup.
This is a direct matrix argument, with no Lie-subgroup classification.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootIsolationWeights_peak {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    rootIsolationWeights i j i - rootIsolationWeights i j j = 2 := by
  norm_num [rootIsolationWeights, hij, Ne.symm hij]

lemma rootIsolationWeights_lt_peak {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (a b : Fin n) (hab : ¬ (a = i ∧ b = j)) :
    rootIsolationWeights i j a - rootIsolationWeights i j b < 2 := by
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j
  all_goals simp_all [rootIsolationWeights] <;> norm_num

lemma hasMatrixVelocity_of_hasDerivAt {n : ℕ} (γ : ℝ → G n)
    (hzero : γ 0 = 1) (V : Matrix (Fin n) (Fin n) ℝ)
    (hderiv : ∀ a b, HasDerivAt (fun t => (γ t).val a b) (V a b) 0) :
    HasMatrixVelocity γ V := by
  intro a b
  have he := (hderiv a b).tendsto_slope_zero_right
  simpa only [zero_add, hzero, Matrix.SpecialLinearGroup.coe_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MatrixVelocitySpace
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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

lemma HasIdentityMatrixDerivative.hasMatrixVelocity {n : ℕ}
    {γ : ℝ → G n} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : HasIdentityMatrixDerivative γ V) : HasMatrixVelocity γ V :=
  hasMatrixVelocity_of_hasDerivAt γ h.1 V h.2

/-- Finite-dimensionality makes the actual velocity space closed; no
closed-subgroup theorem is required for this linear fact. -/
lemma isClosed_matrixVelocitySpace {n : ℕ} (H : Subgroup (G n)) :
    IsClosed (matrixVelocitySpace H : Set (Matrix (Fin n) (Fin n) ℝ)) :=
  (matrixVelocitySpace H).closed_of_finiteDimensional

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixPowerApproximation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stable powers of near-identity matrices

The telescoping estimate is the quantitative step needed to recover a
one-parameter subgroup from the velocity of an actual subgroup curve.
The number of factors grows, while their norms are bounded by a fixed
exponential on the reciprocal scale.
-/

noncomputable section
open Filter
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree

private lemma norm_pow_succ_sub_pow_succ_le {A : Type*} [NormedRing A]
    (a b : A) (K : ℝ) (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (N : ℕ) :
    ‖a ^ (N + 1) - b ^ (N + 1)‖ ≤ (N + 1 : ℝ) * K ^ N * ‖a - b‖ := by
  have hK : 0 ≤ K := (norm_nonneg a).trans ha
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Nat.cast_succ]
    have he : a ^ (N + 1 + 1) - b ^ (N + 1 + 1) =
        (a ^ (N + 1) - b ^ (N + 1)) * b + a ^ (N + 1) * (a - b) := by
      simp only [pow_succ]
      noncomm_ring
    rw [he]
    have hpow : ‖a ^ (N + 1)‖ ≤ K ^ (N + 1) :=
      (norm_pow_le' a (Nat.succ_pos N)).trans (pow_le_pow_left₀ (norm_nonneg a) ha _)
    calc
      _ ≤ ‖a ^ (N + 1) - b ^ (N + 1)‖ * ‖b‖ + ‖a ^ (N + 1)‖ * ‖a - b‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ((N + 1 : ℝ) * K ^ N * ‖a - b‖) * K + K ^ (N + 1) * ‖a - b‖ := by
        gcongr
      _ = (N + 1 + 1 : ℝ) * K ^ (N + 1) * ‖a - b‖ := by
        rw [pow_succ]
        ring

/-- The operator norm gives a dimension-free estimate for actual
matrix powers; no entrywise bound is repeatedly amplified. -/
theorem matrix_power_approximation {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hA : ‖A‖ ≤ Real.exp (C / (N + 1 : ℝ)))
    (hB : ‖B‖ ≤ Real.exp (C / (N + 1 : ℝ))) :
    ‖A ^ (N + 1) - B ^ (N + 1)‖ ≤ Real.exp C * ((N + 1 : ℝ) * ‖A - B‖) := by
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hdiv : 0 ≤ C / (N + 1 : ℝ) := div_nonneg hC hden.le
  have hmul : (N : ℝ) * (C / (N + 1 : ℝ)) ≤ C := by
    have he : (N + 1 : ℝ) * (C / (N + 1 : ℝ)) = C := by
      field_simp [ne_of_gt hden]
    nlinarith
  have hexp : (Real.exp (C / (N + 1 : ℝ))) ^ N ≤ Real.exp C := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hmul
  calc
    _ ≤ (N + 1 : ℝ) * (Real.exp (C / (N + 1 : ℝ))) ^ N * ‖A - B‖ :=
      norm_pow_succ_sub_pow_succ_le A B _ hA hB N
    _ ≤ (N + 1 : ℝ) * Real.exp C * ‖A - B‖ := by gcongr
    _ = _ := by ring

/-- If the one-step error is little-o of the reciprocal number of
factors, the products have the same limit. -/
theorem tendsto_matrix_power_difference_zero {n : ℕ}
    (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ Real.exp (C / (N + 1 : ℝ)))
    (hB : ∀ᶠ N in atTop, ‖B N‖ ≤ Real.exp (C / (N + 1 : ℝ)))
    (herr : Tendsto (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) atTop (𝓝 0)) :
    Tendsto (fun N => ‖(A N) ^ (N + 1) - (B N) ^ (N + 1)‖) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [hA, hB] with N hAN hBN
    exact matrix_power_approximation (A N) (B N) C hC N hAN hBN
  · simpa only [mul_zero] using herr.const_mul (Real.exp C)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootVelocityRecovery
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

lemma transvection_nat_pow {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : ℝ) (N : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij v ^ N =
      Matrix.SpecialLinearGroup.transvection hij ((N : ℝ) * v) := by
  induction N with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  | succ N ih =>
    rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 1
    push_cast
    ring

/-- Entrywise first-order control gives the norm control needed for
growing products. All matrices here use the submultiplicative operator
norm. -/
theorem tendsto_powers_of_pure_root_velocity {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (γ : ℝ → G n) (v : ℝ)
    (hvelocity : HasMatrixVelocity γ (Matrix.single i j v)) :
    Tendsto (fun N : ℕ => γ ((N + 1 : ℝ)⁻¹) ^ (N + 1)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hij v)) := by
  let : Nonempty (Fin n) := ⟨i⟩
  let k : ℕ → ℝ := fun N => N + 1
  let s : ℕ → ℝ := fun N => (k N)⁻¹
  let V : Matrix (Fin n) (Fin n) ℝ := Matrix.single i j v
  let A : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => (γ (s N)).val
  let B : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => 1 + s N • V
  let D : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => k N • (A N - 1)
  let C : ℝ := ‖V‖ + 1
  have hk (N : ℕ) : 0 < k N := by dsimp only [k] <;> positivity
  have hs (N : ℕ) : 0 < s N := inv_pos.mpr (hk N)
  have hstop : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hs0 : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hstop
  have hD : Tendsto D atTop (𝓝 V) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    simpa only [Function.comp_def, D, A, V, s, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, div_eq_mul_inv, inv_inv, mul_comm] using
      (hvelocity a b).comp hs0
  have hDbound : ∀ᶠ N in atTop, ‖D N‖ ≤ C := by
    have he := hD.norm.eventually (Iio_mem_nhds (show ‖V‖ < C by dsimp [C] <;> linarith))
    exact he.mono fun _ h => h.le
  have hAB (N : ℕ) : k N • (A N - B N) = D N - V := by
    have he : A N - B N = (A N - 1) - s N • V := by
      dsimp only [B]
      abel
    rw [he, smul_sub, smul_smul]
    change D N - (k N * (k N)⁻¹) • V = D N - V
    rw [mul_inv_cancel₀ (ne_of_gt (hk N)), one_smul]
  have herr : Tendsto (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) atTop (𝓝 0) := by
    have he := (hD.sub_const V).norm
    have he' : (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) =
        fun N => ‖D N - V‖ := by
      funext N
      rw [← hAB, norm_smul, Real.norm_eq_abs, abs_of_pos (hk N)]
    rw [he']
    simpa only [sub_self, norm_zero] using he
  have hA : ∀ᶠ N in atTop, ‖A N‖ ≤ Real.exp (C / (N + 1 : ℝ)) := by
    filter_upwards [hDbound] with N hN
    have hres : ‖A N - 1‖ ≤ C / k N := by
      apply (le_div_iff₀ (hk N)).mpr
      simpa only [D, norm_smul, Real.norm_eq_abs, abs_of_pos (hk N), mul_comm] using hN
    calc
      ‖A N‖ = ‖(A N - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖A N - 1‖ + ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
      _ ≤ C / k N + 1 := add_le_add hres (le_of_eq norm_one)
      _ ≤ Real.exp (C / k N) := Real.add_one_le_exp _
      _ = _ := rfl
  have hB : ∀ᶠ N in atTop, ‖B N‖ ≤ Real.exp (C / (N + 1 : ℝ)) := by
    apply Eventually.of_forall
    intro N
    have hres : ‖s N • V‖ ≤ C / k N := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hs N)]
      change (k N)⁻¹ * ‖V‖ ≤ C / k N
      rw [mul_comm, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by dsimp [C] <;> linarith) (hk N).le
    calc
      ‖B N‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ + ‖s N • V‖ := norm_add_le _ _
      _ ≤ 1 + C / k N := add_le_add (le_of_eq norm_one) hres
      _ ≤ Real.exp (C / k N) := by simpa only [add_comm] using Real.add_one_le_exp (C / k N)
      _ = _ := rfl
  have hpowers := tendsto_matrix_power_difference_zero A B C
    (show 0 ≤ C by dsimp [C] <;> positivity) hA hB herr
  have hBroot (N : ℕ) : B N =
      (Matrix.SpecialLinearGroup.transvection hij (v / k N)).val := by
    change 1 + s N • Matrix.single i j v = _
    rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.smul_single]
    congr 2
    change (k N)⁻¹ * v = v / k N
    rw [mul_comm, ← div_eq_mul_inv]
  have hBpow (N : ℕ) : B N ^ (N + 1) =
      (Matrix.SpecialLinearGroup.transvection hij v).val := by
    rw [hBroot, ← Matrix.SpecialLinearGroup.coe_pow, transvection_nat_pow]
    have he : (↑(N + 1) : ℝ) * (v / k N) = v := by
      have hcast : (↑(N + 1) : ℝ) = k N := by simp [k]
      rw [hcast]
      exact mul_div_cancel₀ _ (ne_of_gt (hk N))
    rw [he]
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [A, s, k, hBpow, Matrix.SpecialLinearGroup.coe_pow] using hpowers

/-- A pure root tangent direction in a closed matrix subgroup already
gives an actual root element of that subgroup. -/
theorem root_mem_of_pure_matrix_velocity {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (γ : ℝ → G n) (hγ : ∀ t, γ t ∈ L) (v : ℝ)
    (hvelocity : HasMatrixVelocity γ (Matrix.single i j v)) :
    Matrix.SpecialLinearGroup.transvection hij v ∈ L := by
  exact hclosed.mem_of_tendsto (tendsto_powers_of_pure_root_velocity hij γ v hvelocity)
    (Eventually.of_forall fun N => L.pow_mem (hγ _) (N + 1))

theorem root_mem_of_velocitySpace {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (v : ℝ) (hV : Matrix.single i j v ∈ matrixVelocitySpace L) :
    Matrix.SpecialLinearGroup.transvection hij v ∈ L := by
  obtain ⟨γ, hγ, hvelocity⟩ := hV
  exact root_mem_of_pure_matrix_velocity hij L hclosed γ hγ v
    hvelocity.hasMatrixVelocity

/-- The elementary tangent-direction test is exactly full real-root
invariance for a closed subgroup. A single nonzero root element alone
would not suffice for this equivalence. -/
theorem root_direction_mem_velocitySpace_iff {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n))) :
    Matrix.single i j (1 : ℝ) ∈ matrixVelocitySpace L ↔
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L := by
  constructor
  · intro h t
    apply root_mem_of_velocitySpace hij L hclosed t
    have hs := (matrixVelocitySpace L).smul_mem t h
    have he : t • Matrix.single i j (1 : ℝ) = Matrix.single i j t := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rwa [he] at hs
  · intro h
    exact ⟨fun t => Matrix.SpecialLinearGroup.transvection hij (t * 1),
      fun t => h _, hasIdentityMatrixDerivative_rootCurve hij 1⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MatrixExponentialVelocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential recovery from actual subgroup curves

The velocity of a curve in a closed matrix subgroup exponentiates inside
that subgroup. The proof uses growing powers of the curve and the
first-order approximation to the matrix exponential. Thus no matrix
Lie-group classification or determinant formula for the exponential is
needed. The converse supplies an exact exponential test for membership
in the actual velocity subspace.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

private lemma eventual_exp_bound_of_scaled_increment {n : ℕ}
    [Nonempty (Fin n)]
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hA : Tendsto (fun N : ℕ => (N + 1 : ℝ) • (A N - 1)) atTop (𝓝 V)) :
    ∀ᶠ N in atTop, ‖A N‖ ≤ Real.exp ((‖V‖ + 1) / (N + 1 : ℝ)) := by
  have hb : ∀ᶠ N : ℕ in atTop, ‖(N + 1 : ℝ) • (A N - 1)‖ ≤ ‖V‖ + 1 :=
    (hA.norm.eventually (Iio_mem_nhds (by linarith : ‖V‖ < ‖V‖ + 1))).mono
      (fun _ h => h.le)
  filter_upwards [hb] with N hN
  have hk : (0 : ℝ) < N + 1 := by positivity
  have hr : ‖A N - 1‖ ≤ (‖V‖ + 1) / (N + 1 : ℝ) := by
    apply (le_div_iff₀ hk).mpr
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hk, mul_comm] using hN
  calc
    ‖A N‖ = ‖(A N - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖A N - 1‖ + ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
    _ ≤ (‖V‖ + 1) / (N + 1 : ℝ) + 1 := add_le_add hr (le_of_eq norm_one)
    _ ≤ Real.exp ((‖V‖ + 1) / (N + 1 : ℝ)) := Real.add_one_le_exp _

/-- The reciprocal-time powers of an actual curve converge to the
matrix exponential of its velocity. -/
theorem tendsto_matrix_powers_of_velocity {n : ℕ} [Nonempty (Fin n)]
    (γ : ℝ → G n) (V : Matrix (Fin n) (Fin n) ℝ)
    (hvelocity : HasMatrixVelocity γ V) :
    Tendsto (fun N : ℕ => (γ ((N + 1 : ℝ)⁻¹)).val ^ (N + 1)) atTop
      (𝓝 (NormedSpace.exp V)) := by
  let k : ℕ → ℝ := fun N => N + 1
  let s : ℕ → ℝ := fun N => (k N)⁻¹
  let A : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => (γ (s N)).val
  let B : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => NormedSpace.exp (s N • V)
  let D : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => k N • (A N - 1)
  let E : ℕ → Matrix (Fin n) (Fin n) ℝ := fun N => k N • (B N - 1)
  have hk (N : ℕ) : 0 < k N := by dsimp only [k] <;> positivity
  have hktop : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hs0 : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hktop
  have hD : Tendsto D atTop (𝓝 V) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [Function.comp_def, D, A, s, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, div_eq_mul_inv, inv_inv, mul_comm] using
      (hvelocity i j).comp hs0
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V)) V 0 := by
    convert hasDerivAt_exp_smul_const V (0 : ℝ) using 1 <;>
      first | rfl | simp only [zero_smul, NormedSpace.exp_zero, one_mul]
  have hE : Tendsto E atTop (𝓝 V) := by
    convert hd.tendsto_slope_zero_right.comp hs0 using 1
    · funext N
      simp only [Function.comp_def, E, B, s, zero_add, zero_smul,
        NormedSpace.exp_zero, inv_inv]
    · rfl
  have hdiff (N : ℕ) : k N • (A N - B N) = D N - E N := by
    dsimp only [D, E]
    rw [← smul_sub]
    congr 1
    abel
  have herr : Tendsto (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) atTop (𝓝 0) := by
    have he := (hD.sub hE).norm
    have hnorm (N : ℕ) : (N + 1 : ℝ) * ‖A N - B N‖ = ‖D N - E N‖ := by
      rw [← hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (hk N)]
    simpa only [hnorm, sub_self, norm_zero] using he
  have hA := eventual_exp_bound_of_scaled_increment A V hD
  have hB := eventual_exp_bound_of_scaled_increment B V hE
  have hp := tendsto_matrix_power_difference_zero A B (‖V‖ + 1)
    (by positivity) hA hB herr
  have hBpow (N : ℕ) : B N ^ (N + 1) = NormedSpace.exp V := by
    change NormedSpace.exp (s N • V) ^ (N + 1) = NormedSpace.exp V
    have hpow : NormedSpace.exp ((N + 1) • (s N • V)) =
        NormedSpace.exp (s N • V) ^ (N + 1) :=
      NormedSpace.exp_nsmul (N + 1) (s N • V)
    rw [← hpow]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hscalar : (↑(N + 1) : ℝ) * s N = 1 := by
      change (↑(N + 1) : ℝ) * (k N)⁻¹ = 1
      have he : (↑(N + 1) : ℝ) = k N := by simp [k]
      rw [he, mul_inv_cancel₀ (ne_of_gt (hk N))]
    rw [hscalar, one_smul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [A, s, k, hBpow] using hp

/-- The determinant-one assertion is recovered from the approximating
group elements, not assumed as a general exponential formula. -/
theorem exists_subgroup_element_exp_velocity {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (γ : ℝ → G n) (hγ : ∀ t, γ t ∈ L)
    (V : Matrix (Fin n) (Fin n) ℝ) (hV : HasMatrixVelocity γ V) :
    ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp V := by
  have hp := tendsto_matrix_powers_of_velocity γ V hV
  have hd : Matrix.det (NormedSpace.exp V) = 1 := by
    have ht := (continuous_id.matrix_det.tendsto (NormedSpace.exp V)).comp hp
    change Tendsto (fun N : ℕ => Matrix.det ((γ ((N + 1 : ℝ)⁻¹)).val ^ (N + 1)))
      atTop (𝓝 (Matrix.det (NormedSpace.exp V))) at ht
    have he : (fun N : ℕ => Matrix.det ((γ ((N + 1 : ℝ)⁻¹)).val ^ (N + 1))) =
        fun _ => (1 : ℝ) := by
      funext N
      rw [← Matrix.SpecialLinearGroup.coe_pow]
      exact (γ ((N + 1 : ℝ)⁻¹) ^ (N + 1)).property
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let g : G n := ⟨NormedSpace.exp V, hd⟩
  refine ⟨g, ?_, rfl⟩
  apply hL.mem_of_tendsto (show Tendsto
      (fun N : ℕ => γ ((N + 1 : ℝ)⁻¹) ^ (N + 1)) atTop (𝓝 g) from ?_)
    (Eventually.of_forall fun N => L.pow_mem (hγ _) (N + 1))
  apply tendsto_subtype_rng.mpr
  simpa only [Matrix.SpecialLinearGroup.coe_pow] using hp

/-- Exact exponential characterization of the actual tangent subspace
of a closed subgroup. This will allow measurable membership tests without
choosing differentiable curves measurably. -/
theorem mem_matrixVelocitySpace_iff_exp {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    V ∈ matrixVelocitySpace L ↔
      ∀ t : ℝ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp (t • V) := by
  constructor
  · intro hV t
    obtain ⟨γ, hγ, hd⟩ := (matrixVelocitySpace L).smul_mem t hV
    exact exists_subgroup_element_exp_velocity L hL γ hγ (t • V) hd.hasMatrixVelocity
  · intro hexp
    choose γ hγ hg using hexp
    refine ⟨γ, hγ, ?_, ?_⟩
    · apply Subtype.ext
      simp only [hg, zero_smul, NormedSpace.exp_zero,
        Matrix.SpecialLinearGroup.coe_one]
    · intro i j
      have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V)) V 0 := by
        convert hasDerivAt_exp_smul_const V (0 : ℝ) using 1 <;>
          first | rfl | simp only [zero_smul, NormedSpace.exp_zero, one_mul]
      let ev : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
        (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
      have he := ev.hasFDerivAt.comp_hasDerivAt 0 hd
      change HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V) i j) (V i j) 0 at he
      simpa only [hg] using he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_VelocityMembershipMeasurable
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable tests for actual component velocities

For a fixed matrix, membership in the velocity space of a component
stabilizer is a measurable event. The exponential characterization makes
it a countable collection of ordinary stabilizer tests. Rational times
suffice because the subgroup and its matrix image are closed.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

lemma all_exp_mem_iff_rational_exp_mem {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp (t • V)) ↔
      ∀ q : ℚ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp ((q : ℝ) • V) := by
  constructor
  · exact fun h q => h q
  · intro h t
    have himage : IsClosed ((fun g : G n => g.val) '' (L : Set (G n))) :=
      Matrix.SpecialLinearGroup.isClosedEmbedding_val.isClosedMap _ hL
    have hcont : Continuous (fun t : ℝ => NormedSpace.exp (t • V)) :=
      (differentiable_exp_smul_const ℝ V).continuous
    have hclosed := himage.preimage hcont
    have hrat : ∀ q : ℚ, NormedSpace.exp ((q : ℝ) • V) ∈
        (fun g : G n => g.val) '' (L : Set (G n)) := by
      intro q
      obtain ⟨g, hg, he⟩ := h q
      exact ⟨g, hg, he⟩
    exact Rat.denseRange_cast.induction_on t hclosed hrat

lemma mem_matrixVelocitySpace_iff_rational_exp {n : ℕ} [Nonempty (Fin n)]
    (L : Subgroup (G n)) (hL : IsClosed (L : Set (G n)))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    V ∈ matrixVelocitySpace L ↔
      ∀ q : ℚ, ∃ g : G n, g ∈ L ∧ g.val = NormedSpace.exp ((q : ℝ) • V) :=
  (mem_matrixVelocitySpace_iff_exp L hL V).trans
    (all_exp_mem_iff_rational_exp_mem L hL V)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_VelocityClosedGraph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed graph of actual component velocities

Exponential recovery and the closed probability-stabilizer graph imply
that the graph of the actual velocity subspace is closed. In particular,
compact restrictions can be projected without making an arbitrary choice
of tangent curves or frames.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree
open PrimeDegreePackets

theorem isClosed_probability_velocity_graph (n : ℕ) [Nonempty (Fin n)] :
    IsClosed {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
      p.2 ∈ matrixVelocitySpace (invariantRightSubgroup (p.1 : Measure (X n)))} := by
  have he : {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
      p.2 ∈ matrixVelocitySpace (invariantRightSubgroup (p.1 : Measure (X n)))} =
      ⋂ q : ℚ, {p : ProbabilityMeasure (X n) × Matrix (Fin n) (Fin n) ℝ |
        ∃ g : G n, g ∈ invariantRightSubgroup (p.1 : Measure (X n)) ∧
          g.val = NormedSpace.exp ((q : ℝ) • p.2)} := by
    ext p
    simp only [mem_iInter, mem_ofPred_eq]
    exact mem_matrixVelocitySpace_iff_rational_exp _ (isClosed_invariantRightSubgroup _) _
  rw [he]
  apply isClosed_iInter
  intro q
  exact (isClosed_probability_matrix_stabilizer n).preimage
    (continuous_fst.prodMk (NormedSpace.exp_continuous.comp
      (continuous_snd.const_smul (q : ℝ))))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CountableWeakTests
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countably many measure evaluations determine weak convergence

Finite unions from a countable open basis suffice for the Portmanteau
lower bound on every open set. This is used to connect the measurable
kernel evaluations to the weak topology, without assuming a measurable
selection of tangent frames.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

omit [MeasurableSpace Y] [OpensMeasurableSpace Y] in
lemma isOpen_finiteBasisUnion (F : Finset (countableBasis Y)) :
    IsOpen (finiteBasisUnion F) :=
  isOpen_biUnion fun U _ => isOpen_of_mem_countableBasis U.property

theorem tendsto_probability_of_finiteBasisUnion
    (μs : ℕ → ProbabilityMeasure Y) (μ : ProbabilityMeasure Y)
    (h : ∀ F : Finset (countableBasis Y),
      Tendsto (fun k => (μs k : Measure Y) (finiteBasisUnion F)) atTop
        (𝓝 ((μ : Measure Y) (finiteBasisUnion F)))) :
    Tendsto μs atTop (𝓝 μ) := by
  classical
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro U hU
  let I := {B : countableBasis Y // (B.val : Set Y) ⊆ U}
  let W : Finset I → Set Y := fun F => ⋃ B ∈ F, (B.val.val : Set Y)
  have hWU (F : Finset I) : W F ⊆ U := by
    intro x hx
    simp only [W, mem_iUnion] at hx
    obtain ⟨B, hB, hxB⟩ := hx
    exact B.property hxB
  have hmono : Monotone W := by
    intro F G hFG x hx
    simp only [W, mem_iUnion] at hx ⊢
    obtain ⟨B, hB, hxB⟩ := hx
    exact ⟨B, hFG hB, hxB⟩
  have hunion : (⋃ F : Finset I, W F) = U := by
    apply subset_antisymm
    · exact iUnion_subset hWU
    · intro x hx
      obtain ⟨B, hB, hxB, hBU⟩ :=
        (isBasis_countableBasis Y).exists_subset_of_mem_open hx hU
      let i : I := ⟨⟨B, hB⟩, hBU⟩
      refine mem_iUnion.mpr ⟨{i}, ?_⟩
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by simp, hxB⟩⟩
  have hWbasis (F : Finset I) : W F = finiteBasisUnion (F.image fun B => B.val) := by
    ext x
    simp only [W, finiteBasisUnion, mem_iUnion, Finset.mem_image]
    constructor
    · rintro ⟨B, hB, hx⟩
      exact ⟨B.val, ⟨B, hB, rfl⟩, hx⟩
    · rintro ⟨B, ⟨C, hC, rfl⟩, hx⟩
      exact ⟨C, hC, hx⟩
  have hmeasure : (μ : Measure Y) U = ⨆ F : Finset I, (μ : Measure Y) (W F) := by
    rw [← hunion, hmono.measure_iUnion]
  rw [hmeasure]
  apply iSup_le
  intro F
  have hconv : Tendsto (fun k => (μs k : Measure Y) (W F)) atTop
      (𝓝 ((μ : Measure Y) (W F))) := by
    simpa only [hWbasis] using h (F.image fun B => B.val)
  calc
    (μ : Measure Y) (W F) = liminf (fun k => (μs k : Measure Y) (W F)) atTop :=
      hconv.liminf_eq.symm
    _ ≤ liminf (fun k => (μs k : Measure Y) U) atTop :=
      liminf_le_liminf (Eventually.of_forall fun k => measure_mono (hWU F))

/-- The coordinate map into the countable family of open-set tests is
measurable for every actual probability kernel. -/
theorem measurable_kernel_finiteBasisUnion
    {Z : Type*} [MeasurableSpace Z] (κ : ProbabilityTheory.Kernel Z Y)
    (F : Finset (countableBasis Y)) :
    Measurable (fun z => κ z (finiteBasisUnion F)) :=
  ProbabilityTheory.Kernel.measurable_coe κ (isOpen_finiteBasisUnion F).measurableSet

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CountableWeakKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A probability kernel is measurable for the weak topology

A countable family of finite-basis-union evaluations defines a stronger
second-countable topology on probabilities. Kernel evaluations are measurable
for that topology, and the countable Portmanteau criterion makes the map
to the usual weak topology continuous. No global measurable-space
instance on probabilities is changed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

variable (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

omit [OpensMeasurableSpace Y] in
lemma basisProbabilityTests_isInducing :
    Topology.IsInducing (basisProbabilityTests Y) := ⟨rfl⟩

instance instSecondCountableTopologyBasisProbability : SecondCountableTopology (BasisProbability Y) :=
  (basisProbabilityTests_isInducing Y).secondCountableTopology

theorem continuous_basisProbability_toProbability :
    Continuous (BasisProbability.toProbability (Y := Y)) := by
  apply continuous_iff_seqContinuous.mpr
  intro u p hu
  apply tendsto_probability_of_finiteBasisUnion
  intro F
  exact ((continuous_apply F).comp (basisProbabilityTests_isInducing Y).continuous).continuousAt.tendsto.comp hu

variable {Y}

theorem measurable_kernel_basisProbability
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Z Y) [IsMarkovKernel κ] :
    Measurable (fun z =>
      (⟨⟨κ z, inferInstance⟩⟩ : BasisProbability Y)) := by
  have hm : Measurable (fun z => basisProbabilityTests Y
      (⟨⟨κ z, inferInstance⟩⟩ : BasisProbability Y)) := by
    apply measurable_pi_iff.mpr
    intro F
    exact measurable_kernel_finiteBasisUnion κ F
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (fun z =>
      (⟨⟨κ z, inferInstance⟩⟩ : BasisProbability Y))
    (@borel (BasisProbability Y) (TopologicalSpace.induced (basisProbabilityTests Y) _)) ≤ _
  rw [borel_comap, MeasurableSpace.comap_comp,
    ← BorelSpace.measurable_eq (α := Finset (countableBasis Y) → ℝ≥0∞)]
  exact hm.comap_le

/-- The codomain carries the Borel sigma algebra of weak convergence. -/
theorem measurable_kernel_probability_weak
    {Z : Type*} [mZ : MeasurableSpace Z] (κ : Kernel Z Y) [IsMarkovKernel κ] :
    @Measurable Z (ProbabilityMeasure Y) mZ (borel (ProbabilityMeasure Y))
      (fun z => ⟨κ z, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩) := by
  have hcont := (continuous_basisProbability_toProbability Y).borel_measurable
  exact hcont.comp (measurable_kernel_basisProbability κ)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TransferredVelocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Changing coordinates in the actual velocity space

Distances may be measured in any finite-dimensional real model of the
matrix space. This allows the subsequent measurable projection argument
to use Euclidean coordinates while the power estimates use an operator
norm. Every subspace here remains the actual stabilizer velocity space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem lowerSemicontinuous_subspace_distance
    {Z E : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (W : Z → Submodule ℝ E)
    (hgraph : IsClosed {p : Z × E | p.2 ∈ W p.1})
    (hclosed : ∀ z, IsClosed (W z : Set E)) (v : E) :
    LowerSemicontinuous (fun z => Metric.infDist v (W z : Set E)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  let K := Metric.closedBall v r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall v r)
  have hs : IsClosed {p : Z × K | p.2.val ∈ W p.1} :=
    hgraph.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := isClosedMap_fst_of_compactSpace _ hs
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  constructor
  · intro hz
    change Metric.infDist v (W z : Set E) ≤ r at hz
    obtain ⟨w, hw, hdist⟩ := (hclosed z).exists_infDist_eq_dist ⟨0, (W z).zero_mem⟩ v
    have hwK : w ∈ K := by
      exact Metric.mem_closedBall.mpr (by simpa only [dist_comm, hdist] using hz)
    exact ⟨(z, ⟨w, hwK⟩), hw, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    change p.2.val ∈ W p.1 at hp
    change Metric.infDist v (W p.1 : Set E) ≤ r
    exact (Metric.infDist_le_dist_of_mem hp).trans
      (by simpa only [dist_comm] using Metric.mem_closedBall.mp p.2.property)

theorem isClosed_transferredVelocity_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} [Nonempty (Fin n)] (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    IsClosed {p : ProbabilityMeasure (X n) × E |
      p.2 ∈ transferredVelocitySpace e (p.1 : Measure (X n))} :=
  (isClosed_probability_velocity_graph n).preimage
    (continuous_fst.prodMk (e.continuous.comp continuous_snd))

theorem lowerSemicontinuous_transferredVelocity_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)]
    (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ) (v : E) :
    LowerSemicontinuous (fun μ : ProbabilityMeasure (X n) =>
      Metric.infDist v (transferredVelocitySpace e (μ : Measure (X n)) : Set E)) := by
  apply lowerSemicontinuous_subspace_distance _ (isClosed_transferredVelocity_graph e)
  intro μ
  exact (isClosed_matrixVelocitySpace _).preimage e.continuous

theorem measurable_kernel_transferredVelocity_distance
    {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)]
    (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] (v : E) :
    Measurable (fun z => Metric.infDist v (transferredVelocitySpace e (κ z) : Set E)) := by
  let P : Z → ProbabilityMeasure (X n) := fun z => ⟨κ z, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hκ : @Measurable Z (ProbabilityMeasure (X n)) _
      (borel (ProbabilityMeasure (X n))) P := measurable_kernel_probability_weak κ
  have hd : @Measurable (ProbabilityMeasure (X n)) ℝ
      (borel (ProbabilityMeasure (X n))) inferInstance
      (fun μ => Metric.infDist v (transferredVelocitySpace e (μ : Measure (X n)) : Set E)) := by
    let : MeasurableSpace (ProbabilityMeasure (X n)) := borel (ProbabilityMeasure (X n))
    let : BorelSpace (ProbabilityMeasure (X n)) := ⟨rfl⟩
    exact (lowerSemicontinuous_transferredVelocity_distance e v).measurable
  have hm : Measurable (fun z => Metric.infDist v
      (transferredVelocitySpace e (P z : Measure (X n)) : Set E)) := hd.comp hκ
  simpa only [P, ProbabilityMeasure.coe_mk] using hm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ProjectionFromDistances
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recovering measurable orthogonal projections from distances

Polarization expresses every scalar coordinate of an orthogonal
projection using four distances to the subspace. This avoids an assumed
measurable choice of bases. It will be applied to the actual component
velocity spaces after their distance functions have been constructed.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace DukePrimeDegree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma infDist_eq_norm_sub_starProjection (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (v : E) :
    Metric.infDist v (W : Set E) = ‖v - W.starProjection v‖ := by
  rw [Metric.infDist_eq_iInf, W.starProjection_minimal]
  congr 1
  funext w
  exact dist_eq_norm v w

lemma norm_starProjection_sq_eq (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (v : E) :
    ‖W.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - Metric.infDist v (W : Set E) ^ 2 := by
  have hp := W.norm_sq_eq_add_norm_sq_starProjection v
  rw [Submodule.starProjection_orthogonal', sub_apply,
    one_apply_eq_self] at hp
  rw [infDist_eq_norm_sub_starProjection]
  linarith

/-- A coordinate of the projection is determined by the squared
projection norms at the sum and difference of two fixed vectors. -/
theorem inner_starProjection_from_distances (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (v w : E) :
    ⟪W.starProjection v, w⟫_ℝ =
      ((‖v + w‖ ^ 2 - Metric.infDist (v + w) (W : Set E) ^ 2) -
        (‖v - w‖ ^ 2 - Metric.infDist (v - w) (W : Set E) ^ 2)) / 4 := by
  have hproj : W.starProjection (W.starProjection v) = W.starProjection v :=
    W.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem v)
  have hinner : ⟪W.starProjection v, W.starProjection w⟫_ℝ =
      ⟪W.starProjection v, w⟫_ℝ := by
    simpa only [hproj] using
      (W.inner_starProjection_left_eq_right (W.starProjection v) w).symm
  have hp := norm_add_sq_real (W.starProjection v) (W.starProjection w)
  have hm := norm_sub_sq_real (W.starProjection v) (W.starProjection w)
  rw [← map_add, norm_starProjection_sq_eq] at hp
  rw [← map_sub, norm_starProjection_sq_eq] at hm
  rw [hinner] at hp hm
  linarith

theorem measurable_inner_starProjection_of_distances
    {Z : Type*} [MeasurableSpace Z]
    (W : Z → Submodule ℝ E) [∀ z, (W z).HasOrthogonalProjection]
    (hd : ∀ v : E, Measurable (fun z => Metric.infDist v (W z : Set E)))
    (v w : E) : Measurable (fun z => ⟪(W z).starProjection v, w⟫_ℝ) := by
  simp_rw [inner_starProjection_from_distances]
  exact ((measurable_const.sub ((hd (v + w)).pow_const 2)).sub
    (measurable_const.sub ((hd (v - w)).pow_const 2))).div_const 4

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteProjectionFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.compatMatrixBorelSpacePlucker _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite frame selection by Gram determinants

The projected coordinate vectors form a finite measurable spanning family.
Maximal nonzero Gram minors select a basis from that family. All tests used
in the selection are measurable real determinants, so this does not assume
a measurable tangent-frame theorem.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree

section GramFrames

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype I] in
theorem IsMaximalGramFrame.linearIndependent {v : I → E} {S : Finset I}
    (hS : IsMaximalGramFrame v S) : LinearIndependent ℝ (fun i : S => v i) :=
  Matrix.linearIndependent_of_det_gram_ne_zero hS.1

omit [Fintype I] in
theorem IsMaximalGramFrame.span_eq {v : I → E} {S : Finset I}
    (hS : IsMaximalGramFrame v S) :
    Submodule.span ℝ (v '' (S : Set I)) = Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_contra hi
    have hiS : i ∉ S := by
      intro hiS
      exact hi (Submodule.subset_span ⟨i, hiS, rfl⟩)
    have hli : LinearIndepOn ℝ v (S : Set I) := hS.linearIndependent
    have hins : LinearIndepOn ℝ v (insert i (S : Set I)) :=
      (linearIndepOn_insert hiS).mpr ⟨hli, hi⟩
    have hdet : finiteGramDet v (insert i S) ≠ 0 := by
      apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
      let e : ↥(insert i S) → ↑(insert i (S : Set I)) := fun x =>
        ⟨x.val, by
          rcases Finset.mem_insert.mp x.property with h | h
          · exact Or.inl h
          · exact Or.inr h⟩
      have hlin : LinearIndependent ℝ (fun x : ↑(insert i (S : Set I)) => v x) := hins
      apply hlin.comp e
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : ↑(insert i (S : Set I)) => z.val) h
    have hcard : S.card < (insert i S).card := by
      rw [Finset.card_insert_of_notMem hiS]
      exact Nat.lt_succ_self _
    exact hdet (hS.2 _ hcard)

theorem maximalGramFrame_spec (v : I → E) :
    IsMaximalGramFrame v (maximalGramFrame v) := by
  classical
  exact Nat.find_spec (exists_maximalGramFrameIndex v)

theorem selectedFrameVector_linearIndependent (v : I → E) :
    LinearIndependent ℝ (fun j : Fin (maximalGramFrame v).card =>
      selectedFrameVector v j) := by
  have hli := (maximalGramFrame_spec v).linearIndependent
  have heq : (fun j : Fin (maximalGramFrame v).card => selectedFrameVector v j) =
      (fun i : maximalGramFrame v => v i) ∘ (maximalGramFrame v).equivFin.symm := by
    funext j
    simp only [selectedFrameVector, finiteFrameVector, j.isLt, dite_true, Function.comp_def]
  rw [heq]
  exact hli.comp _ (maximalGramFrame v).equivFin.symm.injective

theorem selectedFrameVector_span (v : I → E) :
    Submodule.span ℝ (Set.range (fun j : Fin (maximalGramFrame v).card =>
      selectedFrameVector v j)) = Submodule.span ℝ (Set.range v) := by
  have hrange : Set.range (fun j : Fin (maximalGramFrame v).card =>
      selectedFrameVector v j) = v '' (maximalGramFrame v : Set I) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      simp only [selectedFrameVector, finiteFrameVector, j.isLt, dite_true]
      exact ⟨_, ((maximalGramFrame v).equivFin.symm j).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(maximalGramFrame v).equivFin ⟨i, hi⟩, ?_⟩
      simp only [selectedFrameVector, finiteFrameVector,
        ((maximalGramFrame v).equivFin ⟨i, hi⟩).isLt, dite_true]
      change v (((maximalGramFrame v).equivFin.symm
        ((maximalGramFrame v).equivFin ⟨i, hi⟩)).val) = v i
      rw [Equiv.symm_apply_apply]
  rw [hrange]
  exact (maximalGramFrame_spec v).span_eq

theorem maximalGramFrame_card (v : I → E) :
    (maximalGramFrame v).card = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  have h := finrank_span_eq_card (selectedFrameVector_linearIndependent v)
  rw [selectedFrameVector_span, Fintype.card_fin] at h
  exact h.symm

end GramFrames

section Measurability

variable {Z I E : Type*} [MeasurableSpace Z] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_finiteGramDet (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (S : Finset I) :
    Measurable (fun z => finiteGramDet (v z) S) := by
  have hm : Measurable (fun z => Matrix.gram ℝ (fun i : S => v z i)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact (hv i).inner (hv j)
  exact continuous_id.matrix_det.measurable.comp hm

theorem measurableSet_isMaximalGramFrame (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (S : Finset I) :
    MeasurableSet {z | IsMaximalGramFrame (v z) S} := by
  apply MeasurableSet.inter
  · exact (measurableSet_eq_fun (measurable_finiteGramDet v hv S) measurable_const).compl
  · change MeasurableSet {z | ∀ T : Finset I, S.card < T.card → finiteGramDet (v z) T = 0}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro T
    by_cases hST : S.card < T.card
    · simpa only [hST, true_implies] using
        measurableSet_eq_fun (measurable_finiteGramDet v hv T) measurable_const
    · simp only [hST, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ

theorem measurable_maximalGramFrameIndex (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) :
    Measurable (fun z => maximalGramFrameIndex (v z)) := by
  classical
  exact measurable_find (fun z => exists_maximalGramFrameIndex (v z))
    (fun k => measurableSet_isMaximalGramFrame v hv (frameEnumeration I k))

theorem measurable_selectedFrameVector (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) (j : ℕ) :
    Measurable (fun z => selectedFrameVector (v z) j) := by
  classical
  have hm (k : ℕ) : Measurable (fun z =>
      finiteFrameVector (v z) (frameEnumeration I k) j) := by
    by_cases hj : j < (frameEnumeration I k).card
    · simpa only [finiteFrameVector, hj, dite_true] using
        hv (((frameEnumeration I k).equivFin.symm ⟨j, hj⟩).val)
    · simpa only [finiteFrameVector, hj, dite_false] using
        (measurable_const : Measurable (fun _ : Z => (0 : E)))
  exact Measurable.find hm
    (fun k => measurableSet_isMaximalGramFrame v hv (frameEnumeration I k))
    (fun z => exists_maximalGramFrameIndex (v z))

theorem measurable_selectedFrameCard (v : Z → I → E)
    (hv : ∀ i, Measurable (fun z => v z i)) :
    Measurable (fun z => (maximalGramFrame (v z)).card) := by
  exact (measurable_from_nat : Measurable (fun k => (frameEnumeration I k).card)).comp
    (measurable_maximalGramFrameIndex v hv)

end Measurability

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PluckerCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.compatMatrixBorelSpaceFPF _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.compatMatrixBorelSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual frame minors under diagonal transport

The projective coordinates here are determinants of minors of an actual
real matrix frame. Changing its basis multiplies every coordinate by the
same determinant. Thus diagonal recurrence applies to these coordinates
without an assumed projective-action interface.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped BigOperators ENNReal

namespace DukePrimeDegree

lemma minor_diagonal_frame_mul {n k : ℕ}
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (R : Matrix (Fin k) (Fin k) ℝ) (p : Fin k ↪ Fin n) :
    frameMinor (Matrix.diagonal a * B * R) p =
      (∏ i, a (p i)) * frameMinor B p * R.det := by
  have he : (Matrix.diagonal a * B * R).submatrix p id =
      Matrix.diagonal (fun i => a (p i)) * B.submatrix p id * R := by
    ext i j
    change (∑ u, (Matrix.diagonal a * B) (p i) u * R u j) =
      ∑ u, (Matrix.diagonal (fun v => a (p v)) * B.submatrix p id) i u * R u j
    simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id_eq]
  change ((Matrix.diagonal a * B * R).submatrix p id).det = _
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  rfl

lemma measurable_frameMinor {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j)) (p : Fin k ↪ Fin n) :
    Measurable (fun x => frameMinor (B x) p) := by
  have hm : Measurable (fun x => (B x).submatrix p id) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact hB (p i) j
  exact continuous_id.matrix_det.measurable.comp hm

/-- For a measurably transported real frame, two nonzero minors can
have only the same diagonal weight almost everywhere. This is the
projective recurrence conclusion in actual matrix coordinates. -/
theorem ae_frame_minors_have_one_diagonal_weight
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (R : Y → Matrix (Fin k) (Fin k) ℝ)
    (hR : ∀ᵐ x ∂μ, (R x).det ≠ 0)
    (hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x) :
    ∀ᵐ x ∂μ, ∀ p q : Fin k ↪ Fin n,
      (∏ i, a (p i)) ≠ (∏ i, a (q i)) →
        frameMinor (B x) p = 0 ∨ frameMinor (B x) q = 0 := by
  apply ae_diagonal_projective_single_weight μ T hT
    (fun x p => frameMinor (B x) p) (measurable_frameMinor B hB)
    (fun p => ∏ i, a (p i)) (fun p => Finset.prod_pos (fun i _ => ha (p i)))
    (fun x => (R x).det) hR
  intro p
  filter_upwards [hcov] with x hx
  rw [hx, minor_diagonal_frame_mul]
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FrameWeightRigidity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From minor weights to an invariant subspace

In a genuine Grassmannian coordinate chart, the pivot rows of a frame
form the identity. A one-row replacement minor is then exactly the
corresponding graph coordinate. The single-weight minor conclusion
therefore forces the frame to intertwine the two diagonal operators.
-/

noncomputable section
open MeasureTheory Filter Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

lemma replaceFramePivot_self {n k : ℕ} (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n) :
    replaceFramePivot p j i j = i := by
  simp [replaceFramePivot]

lemma replaceFramePivot_other {n k : ℕ} (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n)
    (hi : i ∉ Set.range p) (u : Fin k) (hu : u ≠ j) :
    replaceFramePivot p j i u = p u := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact p.injective.ne hu
  · intro h
    exact hi ⟨u, h⟩

lemma frameMinor_replace_pivot {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) (hp : B.submatrix p id = 1)
    (j : Fin k) (i : Fin n) (hi : i ∉ Set.range p) :
    frameMinor B (replaceFramePivot p j i) = B i j := by
  have he : B.submatrix (replaceFramePivot p j i) id =
      (1 : Matrix (Fin k) (Fin k) ℝ).updateRow j (B i) := by
    ext u v
    by_cases hu : u = j
    · subst u
      simp only [Matrix.submatrix_apply, id_eq, replaceFramePivot_self, Matrix.updateRow_self]
    · rw [Matrix.submatrix_apply, replaceFramePivot_other p j i hi u hu,
        Matrix.updateRow_ne hu]
      exact congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A u v) hp
  have hrow : (∑ u, (B i u) • (1 : Matrix (Fin k) (Fin k) ℝ) u) = B i := by
    ext v
    simp [Matrix.one_apply, Pi.smul_apply]
  change (B.submatrix (replaceFramePivot p j i) id).det = _
  rw [he]
  simpa only [hrow, Matrix.det_one, smul_eq_mul, mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix (Fin k) (Fin k) ℝ) j (B i)

lemma replaced_pivot_weight_ne {n k : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (p : Fin k ↪ Fin n) (j : Fin k) (i : Fin n)
    (hi : i ∉ Set.range p) (hne : a i ≠ a (p j)) :
    (∏ u, a (replaceFramePivot p j i u)) ≠ ∏ u, a (p u) := by
  have he : (fun u => a (replaceFramePivot p j i u)) =
      Function.update (fun u => a (p u)) j (a i) := by
    funext u
    by_cases hu : u = j
    · subst u
      simp only [replaceFramePivot_self, Function.update_self]
    · simp only [replaceFramePivot_other p j i hi u hu, Function.update_of_ne hu]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase,
    ← Finset.mul_prod_erase Finset.univ (fun u => a (p u)) (Finset.mem_univ j)]
  exact fun h => hne (mul_right_cancel₀
    (Finset.prod_ne_zero_iff.mpr (fun u _ => ha (p u))) h)

/-- In a normalized frame chart, a graph coefficient joining unequal
diagonal weights must vanish. -/
theorem frame_entry_eq_zero_of_minor_weights {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : B.submatrix p id = 1)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hminor : ∀ q, (∏ u, a (q u)) ≠ ∏ u, a (p u) → frameMinor B q = 0)
    (i : Fin n) (j : Fin k) (hne : a i ≠ a (p j)) : B i j = 0 := by
  by_cases hi : i ∈ Set.range p
  · obtain ⟨u, rfl⟩ := hi
    have hu : u ≠ j := by
      intro h
      subst u
      exact hne rfl
    have he := congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A u j) hp
    simpa only [Matrix.submatrix_apply, id_eq, Matrix.one_apply_ne hu] using he
  · have hz := hminor (replaceFramePivot p j i)
      (replaced_pivot_weight_ne a ha p j i hi hne)
    simpa only [frameMinor_replace_pivot B p hp j i hi] using hz

/-- The frame intertwines the ambient diagonal operator and its pivot
restriction. Consequently its column subspace is invariant. -/
theorem diagonal_mul_frame_eq_frame_mul_diagonal {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : B.submatrix p id = 1)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hminor : ∀ q, (∏ u, a (q u)) ≠ ∏ u, a (p u) → frameMinor B q = 0) :
    Matrix.diagonal a * B = B * Matrix.diagonal (fun u => a (p u)) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : a i = a (p j)
  · rw [h, mul_comm]
  · rw [frame_entry_eq_zero_of_minor_weights B p hp a ha hminor i j h,
      mul_zero, zero_mul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizedFrame
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal invariance of an actual frame

A nonzero pivot minor gives a concrete normalized frame, by multiplying
on the right by that minor's inverse.  The one-weight conclusion for
the original minors then makes its column space diagonal-invariant.
The pivot may be chosen separately at each point; no invariant chart
or measurable choice of the pivot is assumed.
-/

noncomputable section
open MeasureTheory Filter Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

lemma frame_submatrix_mul_right {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) :
    (B * R).submatrix p id = B.submatrix p id * R := by
  ext i j
  rfl

lemma frameMinor_mul_right {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (R : Matrix (Fin k) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) :
    frameMinor (B * R) p = frameMinor B p * R.det := by
  unfold frameMinor
  rw [frame_submatrix_mul_right, Matrix.det_mul]

lemma normalizeFrame_pivot {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) (hp : frameMinor B p ≠ 0) :
    (normalizeFrame B p).submatrix p id = 1 := by
  rw [normalizeFrame, frame_submatrix_mul_right]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp)

lemma normalizeFrame_mul_pivot {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (p : Fin k ↪ Fin n) (hp : frameMinor B p ≠ 0) :
    normalizeFrame B p * B.submatrix p id = B := by
  exact Matrix.nonsing_inv_mul_cancel_right _ B (isUnit_iff_ne_zero.mpr hp)

/-- The change of basis exhibiting invariance is the explicit conjugate
of the diagonal on the pivot rows. -/
theorem diagonal_mul_frame_of_minor_weights {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (p : Fin k ↪ Fin n)
    (hp : frameMinor B p ≠ 0)
    (a : Fin n → ℝ) (ha : ∀ i, a i ≠ 0)
    (hminor : ∀ q, (∏ u, a (q u)) ≠ ∏ u, a (p u) → frameMinor B q = 0) :
    Matrix.diagonal a * B = B *
      ((B.submatrix p id)⁻¹ * Matrix.diagonal (fun u => a (p u)) * B.submatrix p id) := by
  have hnormalized : Matrix.diagonal a * normalizeFrame B p =
      normalizeFrame B p * Matrix.diagonal (fun u => a (p u)) := by
    apply diagonal_mul_frame_eq_frame_mul_diagonal _ p (normalizeFrame_pivot B p hp) a ha
    intro q hq
    rw [normalizeFrame, frameMinor_mul_right, hminor q hq, zero_mul]
  calc
    Matrix.diagonal a * B = Matrix.diagonal a *
        (normalizeFrame B p * B.submatrix p id) := by
          rw [normalizeFrame_mul_pivot B p hp]
    _ = normalizeFrame B p * Matrix.diagonal (fun u => a (p u)) *
        B.submatrix p id := by rw [← Matrix.mul_assoc, hnormalized]
    _ = _ := by simp only [normalizeFrame, Matrix.mul_assoc]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FrameChangeOfBasis
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Deriving the frame cocycle from subspace transport

Two full-rank finite frames with the same column space differ by an
invertible matrix. This supplies the change of basis in the diagonal
recurrence argument from transport of the actual velocity subspaces.
-/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

theorem exists_invertible_frame_change {n k : ℕ}
    (B C : Matrix (Fin n) (Fin k) ℝ)
    (hC : LinearIndependent ℝ C.col)
    (hspan : Submodule.span ℝ (Set.range C.col) ≤
      Submodule.span ℝ (Set.range B.col)) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, R.det ≠ 0 ∧ C = B * R := by
  have hcol (j : Fin k) : ∃ c : Fin k → ℝ, B *ᵥ c = C.col j := by
    have hj : C.col j ∈ LinearMap.range B.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact hspan (Submodule.subset_span ⟨j, rfl⟩)
    exact hj
  choose c hc using hcol
  let R : Matrix (Fin k) (Fin k) ℝ := fun i j => c j i
  have hBR : C = B * R := by
    ext i j
    exact (congrFun (hc j) i).symm
  have hRinj : Function.Injective R.mulVec := by
    intro u v huv
    apply (Matrix.mulVec_injective_iff.mpr hC)
    rw [hBR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv]
  refine ⟨R, ?_, hBR⟩
  exact ((Matrix.isUnit_iff_isUnit_det R).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hRinj)).ne_zero

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FullFrameMinors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A nonzero coordinate minor of an independent frame

Maximal Gram minors of the row family select the required coordinate
minor. Row rank equals column rank, so the selected number of rows is
exactly the size of the independent column frame.
-/

noncomputable section
open Matrix Set

namespace DukePrimeDegree

theorem exists_nonzero_frameMinor_of_linearIndependent {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (hB : LinearIndependent ℝ B.col) :
    ∃ p : Fin k ↪ Fin n, frameMinor B p ≠ 0 := by
  let e := EuclideanSpace.equiv (Fin k) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin k) := fun i => e.symm (B.row i)
  let S := maximalGramFrame v
  have hmap : (Submodule.span ℝ (Set.range v)).map e.toLinearMap =
      Submodule.span ℝ (Set.range B.row) := by
    have heq : e.toLinearMap ∘ v = B.row := by
      funext i
      exact e.apply_symm_apply (B.row i)
    rw [Submodule.map_span, ← Set.range_comp, heq]
  have hcard : S.card = k := by
    calc
      S.card = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := maximalGramFrame_card v
      _ = Module.finrank ℝ ((Submodule.span ℝ (Set.range v)).map e.toLinearMap) :=
        (e.toLinearEquiv.finrank_map_eq _).symm
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range B.row)) := by rw [hmap]
      _ = B.rank := B.rank_eq_finrank_span_row.symm
      _ = k := by
        rw [B.rank_eq_finrank_span_cols, finrank_span_eq_card hB, Fintype.card_fin]
  let q : Fin k ≃ S := (S.equivFinOfCardEq hcard).symm
  let p : Fin k ↪ Fin n := q.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hli : LinearIndependent ℝ (fun s : S => v s) := (maximalGramFrame_spec v).linearIndependent
  have hrows : LinearIndependent ℝ (B.submatrix p id).row := by
    have hmapli := hli.map_injOn e.toLinearMap (fun _ _ _ _ h => e.injective h)
    have hcomp := hmapli.comp q q.injective
    change LinearIndependent ℝ (fun i : Fin k => e (v (q i))) at hcomp
    have heq : (fun i : Fin k => e (v (q i))) = (B.submatrix p id).row := by
      funext i
      change e (e.symm (B.row (q i))) = B.row (q i)
      exact e.apply_symm_apply _
    rw [heq] at hcomp
    exact hcomp
  refine ⟨p, ?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FrameSubspaceRecurrence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal recurrence from transport of an actual subspace

The measurable frame theorem needs only transport of its column space.
The change-of-basis matrix and its nonzero determinant are derived here
from that transport and independence; they are not additional dynamical
hypotheses.
-/

noncomputable section
open MeasureTheory Filter Matrix Set

namespace DukePrimeDegree

/-- A fixed-rank frame may be extended by zero outside its invariant rank
event. The projective recurrence then applies to the whole probability
space; restriction to an invariant subspace of the measure is unnecessary. -/
theorem ae_frame_diagonal_invariant_on_event
    {Y : Type*} [MeasurableSpace Y] {n k : ℕ}
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (E : Set Y) (hE : ∀ᵐ x ∂μ, T x ∈ E ↔ x ∈ E)
    (B : Y → Matrix (Fin n) (Fin k) ℝ)
    (hB : ∀ i j, Measurable (fun x => B x i j))
    (hfull : ∀ᵐ x ∂μ, x ∈ E → LinearIndependent ℝ (B x).col)
    (hzero : ∀ᵐ x ∂μ, x ∉ E → B x = 0)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (htransport : ∀ᵐ x ∂μ, x ∈ E →
      Submodule.span ℝ (Set.range (B (T x)).col) =
        Submodule.span ℝ (Set.range (Matrix.diagonal a * B x).col)) :
    ∀ᵐ x ∂μ, x ∈ E → ∃ C : Matrix (Fin k) (Fin k) ℝ,
      Matrix.diagonal a * B x = B x * C := by
  classical
  have hchanges : ∀ᵐ x ∂μ, ∃ R : Matrix (Fin k) (Fin k) ℝ,
      R.det ≠ 0 ∧ B (T x) = Matrix.diagonal a * B x * R := by
    filter_upwards [hE, hzero, hT.quasiMeasurePreserving.ae hzero,
      hT.quasiMeasurePreserving.ae hfull, htransport] with x hEx hz hzT hfT ht
    by_cases hx : x ∈ E
    · exact exists_invertible_frame_change (Matrix.diagonal a * B x)
        (B (T x)) (hfT (hEx.mpr hx)) (ht hx).le
    · refine ⟨1, by simp, ?_⟩
      rw [hz hx, hzT (fun h => hx (hEx.mp h))]
      simp
  let R : Y → Matrix (Fin k) (Fin k) ℝ := fun x =>
    if h : ∃ R : Matrix (Fin k) (Fin k) ℝ,
        R.det ≠ 0 ∧ B (T x) = Matrix.diagonal a * B x * R then
      Classical.choose h else 1
  have hR : ∀ᵐ x ∂μ, (R x).det ≠ 0 := by
    filter_upwards [hchanges] with x hx
    simpa only [R, dite_eq_left hx] using (Classical.choose_spec hx).1
  have hcov : ∀ᵐ x ∂μ, B (T x) = Matrix.diagonal a * B x * R x := by
    filter_upwards [hchanges] with x hx
    simpa only [R, dite_eq_left hx] using (Classical.choose_spec hx).2
  filter_upwards [hfull,
    ae_frame_minors_have_one_diagonal_weight μ T hT B hB a ha R hR hcov]
    with x hx hweights hxE
  obtain ⟨p, hp⟩ := exists_nonzero_frameMinor_of_linearIndependent (B x) (hx hxE)
  refine ⟨((B x).submatrix p id)⁻¹ * Matrix.diagonal (fun u => a (p u)) *
    (B x).submatrix p id, ?_⟩
  apply diagonal_mul_frame_of_minor_weights (B x) p hp a (fun i => ne_of_gt (ha i))
  intro q hq
  exact (hweights q p hq).resolve_right hp

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_KernelVelocityFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.compatMatrixBorelSpacePlucker _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual measurable frames for component stabilizers

Projecting the Euclidean coordinate basis and selecting a maximal Gram
minor constructs a frame of each actual stabilizer velocity space. The
frame cardinality and every fixed column are measurable along a Markov
kernel. This supplies the missing measurable input to diagonal recurrence.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree
open PrimeDegreePackets

theorem euclideanVelocityColumns_span {n : ℕ} (μ : Measure (X n)) :
    Submodule.span ℝ (Set.range (euclideanVelocityColumns μ)) =
      euclideanVelocitySpace μ := by
  let b := EuclideanSpace.basisFun (Fin n × Fin n) ℝ
  have hrange : Set.range (euclideanVelocityColumns μ) =
      (euclideanVelocitySpace μ).starProjection '' Set.range b := by
    exact Set.range_comp _ _
  rw [hrange]
  change Submodule.span ℝ
    ((euclideanVelocitySpace μ).starProjection.toLinearMap '' Set.range b) = _
  rw [← Submodule.map_span]
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
  rw [hspan, Submodule.map_top, Submodule.range_starProjection]

theorem measurable_euclideanVelocityColumns
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] (p : Fin n × Fin n) :
    Measurable (fun z => euclideanVelocityColumns (κ z) p) := by
  have hcoords : Measurable (fun z =>
      (EuclideanSpace.equiv (Fin n × Fin n) ℝ) (euclideanVelocityColumns (κ z) p)) := by
    apply measurable_pi_iff.mpr
    intro q
    have hm := measurable_inner_starProjection_of_distances
      (fun z => euclideanVelocitySpace (κ z))
      (measurable_kernel_transferredVelocity_distance (matrixEuclideanEquiv n) κ)
      (EuclideanSpace.basisFun (Fin n × Fin n) ℝ p)
      (EuclideanSpace.basisFun (Fin n × Fin n) ℝ q)
    change Measurable (fun z => (euclideanVelocityColumns (κ z) p) q)
    simpa only [EuclideanSpace.inner_basisFun_real, euclideanVelocityColumns] using hm
  convert (EuclideanSpace.equiv (Fin n × Fin n) ℝ).symm.continuous.measurable.comp
    hcoords using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact ((EuclideanSpace.equiv (Fin n × Fin n) ℝ).symm_apply_apply _).symm

theorem velocityFrame_linearIndependent {n : ℕ} (μ : Measure (X n)) :
    LinearIndependent ℝ (fun j : Fin (velocityFrameCard μ) => velocityFrame μ j) := by
  exact (selectedFrameVector_linearIndependent (euclideanVelocityColumns μ)).map_injOn
    (matrixEuclideanEquiv n).toLinearMap
    (fun _ _ _ _ h => (matrixEuclideanEquiv n).injective h)

theorem velocityFrame_span {n : ℕ} (μ : Measure (X n)) :
    Submodule.span ℝ (Set.range (fun j : Fin (velocityFrameCard μ) => velocityFrame μ j)) =
      matrixVelocitySpace (invariantRightSubgroup μ) := by
  have hrange : Set.range (fun j : Fin (velocityFrameCard μ) => velocityFrame μ j) =
      matrixEuclideanEquiv n '' Set.range
        (fun j : Fin (velocityFrameCard μ) =>
          selectedFrameVector (euclideanVelocityColumns μ) j) := by
    exact Set.range_comp _ _
  rw [hrange]
  change Submodule.span ℝ ((matrixEuclideanEquiv n).toLinearMap '' Set.range
    (fun j : Fin (velocityFrameCard μ) =>
      selectedFrameVector (euclideanVelocityColumns μ) j)) = _
  rw [← Submodule.map_span]
  have hframe : Submodule.span ℝ (Set.range
      (fun j : Fin (velocityFrameCard μ) =>
        selectedFrameVector (euclideanVelocityColumns μ) j)) =
      Submodule.span ℝ (Set.range (euclideanVelocityColumns μ)) :=
    selectedFrameVector_span (euclideanVelocityColumns μ)
  rw [hframe, euclideanVelocityColumns_span]
  exact Submodule.map_comap_eq_of_surjective (matrixEuclideanEquiv n).surjective _

theorem velocityFrameCard_eq_finrank {n : ℕ} (μ : Measure (X n)) :
    velocityFrameCard μ = Module.finrank ℝ (matrixVelocitySpace (invariantRightSubgroup μ)) := by
  have h := finrank_span_eq_card (velocityFrame_linearIndependent μ)
  rw [velocityFrame_span, Fintype.card_fin] at h
  exact h.symm

theorem measurable_velocityFrameCard
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] :
    Measurable (fun z => velocityFrameCard (κ z)) :=
  measurable_selectedFrameCard (fun z => euclideanVelocityColumns (κ z))
    (measurable_euclideanVelocityColumns κ)

theorem measurable_velocityFrame
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ] (j : ℕ) :
    Measurable (fun z => velocityFrame (κ z) j) :=
  (matrixEuclideanEquiv n).continuous.measurable.comp
    (measurable_selectedFrameVector (fun z => euclideanVelocityColumns (κ z))
      (measurable_euclideanVelocityColumns κ) j)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_NormalizerInvariantSigma
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A normalizer acts on the actual invariant sigma algebra

The normalizer need not fix individual ergodic components. It acts
measurably on their invariant sigma algebra and preserves the trimmed
base measure. These are the base-space facts needed for covariance of
the component kernel.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurable_invariantSigma_of_semiconjugacy
    {H Y : Type*} [Group H] [MulAction H Y] [MeasurableSpace Y]
    (T : Y → Y) (hT : Measurable T) (α : H → H)
    (hα : ∀ h x, T (h • x) = α h • T x) :
    @Measurable Y Y (actionInvariantSigma H Y) (actionInvariantSigma H Y) T := by
  intro s hs
  have hs' (h : H) : MeasurableSet s ∧ (fun x : Y => h • x) ⁻¹' s = s :=
    (iInf_le (fun g : H => MeasurableSpace.invariants (fun x : Y => g • x)) h) s hs
  rw [actionInvariantSigma, MeasurableSpace.measurableSet_iInf]
  intro h
  refine ⟨hT (hs' 1).1, ?_⟩
  ext x
  change T (h • x) ∈ s ↔ T x ∈ s
  rw [hα]
  exact Set.ext_iff.mp (hs' (α h)).2 (T x)

lemma measurePreserving_trim_of_measurable
    {Y : Type*} [mY : MeasurableSpace Y] (m : MeasurableSpace Y)
    (hm : m ≤ mY) (μ : @Measure Y mY) (T : Y → Y)
    (hT : @MeasurePreserving Y Y mY mY T μ μ) (hmT : @Measurable Y Y m m T) :
    @MeasurePreserving Y Y m m T
      (@Measure.trim Y m mY μ hm) (@Measure.trim Y m mY μ hm) := by
  refine ⟨hmT, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hmT hs, trim_measurableSet_eq hm (hmT hs),
    trim_measurableSet_eq hm hs]
  let : MeasurableSpace Y := mY
  exact hT.measure_preimage ((hm s hs).nullMeasurableSet)

lemma lattice_normalizer_measurable_invariantSigma {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n))) :
    @Measurable (X n) (X n) (actionInvariantSigma H (X n))
      (actionInvariantSigma H (X n)) (fun x => rightAction x a) := by
  let α : H → H := fun h => ⟨a⁻¹ * h.val * a,
    (Subgroup.mem_normalizer_iff''.mp ha h.val).mp h.property⟩
  apply measurable_invariantSigma_of_semiconjugacy
    (fun x => rightAction x a) (continuous_rightAction a).measurable α
  intro h x
  change rightAction (rightAction x h.val⁻¹) a =
    rightAction (rightAction x a) (a⁻¹ * h.val * a)⁻¹
  simp only [rightAction_mul]
  congr 1
  group

/-- The actual normalizer transformation preserves the component base
law whenever it preserves the ambient measure. -/
lemma lattice_normalizer_preserves_invariantSigma {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) (hμ : μ.map (fun x => rightAction x a) = μ) :
    @MeasurePreserving (X n) (X n)
      (actionInvariantSigma H (X n)) (actionInvariantSigma H (X n))
      (fun x => rightAction x a)
      (μ.trim (actionInvariantSigma_le H (X n)))
      (μ.trim (actionInvariantSigma_le H (X n))) := by
  exact measurePreserving_trim_of_measurable _ _ μ _
    ⟨(continuous_rightAction a).measurable, hμ⟩
    (lattice_normalizer_measurable_invariantSigma H a ha)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NormalizerKernelCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Covariance of the component kernel under a normalizer

The normalizer moves the component parameter as well as the component
measure. The proof compares the two actual joint laws and uses uniqueness
of disintegration. In particular, it does not replace covariance by the
stronger assertion that every component is fixed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem condExpKernel_equivariant
    {Y : Type*} (m : MeasurableSpace Y)
    [mY : MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (hm : m ≤ mY)
    (μ : @Measure Y mY) [IsProbabilityMeasure μ]
    (T : @MeasurableEquiv Y Y mY mY)
    (hT : @MeasurePreserving Y Y mY mY T μ μ)
    (hmT : @Measurable Y Y m m T)
    (hmTi : @Measurable Y Y m m T.symm) :
    ∀ᵐ x ∂μ.trim hm,
      (condExpKernel μ m x).map T = condExpKernel μ m (T x) := by
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  let κT := Kernel.comap κ T hmT
  let : IsMarkovKernel (κ.map T) := Kernel.IsMarkovKernel.map κ T.measurable
  let : IsMarkovKernel κT := inferInstance
  have hτT : @MeasurePreserving Y Y m m T τ τ :=
    measurePreserving_trim_of_measurable m hm μ T hT hmT
  have hdiag : τ ⊗ₘ κ =
      @Measure.map Y (Y × Y) mY (m.prod mY) Function.diag μ :=
    compProd_trim_condExpKernel hm
  have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hrectangle (A B : Set Y) (hA : @MeasurableSet Y m A)
      (hB : @MeasurableSet Y mY B) :
      (τ ⊗ₘ κ) (A ×ˢ B) = μ (A ∩ B) := by
    rw [hdiag, Measure.map_apply hδ (hA.prod hB)]
    rfl
  have hprod : τ ⊗ₘ κ.map T = τ ⊗ₘ κT := by
    apply Measure.ext_prod
    intro A B hA hB
    have hleft : (τ ⊗ₘ κ.map T) (A ×ˢ B) = μ (A ∩ T ⁻¹' B) := by
      rw [Measure.compProd_apply_prod hA hB]
      simp_rw [Kernel.map_apply' _ T.measurable _ hB]
      rw [← Measure.compProd_apply_prod hA (T.measurable hB),
        hrectangle A (T ⁻¹' B) hA (T.measurable hB)]
    have hright : (τ ⊗ₘ κT) (A ×ˢ B) = μ (T.symm ⁻¹' A ∩ B) := by
      let F : Y → ℝ≥0∞ := (T.symm ⁻¹' A).indicator (fun x => κ x B)
      have hF : @Measurable Y ℝ≥0∞ m _ F :=
        (Kernel.measurable_coe κ hB).indicator (hmTi hA)
      have hFE : (fun x => F (T x)) = A.indicator (fun x => κ (T x) B) := by
        funext x
        by_cases hx : x ∈ A
        · have hTx : T x ∈ T.symm ⁻¹' A := by simpa only [mem_preimage,
            T.symm_apply_apply] using hx
          simp only [F, Set.indicator_of_mem hx, Set.indicator_of_mem hTx]
        · have hTx : T x ∉ T.symm ⁻¹' A := by simpa only [mem_preimage,
            T.symm_apply_apply] using hx
          simp only [F, Set.indicator_of_notMem hx, Set.indicator_of_notMem hTx]
      calc
        (τ ⊗ₘ κT) (A ×ˢ B) = ∫⁻ x in A, κ (T x) B ∂τ := by
          rw [Measure.compProd_apply_prod hA hB]
          rfl
        _ = ∫⁻ x, F (T x) ∂τ := by
          rw [hFE, lintegral_indicator hA]
        _ = ∫⁻ x, F x ∂τ := by
          let : MeasurableSpace Y := m
          exact hτT.lintegral_comp hF
        _ = ∫⁻ x in T.symm ⁻¹' A, κ x B ∂τ := lintegral_indicator (hmTi hA) _
        _ = (τ ⊗ₘ κ) ((T.symm ⁻¹' A) ×ˢ B) :=
          (Measure.compProd_apply_prod (hmTi hA) hB).symm
        _ = μ (T.symm ⁻¹' A ∩ B) := hrectangle _ _ (hmTi hA) hB
    rw [hleft, hright]
    have he : A ∩ T ⁻¹' B = T ⁻¹' (T.symm ⁻¹' A ∩ B) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, T.symm_apply_apply]
    rw [he]
    exact hT.measure_preimage (((T.symm.measurable (hm A hA)).inter hB).nullMeasurableSet)
  have hfirst := condKernel_compProd τ (κ.map T)
  have hsecond := condKernel_compProd τ κT
  have hfirst' : (τ ⊗ₘ κT).condKernel =ᵐ[τ] κ.map T := by
    simpa only [hprod] using hfirst
  have heq := hfirst'.symm.trans hsecond
  filter_upwards [heq] with x hx
  change (κ.map T) x = κT x at hx
  simpa only [κT, Kernel.map_apply _ T.measurable, Kernel.comap_apply, κ] using hx

/-- For the actual lattice action, a normalizer sends each conditional
measure to the conditional measure at the moved parameter. -/
theorem lattice_normalizer_component_covariance {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x => rightAction x a) = μ) :
    ∀ᵐ x ∂μ.trim (actionInvariantSigma_le H (X n)),
      (condExpKernel μ (actionInvariantSigma H (X n)) x).map
        (fun y => rightAction y a) =
      condExpKernel μ (actionInvariantSigma H (X n)) (rightAction x a) := by
  let T : X n ≃ᵐ X n :=
    { toEquiv :=
        { toFun := fun x => rightAction x a
          invFun := fun x => rightAction x a⁻¹
          left_inv := by intro x; simp only [rightAction_mul, mul_inv_cancel, rightAction_one]
          right_inv := by intro x; simp only [rightAction_mul, inv_mul_cancel, rightAction_one] }
      measurable_toFun := (continuous_rightAction a).measurable
      measurable_invFun := (continuous_rightAction a⁻¹).measurable }
  exact condExpKernel_equivariant (actionInvariantSigma H (X n))
    (actionInvariantSigma_le H (X n)) μ T ⟨T.measurable, hμ⟩
    (lattice_normalizer_measurable_invariantSigma H a ha)
    (lattice_normalizer_measurable_invariantSigma H a⁻¹
      ((Subgroup.normalizer (H : Set (G n))).inv_mem ha))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MeasureConjugation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugation of the actual measure stabilizer

Right translation conjugates stabilizers in the opposite direction.
These identities apply to arbitrary measures and do not assume that the
translating element preserves the measure.
-/

noncomputable section
open MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

lemma map_rightAction_mul {n : ℕ} (μ : Measure (X n)) (a b : G n) :
    (μ.map (fun x => rightAction x a)).map (fun x => rightAction x b) =
      μ.map (fun x => rightAction x (a * b)) := by
  rw [Measure.map_map (continuous_rightAction b).measurable
    (continuous_rightAction a).measurable]
  congr 1
  funext x
  exact rightAction_mul x a b

lemma map_rightAction_injective {n : ℕ} (a : G n) :
    Function.Injective (fun μ : Measure (X n) => μ.map (fun x => rightAction x a)) := by
  intro μ ν h
  have he := congrArg (fun ρ : Measure (X n) =>
    ρ.map (fun x => rightAction x a⁻¹)) h
  simpa only [map_rightAction_mul, mul_inv_cancel, rightAction_one,
    Measure.map_id'] using he

lemma mem_invariantRightSubgroup_map_iff {n : ℕ}
    (μ : Measure (X n)) (a g : G n) :
    g ∈ invariantRightSubgroup (μ.map (fun x => rightAction x a)) ↔
      a * g * a⁻¹ ∈ invariantRightSubgroup μ := by
  change (μ.map (fun x => rightAction x a)).map (fun x => rightAction x g) =
    μ.map (fun x => rightAction x a) ↔
    μ.map (fun x => rightAction x (a * g * a⁻¹)) = μ
  constructor
  · intro h
    have he := congrArg (fun ρ : Measure (X n) =>
      ρ.map (fun x => rightAction x a⁻¹)) h
    simpa only [map_rightAction_mul, mul_inv_cancel, rightAction_one,
      Measure.map_id'] using he
  · intro h
    apply map_rightAction_injective a⁻¹
    simpa only [map_rightAction_mul, mul_inv_cancel, rightAction_one,
      Measure.map_id'] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MeasureStabilizerCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual stabilizers of transported component measures

Right translation conjugates the measure stabilizer in the opposite
direction. Combining this identity with component-kernel covariance
gives the exact covariance of their spaces of matrix velocities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrixVelocitySpace_map_rightAction {n : ℕ}
    (μ : Measure (X n)) (a : G n)
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ matrixVelocitySpace (invariantRightSubgroup μ)) :
    a⁻¹.val * V * a.val ∈
      matrixVelocitySpace (invariantRightSubgroup (μ.map (fun x => rightAction x a))) := by
  have hc : ∀ g ∈ invariantRightSubgroup μ,
      a⁻¹ * g * (a⁻¹)⁻¹ ∈
        invariantRightSubgroup (μ.map (fun x => rightAction x a)) := by
    intro g hg
    apply (mem_invariantRightSubgroup_map_iff μ a (a⁻¹ * g * (a⁻¹)⁻¹)).mpr
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    group
  simpa only [inv_inv] using conjugate_mem_matrixVelocitySpace (invariantRightSubgroup μ)
    (invariantRightSubgroup (μ.map (fun x => rightAction x a))) a⁻¹ hc hV

/-- The tangent transport is an equivalence, not just an inclusion.
This is the exact relation needed for a change of frame. -/
lemma matrixVelocitySpace_map_rightAction_iff {n : ℕ}
    (μ : Measure (X n)) (a : G n)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    a⁻¹.val * V * a.val ∈
        matrixVelocitySpace (invariantRightSubgroup
          (μ.map (fun x => rightAction x a))) ↔
      V ∈ matrixVelocitySpace (invariantRightSubgroup μ) := by
  constructor
  · intro hV
    have h := matrixVelocitySpace_map_rightAction
      (μ.map (fun x => rightAction x a)) a⁻¹ hV
    have hmap : (μ.map (fun x => rightAction x a)).map
        (fun x => rightAction x a⁻¹) = μ := by
      simp only [map_rightAction_mul, mul_inv_cancel, rightAction_one, Measure.map_id']
    have ha : a.val * a⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hcancel : a.val * (a⁻¹.val * V * a.val) * a⁻¹.val = V := by
      calc
        _ = (a.val * a⁻¹.val) * V * (a.val * a⁻¹.val) := by simp only [Matrix.mul_assoc]
        _ = V := by rw [ha, Matrix.one_mul, Matrix.mul_one]
    simpa only [inv_inv, hmap, hcancel] using h
  · exact matrixVelocitySpace_map_rightAction μ a

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_VelocityTransportRank
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rank transport for actual stabilizer frames

Right translation conjugates the actual velocity space by a linear
equivalence. Thus the cardinality of the constructed measurable frame
is preserved under component-kernel covariance. This supplies the
invariant rank events used by the finite-frame recurrence theorem.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

theorem map_matrixVelocitySpace_rightAction {n : ℕ}
    (μ : Measure (X n)) (a : G n) :
    (matrixVelocitySpace (invariantRightSubgroup μ)).map
        (slMatrixConjugationEquiv a).toLinearMap =
      matrixVelocitySpace (invariantRightSubgroup (μ.map (fun x => rightAction x a))) := by
  ext V
  constructor
  · rintro ⟨W, hW, rfl⟩
    exact matrixVelocitySpace_map_rightAction μ a hW
  · intro hV
    let W := slMatrixConjugation a⁻¹ V
    have hW : W ∈ matrixVelocitySpace (invariantRightSubgroup μ) := by
      apply (matrixVelocitySpace_map_rightAction_iff μ a W).mp
      change slMatrixConjugation a (slMatrixConjugation a⁻¹ V) ∈ _
      simpa only [slMatrixConjugation_inverse] using hV
    exact ⟨W, hW, slMatrixConjugation_inverse a V⟩

theorem velocityFrameCard_map_rightAction {n : ℕ}
    (μ : Measure (X n)) (a : G n) :
    velocityFrameCard (μ.map (fun x => rightAction x a)) = velocityFrameCard μ := by
  rw [velocityFrameCard_eq_finrank, velocityFrameCard_eq_finrank,
    ← map_matrixVelocitySpace_rightAction μ a]
  exact (slMatrixConjugationEquiv a).finrank_map_eq _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_VelocityRootProjection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root projection inside an invariant velocity space

The extreme weight of a split diagonal isolates an off-diagonal matrix
coefficient inside a closed invariant vector space. For the actual
velocity space of a closed measure stabilizer, the isolated direction
then gives an actual full real root group by the power approximation.
This is the linear step after, rather than a substitute for, proving
diagonal invariance of the component velocity spaces by recurrence.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonal_matrix_conjugation_entry {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ a, ell a = 0) (t : ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ((diagonalOneParameter ell hell t).val * V *
      (diagonalOneParameter ell hell (-t)).val) i j =
        Real.exp ((ell i - ell j) * t) * V i j := by
  change (Matrix.diagonal (fun i => Real.exp (ell i * t)) * V *
    Matrix.diagonal (fun i => Real.exp (ell i * (-t)))) i j = _
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_assoc, mul_comm (V i j), ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tendsto_diagonal_matrix_root_projection {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (V : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun m : ℕ => Real.exp (-2 * (m : ℝ)) •
      ((diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
        (m : ℝ)).val * V *
       (diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
        (-(m : ℝ))).val)) atTop (𝓝 (Matrix.single i j (V i j))) := by
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have he (m : ℕ) :
      (Real.exp (-2 * (m : ℝ)) •
        ((diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
          (m : ℝ)).val * V *
         (diagonalOneParameter (rootIsolationWeights i j) (rootIsolationWeights_sum i j)
          (-(m : ℝ))).val)) a b =
      Real.exp ((rootIsolationWeights i j a - rootIsolationWeights i j b - 2) * (m : ℝ)) *
        V a b := by
    rw [Matrix.smul_apply, diagonal_matrix_conjugation_entry]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  by_cases hab : a = i ∧ b = j
  · obtain ⟨hai, hbj⟩ := hab
    subst a
    subst b
    simp only [rootIsolationWeights_peak i j hij, sub_self, zero_mul,
      Real.exp_zero, one_mul, Matrix.single_apply, and_self, ite_true, if_true]
    exact tendsto_const_nhds
  · have hc : rootIsolationWeights i j a - rootIsolationWeights i j b - 2 < 0 :=
      sub_neg.mpr (rootIsolationWeights_lt_peak i j hij a b hab)
    have hlim := (Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hc)).mul_const (V a b)
    have hab' : ¬ (i = a ∧ j = b) := by
      rintro ⟨hia, hjb⟩
      exact hab ⟨hia.symm, hjb.symm⟩
    simpa only [Function.comp_def, zero_mul, Matrix.single_apply, ite_eq_right hab'] using hlim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixCoordinateFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinate frames on the actual velocity-rank events

The finite-dimensional recurrence argument uses rectangular matrices with
one natural-number row dimension. Flattening the actual matrix space is
only a linear change of coordinates. On each measurable rank event the
selected velocity frame has independent columns and spans the actual
velocity space; outside that event the rectangular frame is zero.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma coordinateVelocityFrame_eq {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ = k) :
    coordinateVelocityFrame μ k =
      Matrix.of (fun (q : Fin (n * n)) (j : Fin k) =>
        matrixCoordinateEquiv n (velocityFrame μ j) q) := by
  ext q j
  exact ite_eq_left hk

lemma coordinateVelocityFrame_eq_zero {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ ≠ k) : coordinateVelocityFrame μ k = 0 := by
  ext q j
  exact ite_eq_right hk

theorem coordinateVelocityFrame_linearIndependent {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ = k) :
    LinearIndependent ℝ (coordinateVelocityFrame μ k).col := by
  have h := velocityFrame_linearIndependent μ
  rw [hk] at h
  have hm := h.map_injOn (matrixCoordinateEquiv n).toLinearMap
    (fun _ _ _ _ he => (matrixCoordinateEquiv n).injective he)
  rw [coordinateVelocityFrame_eq μ hk]
  change LinearIndependent ℝ (fun j : Fin k => matrixCoordinateEquiv n (velocityFrame μ j))
  exact hm

theorem coordinateVelocityFrame_span {n k : ℕ} (μ : Measure (X n))
    (hk : velocityFrameCard μ = k) :
    Submodule.span ℝ (Set.range (coordinateVelocityFrame μ k).col) =
      (matrixVelocitySpace (invariantRightSubgroup μ)).map
        (matrixCoordinateEquiv n).toLinearMap := by
  have h := congrArg (fun W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) =>
      W.map (matrixCoordinateEquiv n).toLinearMap) (velocityFrame_span μ)
  rw [hk, Submodule.map_span, ← Set.range_comp] at h
  rw [coordinateVelocityFrame_eq μ hk]
  change Submodule.span ℝ (Set.range
    (fun j : Fin k => matrixCoordinateEquiv n (velocityFrame μ j))) = _
  exact h

theorem measurable_coordinateVelocityFrame_entry
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (k : ℕ) (q : Fin (n * n)) (j : Fin k) :
    Measurable (fun z => coordinateVelocityFrame (κ z) k q j) := by
  have he : (fun z => coordinateVelocityFrame (κ z) k q j) =
      (fun z => if velocityFrameCard (κ z) = k then
        velocityFrame (κ z) (j : ℕ) (finProdFinEquiv.symm q).1
          (finProdFinEquiv.symm q).2 else (0 : ℝ)) := by
    rfl
  rw [he]
  have hE : MeasurableSet {z | velocityFrameCard (κ z) = k} :=
    measurableSet_eq_fun (measurable_velocityFrameCard κ) measurable_const
  have hv : Measurable (fun z => velocityFrame (κ z) (j : ℕ)
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) :=
    (measurable_pi_apply (finProdFinEquiv.symm q).2).comp
      ((measurable_pi_apply (finProdFinEquiv.symm q).1).comp (measurable_velocityFrame κ (j : ℕ)))
  exact Measurable.ite hE hv measurable_const

lemma matrixCoordinateWeight_pos {n : ℕ} (ell : Fin n → ℝ) (q : Fin (n * n)) :
    0 < matrixCoordinateWeight ell q := Real.exp_pos _

lemma matrixCoordinateEquiv_diagonal_conjugation {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    matrixCoordinateEquiv n
        ((diagonalOneParameter ell hell 1).val * V *
          (diagonalOneParameter ell hell (-1)).val) =
      Matrix.diagonal (matrixCoordinateWeight ell) *ᵥ matrixCoordinateEquiv n V := by
  ext q
  change ((diagonalOneParameter ell hell 1).val * V *
      (diagonalOneParameter ell hell (-1)).val)
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 = _
  rw [diagonal_matrix_conjugation_entry, Matrix.mulVec_diagonal, mul_one]
  rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_KernelVelocityRecurrence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal recurrence for actual component velocity spaces

The kernel covariance is the equality supplied by the
normalizer ergodic decomposition. The velocity space and its measurable
frame are constructed from the kernel, rather than supplied as extra
geometric data. Recurrence is applied separately on its measurable rank
events, and gives invariance of the actual velocity space.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma span_columns_mul_le {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ) :
    Submodule.span ℝ (Set.range (B * C).col) ≤
      Submodule.span ℝ (Set.range B.col) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [← Matrix.range_mulVecLin]
  exact ⟨C.col j, rfl⟩

lemma diagonal_mem_span_of_frame_invariance {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (a : Fin n → ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ)
    (hBC : Matrix.diagonal a * B = B * C)
    {v : Fin n → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range B.col)) :
    Matrix.diagonal a *ᵥ v ∈ Submodule.span ℝ (Set.range B.col) := by
  have hspan : (Submodule.span ℝ (Set.range B.col)).map
      (Matrix.diagonal a).mulVecLin =
      Submodule.span ℝ (Set.range (Matrix.diagonal a * B).col) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hm := Submodule.mem_map_of_mem (f := (Matrix.diagonal a).mulVecLin) hv
  rw [hspan, hBC] at hm
  exact span_columns_mul_le B C hm

lemma coordinate_velocitySpace_transport {n : ℕ}
    (μ : Measure (X n)) (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) :
    (matrixVelocitySpace (invariantRightSubgroup
      (μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1)))))).map
        (matrixCoordinateEquiv n).toLinearMap =
      ((matrixVelocitySpace (invariantRightSubgroup μ)).map
        (matrixCoordinateEquiv n).toLinearMap).map
          (Matrix.diagonal (matrixCoordinateWeight ell)).mulVecLin := by
  rw [← map_matrixVelocitySpace_rightAction μ (diagonalOneParameter ell hell (-1)),
    ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext V q
  change matrixCoordinateEquiv n
      ((diagonalOneParameter ell hell (-1))⁻¹.val * V *
        (diagonalOneParameter ell hell (-1)).val) q = _
  have hinv : (diagonalOneParameter ell hell (-1))⁻¹ =
      diagonalOneParameter ell hell 1 := by
    rw [diagonalOneParameter_neg, inv_inv]
  rw [hinv]
  exact congrFun (matrixCoordinateEquiv_diagonal_conjugation ell hell V) q

/-- Covariance under one actual diagonal translation forces the actual
kernel velocity space to be stable under its adjoint map almost surely.
This uses no ergodicity of that individual translation. -/
theorem ae_kernel_velocity_diagonal_stable
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} [Nonempty (Fin n)]
    (τ : Measure Z) [IsFiniteMeasure τ]
    (κ : Kernel Z (X n)) [IsMarkovKernel κ]
    (T : Z → Z) (hT : MeasurePreserving T τ τ)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (hcov : ∀ᵐ z ∂τ,
      (κ z).map (fun x => rightAction x (diagonalOneParameter ell hell (-1))) = κ (T z)) :
    ∀ᵐ z ∂τ, ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup (κ z)),
      (diagonalOneParameter ell hell 1).val * V *
        (diagonalOneParameter ell hell (-1)).val ∈
          matrixVelocitySpace (invariantRightSubgroup (κ z)) := by
  classical
  let a := matrixCoordinateWeight ell
  have hcard : ∀ᵐ z ∂τ, velocityFrameCard (κ (T z)) = velocityFrameCard (κ z) := by
    filter_upwards [hcov] with z hz
    rw [← hz]
    exact velocityFrameCard_map_rightAction (κ z) _
  have hframes (k : ℕ) : ∀ᵐ z ∂τ, velocityFrameCard (κ z) = k →
      ∃ C : Matrix (Fin k) (Fin k) ℝ,
        Matrix.diagonal a * coordinateVelocityFrame (κ z) k =
          coordinateVelocityFrame (κ z) k * C := by
    apply ae_frame_diagonal_invariant_on_event τ T hT
      {z | velocityFrameCard (κ z) = k} ?_
      (fun z => coordinateVelocityFrame (κ z) k)
      (measurable_coordinateVelocityFrame_entry κ k) ?_ ?_ a
      (matrixCoordinateWeight_pos ell) ?_
    · exact hcard.mono fun z hz => by change _ = k ↔ _ = k; rw [hz]
    · exact Eventually.of_forall fun z hz => coordinateVelocityFrame_linearIndependent (κ z) hz
    · exact Eventually.of_forall fun z hz => coordinateVelocityFrame_eq_zero (κ z) hz
    · filter_upwards [hcov, hcard] with z hz hc hk
      have hkT : velocityFrameCard (κ (T z)) = k := hc.trans hk
      rw [coordinateVelocityFrame_span (κ (T z)) hkT]
      have hcols : Submodule.span ℝ
          (Set.range (Matrix.diagonal a * coordinateVelocityFrame (κ z) k).col) =
          (Submodule.span ℝ (Set.range (coordinateVelocityFrame (κ z) k).col)).map
            (Matrix.diagonal a).mulVecLin := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [hcols, coordinateVelocityFrame_span (κ z) hk, ← hz]
      exact coordinate_velocitySpace_transport (κ z) ell hell
  filter_upwards [ae_all_iff.mpr hframes] with z hz
  intro V hV
  let k := velocityFrameCard (κ z)
  obtain ⟨C, hC⟩ := hz k rfl
  have hv : matrixCoordinateEquiv n V ∈
      Submodule.span ℝ (Set.range (coordinateVelocityFrame (κ z) k).col) := by
    rw [coordinateVelocityFrame_span (κ z) rfl]
    exact Submodule.mem_map_of_mem hV
  have hD := diagonal_mem_span_of_frame_invariance
    (coordinateVelocityFrame (κ z) k) a C hC hv
  rw [coordinateVelocityFrame_span (κ z) rfl,
    ← matrixCoordinateEquiv_diagonal_conjugation ell hell V] at hD
  obtain ⟨W, hW, hWV⟩ := hD
  have he := (matrixCoordinateEquiv n).injective hWV
  rwa [he] at hW

/-- The preceding recurrence applies to the actual invariant-sigma
conditional measures. Normalizer covariance and preservation of their
base law are the proved decomposition statements, not new hypotheses. -/
theorem ae_conditional_velocity_diagonal_stable
    {n : ℕ} [Nonempty (Fin n)]
    (H : Subgroup (G n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (ha : diagonalOneParameter ell hell (-1) ∈ Subgroup.normalizer (H : Set (G n)))
    (hμ : μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1))) = μ) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X n)) z)),
      (diagonalOneParameter ell hell 1).val * V *
        (diagonalOneParameter ell hell (-1)).val ∈
          matrixVelocitySpace (invariantRightSubgroup
            (condExpKernel μ (actionInvariantSigma H (X n)) z)) := by
  let m := actionInvariantSigma H (X n)
  let : MeasurableSpace (X n) := xMeasurableSpace n
  have hm : m ≤ xMeasurableSpace n := actionInvariantSigma_le H (X n)
  let τ : @Measure (X n) m := @Measure.trim (X n) m (xMeasurableSpace n) μ hm
  let κ : @Kernel (X n) (X n) m (xMeasurableSpace n) := condExpKernel μ m
  exact @ae_kernel_velocity_diagonal_stable (X n) m n inferInstance
    τ inferInstance κ inferInstance
    (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
    (lattice_normalizer_preserves_invariantSigma H _ ha μ hμ) ell hell
    (lattice_normalizer_component_covariance H _ ha μ hμ)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ComponentRootPattern
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma all_root_mem_map_diagonal_iff {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n))
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (t : ℝ) :
    (∀ s : ℝ, Matrix.SpecialLinearGroup.transvection hij s ∈
      invariantRightSubgroup (μ.map (fun x => rightAction x
        (diagonalOneParameter ell hell t)))) ↔
      ∀ s : ℝ, Matrix.SpecialLinearGroup.transvection hij s ∈ invariantRightSubgroup μ := by
  let a := diagonalOneParameter ell hell t
  let c := Real.exp ((ell i - ell j) * t)
  have hc : c ≠ 0 := Real.exp_ne_zero _
  have hconj (s : ℝ) : a * Matrix.SpecialLinearGroup.transvection hij s * a⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (c * s) := by
    rw [← diagonalOneParameter_neg]
    exact diagonal_conjugation_transvection ell hell hij s t
  constructor
  · intro h s
    have hs := (mem_invariantRightSubgroup_map_iff μ a _).mp (h (s / c))
    rw [hconj, mul_div_cancel₀ _ hc] at hs
    exact hs
  · intro h s
    apply (mem_invariantRightSubgroup_map_iff μ a _).mpr
    rw [hconj]
    exact h _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ComponentRootConstancy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# No new invariant roots on the component base

Diagonal covariance makes each full-root invariance event invariant on
the parameter space. Diagonal ergodicity makes that event null or conull.
In the conull case, integration of the actual conditional measures gives
root invariance of the original measure. This conclusion does not assume
that the individual conditional measures are diagonal invariant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma translation_mem_of_ae_kernel_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (τ : Measure Z) (κ : Kernel Z (X n)) (g : G n)
    (hκ : ∀ᵐ z ∂τ, g ∈ invariantRightSubgroup (κ z)) :
    g ∈ invariantRightSubgroup (κ ∘ₘ τ) := by
  change (κ ∘ₘ τ).map (fun x => rightAction x g) = κ ∘ₘ τ
  rw [Measure.map_comp τ κ (continuous_rightAction g).measurable]
  apply Measure.comp_congr
  filter_upwards [hκ] with z hz
  change (κ z).map (fun x => rightAction x g) = κ z at hz
  simpa only [Kernel.map_apply _ (continuous_rightAction g).measurable] using hz

lemma root_mem_of_ae_kernel_invariant
    {Z : Type*} [MeasurableSpace Z] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (τ : Measure Z) (κ : Kernel Z (X n))
    (hκ : ∀ᵐ z ∂τ, ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)) :
    ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
      invariantRightSubgroup (κ ∘ₘ τ) := by
  intro t
  exact translation_mem_of_ae_kernel_invariant τ κ _ (hκ.mono fun z hz => hz t)

/-- On the actual invariant-sigma conditional measures, a root can be
present on a positive set of parameters only if it fixes the ambient
diagonal-ergodic measure. The normalizer condition concerns the subgroup
used for conditioning, not the stabilizer of each component. -/
theorem ae_component_root_implies_ambient_root
    (d : ℕ) (H : Subgroup (G (d + 1)))
    (hAH : ∀ u : LogCoordinates d,
      diagonalFlow u ∈ Subgroup.normalizer (H : Set (G (d + 1))))
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    {i j : Fin (d + 1)} (hij : i ≠ j) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X (d + 1))),
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X (d + 1))) z)) →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
  let m := actionInvariantSigma H (X (d + 1))
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  have hm : m ≤ xMeasurableSpace (d + 1) := actionInvariantSigma_le H (X (d + 1))
  let κ := condExpKernel μ m
  let E : Set (X (d + 1)) := {z | ∀ t : ℝ,
    Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)}
  have hE : @MeasurableSet (X (d + 1)) m E :=
    @measurableSet_kernel_root_invariant (X (d + 1)) m (d + 1) i j hij κ inferInstance
  have hEinv (u : Multiplicative (LogCoordinates d)) :
      (u • ·) ⁻¹' E =ᵐ[μ] E := by
    let ell : Fin (d + 1) → ℝ := Fin.snoc u.toAdd (-∑ k, u.toAdd k)
    have hell : ∑ k, ell k = 0 := by simp [ell, Fin.sum_univ_castSucc]
    have ha : diagonalOneParameter ell hell 1 = diagonalFlow u.toAdd := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      congr 1
      funext k
      simp [ell]
    have hμ : μ.map (fun x => rightAction x (diagonalFlow u.toAdd)) = μ :=
      (measurePreserving_smul u μ).map_eq
    have hc := lattice_normalizer_component_covariance H
      (diagonalFlow u.toAdd) (hAH u.toAdd) μ hμ
    apply Filter.Eventually.set_eq
    filter_upwards [ae_of_ae_trim hm hc] with z hz
    change (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
      invariantRightSubgroup (κ (rightAction z (diagonalFlow u.toAdd)))) ↔
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup (κ z)
    change (κ z).map (fun x => rightAction x (diagonalFlow u.toAdd)) =
      κ (rightAction z (diagonalFlow u.toAdd)) at hz
    rw [← hz, ← ha]
    exact all_root_mem_map_diagonal_iff hij (κ z) ell hell 1
  have hconst := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq
    (G := Multiplicative (LogCoordinates d)) (hm E hE) hEinv
  rcases eventuallyConst_set.mp hconst with hall | hnone
  · have halltrim : ∀ᵐ z ∂μ.trim hm, z ∈ E := by
      rw [ae_iff] at hall ⊢
      change μ Eᶜ = 0 at hall
      change μ.trim hm Eᶜ = 0
      rwa [trim_measurableSet_eq hm hE.compl]
    have hroot := @root_mem_of_ae_kernel_invariant (X (d + 1)) m (d + 1) i j
      hij (μ.trim hm) κ halltrim
    have hdec : κ ∘ₘ μ.trim hm = μ := condExpKernel_comp_trim hm
    rw [hdec] at hroot
    exact Eventually.of_forall fun _ _ => hroot
  · have hnonetrim : ∀ᵐ z ∂μ.trim hm, z ∉ E := by
      rw [ae_iff] at hnone ⊢
      have he : {a | ¬a ∉ E} = E := by ext a; simp only [mem_ofPred_eq, not_not]
      rw [he] at hnone ⊢
      rwa [trim_measurableSet_eq hm hE]
    exact hnonetrim.mono fun _ hz h => (hz h).elim

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_FiniteDiagonalVelocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root recovery from finitely many diagonal recurrence statements

For each root, a single diagonal has that root as its unique largest
weight. Stability under this one diagonal gives stability under all its
positive integer powers, which is enough to project onto that root.
Thus the actual component application requires only finitely many
recurrence statements, rather than a simultaneous assertion for an
uncountable family of diagonal elements.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixConjugation_pow_mem {n : ℕ}
    (W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ)) (a : G n)
    (hW : ∀ V ∈ W, slMatrixConjugation a V ∈ W)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ W) (m : ℕ) :
    slMatrixConjugation (a ^ m) V ∈ W := by
  induction m with
  | zero => simpa only [pow_zero, slMatrixConjugation_one] using hV
  | succ m hm =>
    rw [pow_succ, slMatrixConjugation_mul]
    exact hW _ hm

theorem single_mem_of_isolating_diagonal_stability {n : ℕ}
    (W : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (i j : Fin n) (hij : i ≠ j)
    (hW : ∀ V ∈ W,
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) 1).val * V *
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) (-1)).val ∈ W)
    {V : Matrix (Fin n) (Fin n) ℝ} (hV : V ∈ W) :
    Matrix.single i j (V i j) ∈ W := by
  let ell := rootIsolationWeights i j
  have hell := rootIsolationWeights_sum i j
  let a := diagonalOneParameter ell hell (-1)
  have hstep : ∀ U ∈ W, slMatrixConjugation a U ∈ W := by
    intro U hU
    simpa only [a, slMatrixConjugation, diagonalOneParameter_neg, inv_inv] using hW U hU
  have hpower (m : ℕ) :
      (diagonalOneParameter ell hell (m : ℝ)).val * V *
        (diagonalOneParameter ell hell (-(m : ℝ))).val ∈ W := by
    have hm := slMatrixConjugation_pow_mem W a hstep hV m
    simpa only [a, slMatrixConjugation, diagonalOneParameter_neg,
      diagonalOneParameter_nat, inv_pow, inv_inv] using hm
  apply W.closed_of_finiteDimensional.mem_of_tendsto
    (tendsto_diagonal_matrix_root_projection i j hij V)
  exact Eventually.of_forall fun m => W.smul_mem _ (hpower m)

theorem full_root_of_isolating_diagonal_velocity {n : ℕ}
    (L : Subgroup (G n)) (hclosed : IsClosed (L : Set (G n)))
    (i j : Fin n) (hij : i ≠ j)
    (hW : ∀ V ∈ matrixVelocitySpace L,
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) 1).val * V *
      (diagonalOneParameter (rootIsolationWeights i j)
        (rootIsolationWeights_sum i j) (-1)).val ∈ matrixVelocitySpace L)
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ matrixVelocitySpace L) (hijV : V i j ≠ 0) :
    ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L := by
  have hs := single_mem_of_isolating_diagonal_stability (matrixVelocitySpace L) i j hij hW hV
  apply (root_direction_mem_velocitySpace_iff hij L hclosed).mp
  have hscale := (matrixVelocitySpace L).smul_mem (V i j)⁻¹ hs
  have he : (V i j)⁻¹ • Matrix.single i j (V i j) = Matrix.single i j (1 : ℝ) := by
    rw [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ hijV]
  rwa [he] at hscale

/-- Conditioning on a subgroup normalized by the diagonal action cannot
introduce velocity coefficients outside the ambient invariant-root
pattern. This applies in particular to a single coordinate block; the
individual conditional measures need not be diagonal invariant. -/
theorem ae_normalized_component_velocity_support_oai
    (d : ℕ) (H : Subgroup (G (d + 1)))
    (hAH : ∀ u : LogCoordinates d,
      diagonalFlow u ∈ Subgroup.normalizer (H : Set (G (d + 1))))
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ] :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X (d + 1))),
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup
        (condExpKernel μ (actionInvariantSigma H (X (d + 1))) z)),
      ∀ i j, ¬rootInvarianceRelation μ i j → V i j = 0 := by
  let m := actionInvariantSigma H (X (d + 1))
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  have hm : m ≤ xMeasurableSpace (d + 1) := actionInvariantSigma_le H (X (d + 1))
  have hdiag (i j : Fin (d + 1)) : ∀ᵐ z ∂μ.trim hm,
      ∀ V ∈ matrixVelocitySpace (invariantRightSubgroup (condExpKernel μ m z)),
        (diagonalOneParameter (rootIsolationWeights i j)
          (rootIsolationWeights_sum i j) 1).val * V *
        (diagonalOneParameter (rootIsolationWeights i j)
          (rootIsolationWeights_sum i j) (-1)).val ∈
          matrixVelocitySpace (invariantRightSubgroup (condExpKernel μ m z)) := by
    let ell := rootIsolationWeights i j
    have hell := rootIsolationWeights_sum i j
    have hpres : μ.map (fun x => rightAction x (diagonalOneParameter ell hell (-1))) = μ := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact (measurePreserving_smul
        (Multiplicative.ofAdd (fun k : Fin d => ell k.castSucc * (-1))) μ).map_eq
    have hnormal : diagonalOneParameter ell hell (-1) ∈
        Subgroup.normalizer (H : Set (G (d + 1))) := by
      rw [diagonalOneParameter_eq_diagonalFlow]
      exact hAH _
    exact ae_conditional_velocity_diagonal_stable H μ ell hell hnormal hpres
  have hno (i j : Fin (d + 1)) : ∀ᵐ z ∂μ.trim hm, ∀ hij : i ≠ j,
      (∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈
        invariantRightSubgroup (condExpKernel μ m z)) →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ invariantRightSubgroup μ := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · exact (ae_component_root_implies_ambient_root d H hAH μ hij).mono fun _ hz _ => hz
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hdiag i)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hno i))] with z hz hroot
  intro V hV i j hn
  by_contra hne
  have hij : i ≠ j := fun he => hn (Or.inl he)
  have hfull := full_root_of_isolating_diagonal_velocity
    (invariantRightSubgroup (condExpKernel μ m z))
    (isClosed_invariantRightSubgroup _) i j hij (hz i j) hV hne
  exact hn (Or.inr ⟨hij, hroot i j hij hfull⟩)

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.ae_normalized_component_velocity_support_oai := @OAI.DukePrimeDegree.ae_normalized_component_velocity_support_oai
