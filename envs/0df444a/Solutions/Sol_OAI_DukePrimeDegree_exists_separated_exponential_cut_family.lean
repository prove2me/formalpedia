-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_separated_exponential_cut_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:35:46.227762+00:00
-- url     : https://prove2.me/submissions/96fc5939-cbdf-49f9-8cac-ec4f53788990

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SummablePartitionBoundaries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing partition cuts with summable boundary returns

Almost every real cut of a measurable real-valued function has summable
strip masses for any summable sequence of widths. Invariant dynamics
therefore avoid those shrinking strips eventually almost everywhere.
This supplies the boundary control for partitions subordinate to
contracting root leaves.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

lemma measurable_realBoundaryStrip_mass (μ : Measure Y) [SFinite μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    Measurable (fun r => μ (realBoundaryStrip f r ε)) := by
  have hs : MeasurableSet {z : ℝ × Y | |f z.2-z.1| ≤ ε} := by
    simp only [abs_le]
    exact (measurableSet_le measurable_const ((hf.comp measurable_snd).sub measurable_fst)).inter
      (measurableSet_le ((hf.comp measurable_snd).sub measurable_fst) measurable_const)
  exact measurable_measure_prodMk_left hs

lemma lintegral_realBoundaryStrip_mass (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) (ε : ℝ) :
    (∫⁻ r : ℝ, μ (realBoundaryStrip f r ε)) = ENNReal.ofReal (2*ε) := by
  let S : Set (ℝ × Y) := {z | |f z.2-z.1| ≤ ε}
  have hS : MeasurableSet S := by
    simp only [S,abs_le]
    exact (measurableSet_le measurable_const ((hf.comp measurable_snd).sub measurable_fst)).inter
      (measurableSet_le ((hf.comp measurable_snd).sub measurable_fst) measurable_const)
  change (∫⁻ r : ℝ, μ (Prod.mk r ⁻¹' S)) = _
  rw [←Measure.prod_apply hS,Measure.prod_apply_symm hS]
  have hsection (x : Y) : (fun r : ℝ => (r,x)) ⁻¹' S = Icc (f x-ε) (f x+ε) := by
    ext r
    change |f x-r| ≤ ε ↔ f x-ε ≤ r ∧ r ≤ f x+ε
    rw [abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp_rw [hsection,Real.volume_Icc,show ∀ x : Y, f x+ε-(f x-ε)=2*ε by intro x; ring]
  simp only [lintegral_const,measure_univ,mul_one]

lemma fiber_null_of_summable_realBoundaryStrip_mass
    (μ : Measure Y) {f : Y → ℝ} (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (r : ℝ)
    (hr : (∑' n, μ (realBoundaryStrip f r (ε n))) ≠ ∞) :
    μ {x | f x=r} = 0 := by
  by_contra h
  have hle : (∑' _ : ℕ, μ {x | f x=r}) ≤ ∑' n, μ (realBoundaryStrip f r (ε n)) := by
    apply ENNReal.tsum_le_tsum
    intro n
    apply measure_mono
    intro x hx
    change |f x-r| ≤ ε n
    rw [hx,sub_self,abs_zero]
    exact hε n
  rw [ENNReal.tsum_const_eq_top_of_ne_zero h] at hle
  exact hr (top_le_iff.mp hle)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_QuantitativeCutAverage
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xBorelSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative selection of a real cut

A nonnegative cost with bounded total integral has a cut in any given
interval with cost at most twice the interval average. This will control
all dyadic boundary widths at once.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

theorem exists_cut_cost_le
    (F : ℝ → ℝ≥0∞) {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hI : (∫⁻ r, F r) ≤ ENNReal.ofReal C) :
    ∃ r ∈ Ioo a b, F r ≤ ENNReal.ofReal (2*C/(b-a)) := by
  by_contra h
  have hall : ∀ r ∈ Ioo a b, ENNReal.ofReal (2*C/(b-a)) ≤ F r := by
    intro r hr
    exact (lt_of_not_ge (fun hle => h ⟨r,hr,hle⟩)).le
  have hlower : ENNReal.ofReal (2*C/(b-a))*volume (Ioo a b) ≤
      ∫⁻ r in Ioo a b, F r := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hall r hr
  have hbound : ENNReal.ofReal (2*C) ≤ ENNReal.ofReal C := by
    have he : ENNReal.ofReal (2*C/(b-a))*volume (Ioo a b) = ENNReal.ofReal (2*C) := by
      rw [Real.volume_Ioo,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [(sub_pos.mpr hab).ne']
    rw [he] at hlower
    exact hlower.trans ((lintegral_mono' Measure.restrict_le_self le_rfl).trans hI)
  have := (ENNReal.ofReal_le_ofReal_iff hC.le).mp hbound
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets



theorem cube_grid_cover (d : ℕ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset (Fin d → ℝ),
      (∀ u ∈ s, ∀ i, |u i| ≤ R+1) ∧
      (s.card : ℝ) ≤ (2*R+2)^d / r^d ∧
      ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ R) →
        ∃ u ∈ s, ∀ i, |x i-u i| < r := by
  classical
  let N : ℕ := ⌈2*R/r⌉₊
  let g (k : Fin d → Fin (N+1)) : Fin d → ℝ := fun i => -R + (k i : ℕ)*r
  let s : Finset (Fin d → ℝ) := Finset.univ.image g
  have hN : (N:ℝ) < 2*R/r+1 := by
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) hr.le)
  have hNr : (N:ℝ)*r < 2*R+r := by
    have := (mul_lt_mul_iff_left₀ hr).mpr hN
    field_simp at this
    nlinarith
  refine ⟨s, ?_, ?_, ?_⟩
  · intro u hu i
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
    dsimp [g]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (k i).val) hr.le]
    · have hki : ((k i).val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (k i).isLt)
      nlinarith [mul_le_mul_of_nonneg_right hki hr.le]
  · have hcard : s.card ≤ (N+1)^d := by
      calc
        _ ≤ (Finset.univ : Finset (Fin d → Fin (N+1))).card := Finset.card_image_le
        _ = _ := by simp
    have hN1 : ((N+1:ℕ):ℝ) ≤ (2*R+2)/r := by
      apply (le_div_iff₀ hr).mpr
      push_cast
      nlinarith
    calc
      (s.card:ℝ) ≤ (((N+1)^d:ℕ):ℝ) := Nat.cast_le.mpr hcard
      _ = (((N+1:ℕ):ℝ))^d := Nat.cast_pow _ _
      _ ≤ ((2*R+2)/r)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hN1 d
      _ = _ := div_pow _ _ _
  · intro x hx
    have hx0 (i : Fin d) : 0 ≤ (x i+R)/r := by
      apply div_nonneg _ hr.le
      have := (abs_le.mp (hx i)).1
      linarith
    let k (i : Fin d) : Fin (N+1) := ⟨⌊(x i+R)/r⌋₊, by
      apply Nat.lt_succ_of_le
      apply (Nat.floor_mono ?_).trans (Nat.floor_le_ceil _)
      apply div_le_div_of_nonneg_right _ hr.le
      have := (abs_le.mp (hx i)).2
      linarith⟩
    refine ⟨g k, Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
    intro i
    have hlo := Nat.floor_le (hx0 i)
    have hhi := Nat.lt_floor_add_one ((x i+R)/r)
    have Hlo : (⌊(x i+R)/r⌋₊ : ℝ)*r ≤ x i+R := (le_div_iff₀ hr).mp hlo
    have Hhi : x i+R < ((⌊(x i+R)/r⌋₊ : ℝ)+1)*r := (div_lt_iff₀ hr).mp hhi
    dsimp [g,k]
    rw [abs_of_nonneg (by linarith)]
    linarith

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets


lemma left_div_entry_bound {n : ℕ} (g h : G n) {C b : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ i j, |g⁻¹.1 i j| ≤ C)
    (hgh : ∀ i j, |h.1 i j-g.1 i j| ≤ b) :
    ∀ i j, |(g⁻¹*h).1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ n*C*b := by
  intro i j
  have heq : (g⁻¹*h).1 - (1 : Matrix (Fin n) (Fin n) ℝ) = g⁻¹.1*(h.1-g.1) := by
    rw [Matrix.mul_sub]
    simp only [← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
  change |((g⁻¹*h).1-(1 : Matrix (Fin n) (Fin n) ℝ)) i j| ≤ _
  rw [heq,Matrix.mul_apply]
  calc
    |∑ k, g⁻¹.1 i k*(h.1-g.1) k j| ≤ ∑ k, |g⁻¹.1 i k*(h.1-g.1) k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, C*b := Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hg i k) (hgh k j) (abs_nonneg _) hC
    _ = n*C*b := by simp <;> ring



end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixLogLength
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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

lemma matrixLogLength_le_displacements {n : ℕ} (g : G n) :
    matrixLogLength g ≤ ‖g.val-1‖+‖(g⁻¹).val-1‖ := by
  have h₁ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+‖g.val-1‖)
  have h₂ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+‖(g⁻¹).val-1‖)
  unfold matrixLogLength
  linarith

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

lemma norm_sub_one_le_exp_matrixLogLength {n : ℕ} (g : G n) :
    ‖g.val-1‖ ≤ Real.exp (matrixLogLength g)-1 := by
  have hi : 0 ≤ Real.log (1+‖(g⁻¹).val-1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)])
  have he := Real.exp_le_exp.mpr (show Real.log (1+‖g.val-1‖) ≤ matrixLogLength g by
    unfold matrixLogLength
    linarith)
  rw [Real.exp_log (by positivity)] at he
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogDistance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientLogTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ConjugationRadius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative conjugation of local matrix balls

The logarithmic displacement length gives an explicit exponential loss
when a local quotient chart is transported by a group element.
-/

noncomputable section
open Set Matrix
open scoped Matrix.Norms.Operator Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrix_entry_abs_le_operator_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  have H : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun k => ∑ l, ‖A k l‖₊) (Finset.mem_univ i))
  change ‖A i j‖ ≤ ‖A‖
  exact_mod_cast H

lemma matrix_operator_norm_le_card_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hA : ∀ i j, |A i j| ≤ r) : ‖A‖ ≤ (n:ℝ)*r := by
  change ‖fun i => WithLp.toLp 1 (A i)‖ ≤ (n:ℝ)*r
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hr)]
  intro i
  rw [PiLp.norm_eq_of_L1]
  change (∑ j, ‖A i j‖) ≤ (n:ℝ)*r
  calc
    _ ≤ ∑ _j : Fin n, r := Finset.sum_le_sum (fun j _ => by simpa only [Real.norm_eq_abs] using hA i j)
    _ = _ := by simp

lemma specialLinear_norm_le_exp_length {n : ℕ} (hn : 0 < n) (g : G n) :
    ‖g.val‖ ≤ Real.exp (matrixLogLength g) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have h := norm_add_le (g.val-1) (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [sub_add_cancel,norm_one] at h
  have H := norm_sub_one_le_exp_matrixLogLength g
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DyadicBoundaryCuts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distance cuts with uniform quantitative boundary bounds

One cut controls all dyadic widths. The constant depends only on the
length of the interval from which the cut is selected, not the observable
or the probability measure.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

lemma lintegral_dyadicBoundaryCost (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) :
    (∫⁻ r, dyadicBoundaryCost μ f r) = 4 := by
  unfold dyadicBoundaryCost
  have hm (k : ℕ) : Measurable (fun r =>
      ENNReal.ofReal ((2:ℝ)^k) * μ (realBoundaryStrip f r ((1/4:ℝ)^k))) :=
    measurable_const.mul (measurable_realBoundaryStrip_mass μ hf _)
  rw [lintegral_tsum (fun k => (hm k).aemeasurable)]
  simp_rw [lintegral_const_mul _ (measurable_realBoundaryStrip_mass μ hf _),
    lintegral_realBoundaryStrip_mass μ hf]
  have he (k : ℕ) : ENNReal.ofReal ((2:ℝ)^k) * ENNReal.ofReal (2*(1/4:ℝ)^k) =
      ENNReal.ofReal (2*(1/2:ℝ)^k) := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = 2*((2:ℝ)^k*(1/4:ℝ)^k) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  simp_rw [he]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (summable_geometric_two.mul_left 2),tsum_mul_left,tsum_geometric_two]
  norm_num

theorem exists_dyadic_boundary_cut (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, μ {x | f x=r}=0 ∧
      ∀ k : ℕ, μ (realBoundaryStrip f r ((1/4:ℝ)^k)) ≤
        ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
  obtain ⟨r,hr,hcost⟩ := exists_cut_cost_le (dyadicBoundaryCost μ f)
    (by norm_num : (0:ℝ)<4) hab (by rw [lintegral_dyadicBoundaryCost μ hf]; norm_num)
  have hbound (k : ℕ) : μ (realBoundaryStrip f r ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
    have hterm := (ENNReal.le_tsum k (f := fun j : ℕ =>
      ENNReal.ofReal ((2:ℝ)^j)*μ (realBoundaryStrip f r ((1/4:ℝ)^j)))).trans hcost
    have hp : 0 ≤ (1/2:ℝ)^k := by positivity
    have H := mul_le_mul' (le_rfl : ENNReal.ofReal ((1/2:ℝ)^k) ≤
      ENNReal.ofReal ((1/2:ℝ)^k)) hterm
    have he : ENNReal.ofReal ((1/2:ℝ)^k)*(ENNReal.ofReal ((2:ℝ)^k)*
        μ (realBoundaryStrip f r ((1/4:ℝ)^k))) =
        μ (realBoundaryStrip f r ((1/4:ℝ)^k)) := by
      rw [←mul_assoc,←ENNReal.ofReal_mul hp,←mul_pow]
      norm_num
    have heR : ENNReal.ofReal ((1/2:ℝ)^k)*ENNReal.ofReal (2*4/(b-a)) =
        ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
      rw [←ENNReal.ofReal_mul hp]
      congr 1
      ring
    rwa [he,heR] at H
  refine ⟨r,hr,?_,hbound⟩
  apply fiber_null_of_summable_realBoundaryStrip_mass μ
    (fun k : ℕ => (1/4:ℝ)^k) (fun _ => by positivity) r
  have hsum := ENNReal.tsum_le_tsum hbound
  have he : (∑' k : ℕ, ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k)) < ∞ :=
    (summable_geometric_two.mul_left (8/(b-a))).tsum_ofReal_lt_top
  exact (lt_of_le_of_lt hsum he).ne

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuantitativeQuotientCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite quotient covers with quantitative size control

Entrywise grids of bounded representatives give open covers of the
logarithmic quotient balls. Each member has uniformly small relative
lifts, and the number of members has an explicit grid bound.
-/

noncomputable section
open Set Matrix
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_quantitative_quotient_cover {n : ℕ} (hn : 0 < n)
    (R r : ℝ) (hr : 0 < r) :
    let δ := min 1 (r/(4*(n:ℝ)*Real.exp (R+1)))
    ∃ (N : ℕ) (V : Fin N → Set (X n)),
      (N:ℝ) ≤ (2*Real.exp (R+1)+2)^(n*n)/δ^(n*n) ∧
      (∀ i, IsOpen (V i)) ∧
      {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R} ⊆ ⋃ i, V i ∧
      ∀ i, ∀ x ∈ V i, ∀ y ∈ V i,
        ∃ g ∈ matrixBall n r, rightAction x g = y := by
  classical
  let B := Real.exp (R+1)
  let δ := min 1 (r/(4*(n:ℝ)*B))
  have hB : 0 < B := Real.exp_pos _
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδr : δ ≤ r/(4*(n:ℝ)*B) := min_le_right _ _
  have hbudget : (n:ℝ)*B*(2*δ) ≤ r/2 := by
    have H := (le_div_iff₀ (show 0 < 4*(n:ℝ)*B by positivity)).mp hδr
    nlinarith
  obtain ⟨s,_,hcard,hcover⟩ := cube_grid_cover (n*n) hB.le hδ hδ1
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let q (g : G n) (t : Fin (n*n)) : ℝ :=
    g.val (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  let U (i : Fin (Fintype.card s)) : Set (G n) :=
    {g | matrixLogLength g < R+1 ∧ ∀ t, |q g t-(e i).val t| < δ}
  let V (i : Fin (Fintype.card s)) : Set (X n) :=
    Quotient.mk (QuotientGroup.rightRel (integralGroup n)) '' U i
  refine ⟨Fintype.card s,V,?_,?_,?_,?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro i
    apply (quotient_covering n).isOpenMap
    apply IsOpen.inter (isOpen_lt (continuous_matrixLogLength n) continuous_const)
    change IsOpen {g : G n | ∀ t, |q g t-(e i).val t| < δ}
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro t
    apply isOpen_lt _ continuous_const
    dsimp [q]
    fun_prop
  · intro x hx
    obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt
      (Quotient.mk _ (1 : G n)) x (by norm_num : (0:ℝ)<1)
    have hgR : matrixLogLength g < R+1 := by
      have H : quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R := hx
      linarith
    have hgB : ∀ t, |q g t| ≤ B := by
      intro t
      exact (matrix_entry_abs_le_operator_norm g.val _ _).trans
        ((specialLinear_norm_le_exp_length hn g).trans
          (Real.exp_le_exp.mpr hgR.le))
    obtain ⟨c,hc,hgc⟩ := hcover (q g) hgB
    apply mem_iUnion.mpr
    refine ⟨e.symm ⟨c,hc⟩,g,?_,?_⟩
    · exact ⟨hgR,by simpa using hgc⟩
    · change Quotient.mk _ ((1 : G n)*g) = x at hg
      simpa only [one_mul] using hg
  · intro i x hx y hy
    obtain ⟨g,hg,rfl⟩ := hx
    obtain ⟨h,hh,rfl⟩ := hy
    have hginv : ∀ j k, |(g⁻¹).val j k| ≤ B := by
      intro j k
      apply (matrix_entry_abs_le_operator_norm _ j k).trans
      apply (specialLinear_norm_le_exp_length hn g⁻¹).trans
      rw [matrixLogLength_inv]
      exact Real.exp_le_exp.mpr hg.1.le
    have hdiff : ∀ j k, |h.val j k-g.val j k| ≤ 2*δ := by
      intro j k
      have hg' := hg.2 (finProdFinEquiv (j,k))
      have hh' := hh.2 (finProdFinEquiv (j,k))
      simp only [q,Equiv.symm_apply_apply] at hg' hh'
      calc
        _ = |(h.val j k-(e i).val (finProdFinEquiv (j,k))) +
            ((e i).val (finProdFinEquiv (j,k))-g.val j k)| := by congr 1; ring
        _ ≤ |h.val j k-(e i).val (finProdFinEquiv (j,k))| +
            |(e i).val (finProdFinEquiv (j,k))-g.val j k| := abs_add_le _ _
        _ ≤ 2*δ := by rw [abs_sub_comm ((e i).val _)]; linarith
    refine ⟨g⁻¹*h,?_,?_⟩
    · intro j k
      exact ((left_div_entry_bound g h hB.le hginv hdiff j k).trans hbudget).trans_lt
        (by linarith)
    · change Quotient.mk _ (g*(g⁻¹*h)) = Quotient.mk _ h
      congr 1
      group

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SmallMatrixLength
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative logarithmic length near the identity

The algebraic inverse identity bounds the inverse norm by two on a
half-unit operator ball. Consequently logarithmic length is bounded by
three times the displacement norm there.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

lemma specialLinear_inverse_norm_le_two {n : ℕ} (hn : 0 < n)
    (g : G n) (hg : ‖g.val-1‖ ≤ 1/2) : ‖(g⁻¹).val‖ ≤ 2 := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he : (g⁻¹).val = 1-(g⁻¹).val*(g.val-1) := by
    rw [Matrix.mul_sub,Matrix.mul_one]
    have hmul : (g⁻¹).val*g.val = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      change (g⁻¹*g).val=1
      simp
    rw [hmul]
    abel
  have hbound : ‖(g⁻¹).val‖ ≤ 1+‖(g⁻¹).val‖*‖g.val-1‖ := by
    calc
      _ = ‖1-(g⁻¹).val*(g.val-1)‖ := congrArg norm he
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖+‖(g⁻¹).val*(g.val-1)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_one]
        exact add_le_add le_rfl (norm_mul_le (g⁻¹).val (g.val-1))
  nlinarith [mul_le_mul_of_nonneg_left hg (norm_nonneg (g⁻¹).val)]

lemma matrixLogLength_le_three_norm {n : ℕ} (hn : 0 < n)
    (g : G n) (hg : ‖g.val-1‖ ≤ 1/2) :
    matrixLogLength g ≤ 3*‖g.val-1‖ := by
  have hi := specialLinear_inverse_norm_le_two hn g hg
  have he : (g⁻¹).val-1 = -((g⁻¹).val*(g.val-1)) := by
    rw [Matrix.mul_sub,Matrix.mul_one]
    have hmul : (g⁻¹).val*g.val = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      change (g⁻¹*g).val=1
      simp
    rw [hmul]
    abel
  have hdiff : ‖(g⁻¹).val-1‖ ≤ 2*‖g.val-1‖ := by
    rw [he,norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have H := matrixLogLength_le_displacements g
  linarith

lemma matrixLogLength_le_three_card_radius {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : (n:ℝ)*r ≤ 1/2)
    {g : G n} (hg : g ∈ matrixBall n r) :
    matrixLogLength g ≤ 3*(n:ℝ)*r := by
  have hnorm := matrix_operator_norm_le_card_mul (g.val-1) hr (fun i j => (hg i j).le)
  exact (matrixLogLength_le_three_norm hn g (hnorm.trans hsmall)).trans (by nlinarith)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuantitativeDistanceNet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative distance nets on logarithmic quotient balls

Finite matrix grids give nets for the intrinsic quotient distance. In
the other direction a small quotient distance gives a small actual
right lift, which is what the future-fiber construction needs.
-/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_quantitative_distance_net {n : ℕ} (hn : 0 < n)
    (R s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ (N : ℕ) (z : Fin N → X n), (N:ℝ) ≤ quotientNetBound n R s ∧
      ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
        ∃ i, quotientLogDistance (z i) x < s := by
  classical
  let r := s/(12*(n:ℝ))
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r] <;> positivity
  have hnr : (n:ℝ)*r=s/12 := by dsimp [r]; field_simp
  have h3nr : 3*(n:ℝ)*r=s/4 := by nlinarith [hnr]
  have hsmall : (n:ℝ)*r ≤ 1/2 := by rw [hnr]; linarith
  obtain ⟨N,V,hN,hopen,hcover,hrel⟩ := exists_quantitative_quotient_cover hn R r hr
  let z (i : Fin N) : X n :=
    if h : (V i).Nonempty then h.choose else Quotient.mk _ (1 : G n)
  refine ⟨N,z,?_,?_⟩
  · exact hN
  · intro x hx
    obtain ⟨i,hxi⟩ := mem_iUnion.mp (hcover hx)
    have hne : (V i).Nonempty := ⟨x,hxi⟩
    have hzi : z i ∈ V i := by
      simp only [z,dite_eq_left hne]
      exact hne.choose_spec
    obtain ⟨g,hg,hgx⟩ := hrel i (z i) hzi x hxi
    refine ⟨i,?_⟩
    have H := (quotientLogDistance_le_length (z i) x g hgx).trans
      (matrixLogLength_le_three_card_radius hn hr.le hsmall hg)
    rw [h3nr] at H
    linarith

theorem exists_matrix_lift_of_logDistance_lt {n : ℕ}
    {r : ℝ} (hr : 0 < r) {x y : X n}
    (hxy : quotientLogDistance x y < Real.log (1+r)) :
    ∃ g ∈ matrixBall n r, rightAction x g=y := by
  obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt x y (sub_pos.mpr hxy)
  have hnorm : ‖g.val-1‖ < r := norm_sub_one_lt_of_matrixLogLength_lt g hr (by linarith)
  refine ⟨g,?_,hg⟩
  intro i j
  exact (matrix_entry_abs_le_operator_norm (g.val-1) i j).trans_lt hnorm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_DistanceCutBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size bounds for the explicit quotient distance cuts -/

noncomputable section
namespace DukePrimeDegree

lemma quotientNetBound_le_power {n : ℕ} (hn : 0 < n)
    {R s : ℝ} (hR : 0 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1) :
    quotientNetBound n R s ≤
      (192*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/s)^(n*n) := by
  let E := Real.exp (R+1)
  have hE : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (by linarith)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have h4 : (1:ℝ) ≤ 4*(n:ℝ)*E := by nlinarith
  have h12 : (1:ℝ) ≤ 12*(n:ℝ) := by linarith
  have hmin : s/(12*(n:ℝ))/(4*(n:ℝ)*E) ≤ 1 :=
    ((div_le_self (by positivity) h4).trans (div_le_self hs.le h12)).trans hs1
  change (2*E+2)^(n*n)/(min 1 (s/(12*(n:ℝ))/(4*(n:ℝ)*E)))^(n*n) ≤ _
  rw [min_eq_right hmin,←div_pow]
  have heq : (2*E+2)/(s/(12*(n:ℝ))/(4*(n:ℝ)*E)) =
      48*(n:ℝ)*(n:ℝ)*E*(2*E+2)/s := by
    field_simp
    ring
  have he2 : E*E=Real.exp (2*(R+1)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  apply pow_le_pow_left₀ (by positivity)
  rw [heq]
  apply div_le_div_of_nonneg_right _ hs.le
  calc
    _ ≤ 48*(n:ℝ)*(n:ℝ)*E*(4*E) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by rw [←he2]; ring

lemma half_le_log_one_add {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r/2 ≤ Real.log (1+r) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hr)
  apply (le_div_iff₀ (by linarith : 0 < r+2)).mpr
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]

theorem distanceCut_size_bound {n : ℕ} (hn : 0 < n)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    quotientNetBound n R (Real.log (1+r)/4) * (48/Real.log (1+r)) ≤
      (1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/r)^(n*n) * (96/r) := by
  let τ := Real.log (1+r)
  have hτ : 0 < τ := Real.log_pos (by linarith)
  have hτlow : r/2 ≤ τ := half_le_log_one_add hr.le hr1
  have hτhi : τ ≤ r := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+r by linarith)
    dsimp [τ]
    linarith
  have hnet := quotientNetBound_le_power hn hR (by positivity : 0 < τ/4)
    (show τ/4 ≤ 1 by linarith)
  have hb : 192*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/(τ/4) ≤
      1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/r := by
    apply (div_le_div_iff₀ (by positivity) hr).mpr
    have hp : 0 ≤ 384*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hτlow hp]
  have hc : 48/τ ≤ 96/r := by
    apply (div_le_div_iff₀ hτ hr).mpr
    linarith
  exact mul_le_mul (hnet.trans (pow_le_pow_left₀ (by positivity) hb _)) hc
    (by positivity) (by positivity)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ExponentialCutSize
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential size control for cuts on increasing quotient balls -/

noncomputable section
namespace DukePrimeDegree

theorem distanceCut_size_exponential {n : ℕ} (hn : 0 < n)
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K > 0, ∃ C ≥ 0, ∀ m : ℕ,
      quotientNetBound n (A*(m:ℝ)+R₀) (Real.log (1+a*Real.exp (-B*(m:ℝ)))/4) *
        (48/Real.log (1+a*Real.exp (-B*(m:ℝ)))) ≤ K*Real.exp (C*(m:ℝ)) := by
  let Q := 1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(R₀+1))/a
  let K := Q^(n*n)*(96/a)
  let C := ((n*n:ℕ):ℝ)*(2*A+B)+B
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hQ : 0 < Q := by dsimp [Q] <;> positivity
  have hK : 0 < K := mul_pos (pow_pos hQ _) (div_pos (by norm_num) ha)
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  refine ⟨K,hK,C,hC,?_⟩
  intro m
  let r := a*Real.exp (-B*(m:ℝ))
  have hr : 0 < r := mul_pos ha (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    have he : Real.exp (-B*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) m)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans (by simpa using ha1)
  have hsize := distanceCut_size_bound hn
    (show 0 ≤ A*(m:ℝ)+R₀ by positivity) hr hr1
  apply hsize.trans
  have he₁ : Real.exp (2*(A*(m:ℝ)+R₀+1)) =
      Real.exp (2*(R₀+1))*Real.exp (2*A*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have he₂ : Real.exp ((2*A+B)*(m:ℝ)) =
      Real.exp (2*A*(m:ℝ))*Real.exp (B*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have he₃ : Real.exp (-B*(m:ℝ)) = (Real.exp (B*(m:ℝ)))⁻¹ := by
    rw [←Real.exp_neg]
    congr 1
    ring
  have hratio : 1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(A*(m:ℝ)+R₀+1))/r =
      Q*Real.exp ((2*A+B)*(m:ℝ)) := by
    dsimp [r,Q]
    rw [he₁,he₂,he₃]
    field_simp
  have hratio' : 96/r = (96/a)*Real.exp (B*(m:ℝ)) := by
    dsimp [r]
    rw [he₃]
    field_simp
  rw [hratio,hratio',mul_pow,←Real.exp_nat_mul]
  have he₄ : Real.exp (((n*n:ℕ):ℝ)*((2*A+B)*(m:ℝ)))*Real.exp (B*(m:ℝ)) =
      Real.exp (C*(m:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    dsimp [C]
    ring
  calc
    _ = K*(Real.exp (((n*n:ℕ):ℝ)*((2*A+B)*(m:ℝ)))*Real.exp (B*(m:ℝ))) := by
      dsimp [K]
      ring
    _ ≤ _ := by rw [he₄]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SeparatedQuotientNet
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated quotient-distance nets

Thinning the existing quantitative net retains its cardinality bound and
adds separation. This is the local packing input for controlling how
many covering labels can meet one small image cell.
-/

noncomputable section
open Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_separated_quotient_subnet {n N : ℕ} (z : Fin N → X n)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ S : Finset (Fin N),
      (S : Set (Fin N)).Pairwise (fun i j => r < quotientLogDistance (z i) (z j)) ∧
      ∀ i, ∃ j ∈ S, quotientLogDistance (z i) (z j) ≤ r := by
  classical
  let F : Finset (Finset (Fin N)) := Finset.univ.filter
    (fun S => (S : Set (Fin N)).Pairwise (fun i j => r < quotientLogDistance (z i) (z j)))
  have hF : F.Nonempty := ⟨∅,by simp [F]⟩
  obtain ⟨S,hS,hmax⟩ := F.exists_max_image Finset.card hF
  have hsep : (S : Set (Fin N)).Pairwise (fun i j => r < quotientLogDistance (z i) (z j)) :=
    (Finset.mem_filter.mp hS).2
  refine ⟨S,hsep,?_⟩
  intro i
  by_contra hn
  have hfar (j : Fin N) (hj : j ∈ S) : r < quotientLogDistance (z i) (z j) := by
    exact lt_of_not_ge (fun h => hn ⟨j,hj,h⟩)
  have hi : i ∉ S := by
    intro hi
    have hh := hfar i hi
    rw [quotientLogDistance_self] at hh
    linarith
  have hnew : ((insert i S : Finset (Fin N)) : Set (Fin N)).Pairwise
      (fun a b => r < quotientLogDistance (z a) (z b)) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hai | has
    · subst a
      rcases Finset.mem_insert.mp hb with hbi | hbs
      · subst b
        exact (hab rfl).elim
      · exact hfar b hbs
    · rcases Finset.mem_insert.mp hb with hbi | hbs
      · subst b
        rw [quotientLogDistance_symm]
        exact hfar a has
      · exact hsep has hbs hab
  have hmem : insert i S ∈ F := by simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]; exact hnew
  have hc := hmax (insert i S) hmem
  rw [Finset.card_insert_of_notMem hi] at hc
  omega

theorem exists_separated_quantitative_distance_net {n : ℕ} (hn : 0 < n)
    (R r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (N : ℕ) (z : Fin N → X n),
      (N:ℝ) ≤ quotientNetBound n R (r/2) ∧
      (∀ i j, i ≠ j → r/2 < quotientLogDistance (z i) (z j)) ∧
      ∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
        ∃ i, quotientLogDistance (z i) x < r := by
  classical
  obtain ⟨M,w,hM,hcover⟩ := exists_quantitative_distance_net hn R (r/2)
    (by positivity) (by linarith)
  obtain ⟨S,hsep,hnet⟩ := exists_separated_quotient_subnet w (show 0 ≤ r/2 by positivity)
  let e : Fin S.card ≃ S := S.equivFin.symm
  let z : Fin S.card → X n := fun i => w (e i).val
  refine ⟨S.card,z,?_,?_,?_⟩
  · have hcN : S.card ≤ M := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    have hc : (S.card:ℝ) ≤ M := by exact_mod_cast hcN
    exact hc.trans hM
  · intro i j hij
    apply hsep (e i).prop (e j).prop
    intro he
    exact hij (e.injective (Subtype.ext he))
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    obtain ⟨j,hj,hd⟩ := hnet i
    refine ⟨e.symm ⟨j,hj⟩,?_⟩
    have htri := quotientLogDistance_triangle (w j) (w i) x
    rw [quotientLogDistance_symm (w j) (w i)] at htri
    change quotientLogDistance (w (e (e.symm ⟨j,hj⟩)).val) x < r
    simp only [Equiv.apply_symm_apply]
    linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SeparatedControlledCuts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated quotient observations with controlled distance boundaries

Each logarithmic ball admits finitely many distance cuts that cover it,
have small relative lifts, and satisfy a common dyadic boundary estimate.
Both the number of cuts and their boundary constants are explicit.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_separated_controlled_distance_cuts {n : ℕ} (hn : 0 < n)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (R r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    let τ := Real.log (1+r)
    ∃ (N : ℕ) (z : Fin N → X n) (c : Fin N → ℝ),
      (N:ℝ) ≤ quotientNetBound n R (τ/8) ∧
      (∀ i j, i ≠ j → τ/8 < quotientLogDistance (z i) (z j)) ∧
      (∀ i, τ/3 < c i ∧ c i < τ/2 ∧
        μ {x | quotientLogDistance (z i) x=c i}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z i)) (c i) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (48/τ*(1/2:ℝ)^k)) ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R →
        ∃ i, quotientLogDistance (z i) x < c i) ∧
      ∀ i, ∀ x, quotientLogDistance (z i) x < c i →
        ∀ y, quotientLogDistance (z i) y < c i →
        ∃ g ∈ matrixBall n r, rightAction x g=y := by
  classical
  let τ := Real.log (1+r)
  have hτ : 0 < τ := Real.log_pos (by linarith)
  have hτr : τ ≤ r := by
    have H := Real.log_le_sub_one_of_pos (show 0 < 1+r by linarith)
    dsimp [τ]
    linarith
  obtain ⟨N,z,hN,hsep,hcover⟩ := exists_separated_quantitative_distance_net hn R (τ/4)
    (by positivity) (by linarith)
  have hex (i : Fin N) := exists_dyadic_boundary_cut μ
    (continuous_quotientLogDistance n (z i)).measurable
    (show τ/3 < τ/2 by linarith)
  choose c hc hnull hboundary using hex
  have hN' : (N:ℝ) ≤ quotientNetBound n R (τ/8) := by
    have he : τ/4/2=τ/8 := by ring
    simpa only [he] using hN
  have hsep' : ∀ i j, i ≠ j → τ/8 < quotientLogDistance (z i) (z j) := by
    intro i j hij
    have he : τ/4/2=τ/8 := by ring
    simpa only [he] using hsep i j hij
  refine ⟨N,z,c,hN',hsep',?_,?_,?_⟩
  · intro i
    refine ⟨(hc i).1,(hc i).2,hnull i,?_⟩
    intro k
    convert hboundary i k using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    change 48/τ*(1/2:ℝ)^k = 8/(τ/2-τ/3)*(1/2:ℝ)^k
    have hne := hτ.ne'
    field_simp [hne]
    ring
  · intro x hx
    obtain ⟨i,hi⟩ := hcover x hx
    exact ⟨i,hi.trans (by linarith [(hc i).1])⟩
  · intro i x hx y hy
    apply exists_matrix_lift_of_logDistance_lt hr
    have H := quotientLogDistance_triangle x (z i) y
    rw [quotientLogDistance_symm x (z i)] at H
    change quotientLogDistance x y < τ
    linarith [(hc i).2]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SeparatedCutFamily
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential size control for separated covering cuts -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma quotientNetBound_half_le {n : ℕ} (hn : 0 < n) (R : ℝ)
    {s : ℝ} (hs : 0 < s) :
    quotientNetBound n R (s/2) ≤ (2:ℝ)^(n*n)*quotientNetBound n R s := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let A : ℝ := (s/(12*(n:ℝ)))/(4*(n:ℝ)*Real.exp (R+1))
  have hA : 0 < A := by dsimp [A] <;> positivity
  let D := min (1:ℝ) A
  let E := min (1:ℝ) (A/2)
  have hD : 0 < D := lt_min zero_lt_one hA
  have hE : 0 < E := lt_min zero_lt_one (by positivity)
  have hd : D/2 ≤ E := by
    apply le_min
    · have hh := min_le_left (1:ℝ) A
      dsimp [D]
      linarith
    · exact div_le_div_of_nonneg_right (min_le_right (1:ℝ) A) (by norm_num)
  have hp := pow_le_pow_left₀ (show 0 ≤ D/2 by positivity) hd (n*n)
  have he : ((s/2)/(12*(n:ℝ)))/(4*(n:ℝ)*Real.exp (R+1))=A/2 := by
    dsimp [A]
    ring
  unfold quotientNetBound
  rw [he]
  change (2*Real.exp (R+1)+2)^(n*n)/E^(n*n) ≤
    (2:ℝ)^(n*n)*((2*Real.exp (R+1)+2)^(n*n)/D^(n*n))
  calc
    _ ≤ (2*Real.exp (R+1)+2)^(n*n)/(D/2)^(n*n) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity : 0 < D/2) _) hp
    _ = _ := by rw [div_pow]; field_simp

lemma separatedCut_size_exponential {n : ℕ} (hn : 0 < n)
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K > 0, ∃ C ≥ 0, ∀ m : ℕ,
      quotientNetBound n (A*(m:ℝ)+R₀) (Real.log (1+a*Real.exp (-B*(m:ℝ)))/8) *
        (48/Real.log (1+a*Real.exp (-B*(m:ℝ)))) ≤ K*Real.exp (C*(m:ℝ)) := by
  obtain ⟨K,hK,C,hC,hbound⟩ := distanceCut_size_exponential hn hA hB hR₀ ha ha1
  refine ⟨(2:ℝ)^(n*n)*K,by positivity,C,hC,?_⟩
  intro m
  let τ := Real.log (1+a*Real.exp (-B*(m:ℝ)))
  have hτ : 0 < τ := Real.log_pos (by have := Real.exp_pos (-B*(m:ℝ)); nlinarith)
  have hnB := quotientNetBound_half_le hn (A*(m:ℝ)+R₀) (show 0 < τ/4 by positivity)
  have he : τ/4/2=τ/8 := by ring
  rw [he] at hnB
  have hmul := mul_le_mul_of_nonneg_right hnB (show 0 ≤ 48/τ by positivity)
  have h := mul_le_mul_of_nonneg_left (hbound m) (show 0 ≤ (2:ℝ)^(n*n) by positivity)
  change quotientNetBound n (A*(m:ℝ)+R₀) (τ/8)*(48/τ) ≤ _
  calc
    _ ≤ (2:ℝ)^(n*n)*(quotientNetBound n (A*(m:ℝ)+R₀) (τ/4)*(48/τ)) := by
      convert hmul using 1 <;> first | rfl | ring
    _ ≤ (2:ℝ)^(n*n)*(K*Real.exp (C*(m:ℝ))) := h
    _ = _ := by ring

theorem exists_separated_exponential_cut_family_oai {n : ℕ} (hn : 0 < n)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
    let τ := fun m => Real.log (1+r m)
    ∃ (N : ℕ → ℕ) (z : ∀ m, Fin (N m) → X n) (c : ∀ m, Fin (N m) → ℝ)
      (K C : ℝ), 0 < K ∧ 0 ≤ C ∧ ∀ m,
      ((N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) ∧
      (∀ i j, i ≠ j → τ m/8 < quotientLogDistance (z m i) (z m j)) ∧
      (∀ i, τ m/3 < c m i ∧ c m i < τ m/2 ∧
        μ {x | quotientLogDistance (z m i) x=c m i}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z m i)) (c m i) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (48/τ m*(1/2:ℝ)^k)) ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ A*(m:ℝ)+R₀ →
        ∃ i, quotientLogDistance (z m i) x < c m i) ∧
      ∀ i, ∀ x, quotientLogDistance (z m i) x < c m i →
        ∀ y, quotientLogDistance (z m i) y < c m i →
        ∃ g ∈ matrixBall n (r m), rightAction x g=y := by
  classical
  let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
  let τ := fun m => Real.log (1+r m)
  have hr (m : ℕ) : 0 < r m := mul_pos ha (Real.exp_pos _)
  have hr1 (m : ℕ) : r m ≤ 1 := by
    have he : Real.exp (-B*(m:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (by nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) m)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans (by simpa using ha1)
  have hτ (m : ℕ) : 0 < τ m := Real.log_pos (by linarith [hr m])
  have hex (m : ℕ) := exists_separated_controlled_distance_cuts hn μ
    (A*(m:ℝ)+R₀) (r m) (hr m) (hr1 m)
  choose N z c hN hsep hcut hcover hsmall using hex
  obtain ⟨K,hK,C,hC,hsize⟩ := separatedCut_size_exponential hn hA hB hR₀ ha ha1
  refine ⟨N,z,c,K,C,hK,hC,?_⟩
  intro m
  refine ⟨?_,hsep m,hcut m,hcover m,hsmall m⟩
  have hreal : (N m:ℝ)*(48/τ m) ≤ K*Real.exp (C*(m:ℝ)) :=
    (mul_le_mul_of_nonneg_right (hN m)
      (div_nonneg (by norm_num) (hτ m).le)).trans (hsize m)
  have H := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] at H

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_separated_exponential_cut_family_oai := @OAI.DukePrimeDegree.exists_separated_exponential_cut_family_oai
