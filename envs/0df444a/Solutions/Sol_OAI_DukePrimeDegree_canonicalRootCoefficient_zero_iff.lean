-- Prove2me | solution 1 for OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:49.562599+00:00
-- url     : https://prove2.me/submissions/e20e4590-fec3-46ad-b23a-611969b31851

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.infinitePlace_mult_smul
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
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal


namespace PrimeDegreePackets

lemma ae_eq_of_measurePreserving_ennreal_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f x ≤ f (T x)) : f =ᵐ[μ] f ∘ T := by
  have hint : ∫⁻ x, f x ∂μ < ∞ :=
    (lintegral_mono_ae hf1).trans_lt (by simp)
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  exact ae_eq_of_ae_le_of_lintegral_le hmono hint.ne
    (hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving) he.le

lemma ae_eq_of_measurePreserving_ennreal_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x) : f =ᵐ[μ] f ∘ T := by
  have hfT := hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  have hint : ∫⁻ x, f (T x) ∂μ < ∞ := by
    rw [he]
    exact (lintegral_mono_ae hf1).trans_lt (by simp)
  exact (ae_eq_of_ae_le_of_lintegral_le hmono hint.ne hf he.ge).symm

lemma realScaling_preimage_singleton (c : ℝ) (hc : c ≠ 0) :
    (Homeomorph.mulLeft₀ c hc) ⁻¹' ({0} : Set ℝ) = {0} := by
  ext x
  change c*x=0 ↔ x=0
  exact mul_eq_zero.trans (or_iff_right hc)

lemma realScaling_preimage_unitBall_subset (c : ℝ) (hc : 1 ≤ c) :
    (Homeomorph.mulLeft₀ c (ne_of_gt (zero_lt_one.trans_le hc))) ⁻¹' Metric.ball (0:ℝ) 1 ⊆
      Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_nonneg (zero_le_one.trans hc)] at hx
  nlinarith [abs_nonneg x]

lemma realScaling_unitBall_subset_preimage (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Metric.ball (0:ℝ) 1 ⊆ (Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_pos hc]
  nlinarith [abs_nonneg x]

lemma normalized_realScaling_atom (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} =
      (ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1))⁻¹ * ν {0} := by
  change (ν.map (Homeomorph.mulLeft₀ c hc) (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc) {0} = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable (measurableSet_singleton 0),
    realScaling_preimage_singleton]

 

theorem ae_atom_eq_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (ν : α → Measure ℝ) (hν : AEMeasurable ν μ)
    (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (c : ℝ) (hc : 0 < c)
    (hcov : ∀ᵐ x ∂μ, ν (T x) =
      anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} = ν (T x) {0} := by
  have hm : AEMeasurable (fun x => ν x {0}) μ :=
    (Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable hν
  have hle : ∀ᵐ x ∂μ, ν x {0} ≤ 1 := by
    filter_upwards [hball] with x hx
    rw [←hx]
    exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one))
  rcases le_total 1 c with h | h
  · apply ae_eq_of_measurePreserving_ennreal_le μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) ≤ 1 := by
      rw [←hx]
      exact measure_mono (realScaling_preimage_unitBall_subset c h)
    calc
      ν x {0} = 1 * ν x {0} := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (ENNReal.one_le_inv.mpr hb) le_rfl
  · apply ae_eq_of_measurePreserving_ennreal_ge μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : 1 ≤ ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) := by
      rw [←hx]
      exact measure_mono (realScaling_unitBall_subset_preimage c hc h)
    calc
      _ ≤ 1 * ν x {0} := mul_le_mul' (ENNReal.inv_le_one.mpr hb) le_rfl
      _ = ν x {0} := one_mul _

lemma scaling_ball_mass_of_atom_eq (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0)
    (h0 : ν {0} ≠ 0) (hT : ν {0} ≠ ∞)
    (he : anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} = ν {0}) :
    ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1) = 1 := by
  rw [normalized_realScaling_atom] at he
  have H := congrArg (fun a : ℝ≥0∞ => a*(ν {0})⁻¹) he
  rw [ENNReal.mul_inv_cancel_right h0 hT,ENNReal.mul_inv_cancel h0 hT] at H
  exact ENNReal.inv_eq_one.mp H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma real_iInter_ball_inv_nat :
    (⋂ m : ℕ, Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) = {0} := by
  ext x
  simp only [mem_iInter,mem_singleton_iff,Metric.mem_ball,Real.dist_eq,sub_zero]
  constructor
  · intro h
    by_contra hx
    have hx0 : 0 < |x| := abs_pos.mpr hx
    obtain ⟨m,hm⟩ := exists_nat_gt (|x|⁻¹)
    have hm0 : (0:ℝ) < m+1 := by positivity
    have hh := h m
    have hl : (m+1:ℝ)⁻¹ < |x| := by
      rw [←one_div]
      apply (one_div_lt hm0 hx0).mpr
      simpa only [one_div] using hm.trans (by linarith : (m:ℝ) < m+1)
    exact (not_lt_of_ge hl.le) hh
  · rintro rfl m
    simp only [abs_zero]
    positivity

lemma realMeasure_eq_dirac_of_ball_masses (ν : Measure ℝ)
    (hsmall : ∀ m : ℕ, ν (Metric.ball 0 ((m+1:ℝ)⁻¹)) = 1)
    (hlarge : ∀ m : ℕ, ν (Metric.ball 0 (m+1:ℝ)) = 1) : ν = Measure.dirac 0 := by
  have hmono : Monotone (fun m : ℕ => Metric.ball (0:ℝ) (m+1:ℝ)) := by
    intro a b hab
    exact Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hu : ν univ = 1 := by
    rw [← Metric.iUnion_ball_nat_succ (0:ℝ),hmono.measure_iUnion]
    simp only [hlarge,iSup_const]
  have hanti : Antitone (fun m : ℕ => Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have h0 : ν {0} = 1 := by
    rw [←real_iInter_ball_inv_nat,hanti.measure_iInter
      (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet) ⟨0,by rw [hsmall]; exact ENNReal.one_ne_top⟩]
    simp only [hsmall,iInf_const]
  let : IsFiniteMeasure ν := ⟨by rw [hu]; exact ENNReal.one_lt_top⟩
  have hc : ν ({0} : Set ℝ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton _) (by finiteness),hu,h0,tsub_self]
  ext s hs
  by_cases hx : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply_of_mem hx]
    apply le_antisymm
    · simpa only [hu] using measure_mono (subset_univ s) (μ := ν)
    · rw [←h0]
      exact measure_mono (singleton_subset_iff.mpr hx)
  · simp only [Measure.dirac_apply,indicator_of_notMem hx]
    apply le_antisymm _ bot_le
    exact (measure_mono (subset_compl_singleton_iff.mpr hx)).trans hc.le

 

theorem ae_dirac_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : α → Measure ℝ)
    (hν : AEMeasurable ν μ) (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (hscale : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α,
      MeasurePreserving T μ μ ∧ ∀ᵐ x ∂μ, ν (T x) =
        anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x = Measure.dirac 0 := by
  have H (c : ℝ) (hc : 0 < c) : ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x (Metric.ball 0 (1/c)) = 1 := by
    obtain ⟨T,hT,hcov⟩ := hscale c hc
    have he := ae_atom_eq_of_scaling_covariance μ hT ν hν hball c hc hcov
    filter_upwards [hball,hcov,he] with x hx hc' he' h0
    have hT' : ν x {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
      rw [←hx]
      exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one)))
    have hh := scaling_ball_mass_of_atom_eq (ν x) c hc.ne' h0 hT' (by rw [←hc']; exact he'.symm)
    rwa [realScaling_preimage_ball c 1 hc] at hh
  have HS := ae_all_iff.mpr (fun m : ℕ => H (m+1) (by positivity))
  have HL := ae_all_iff.mpr (fun m : ℕ => H ((m+1:ℝ)⁻¹) (by positivity))
  filter_upwards [HS,HL] with x hs hl h0
  apply realMeasure_eq_dirac_of_ball_masses (ν x)
  · intro m
    simpa only [one_div] using hs m h0
  · intro m
    simpa only [one_div,inv_inv] using hl m h0

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_atom_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} ≠ 0 →
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply ae_dirac_of_scaling_covariance μ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
  intro c hc
  let ell := coordinateContractionWeights d j
  have hell : ∑ k, ell k = 0 := coordinateContractionWeights_sum d j
  let t := Real.log c / (d+1:ℝ)
  let a := diagonalOneParameter ell hell t
  have hinv : μ.map (fun x => rightAction x a) = μ := by
    rw [show a = diagonalFlow (fun k : Fin d => ell k.castSucc*t) from
      diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  refine ⟨(fun x => rightAction x a),⟨(continuous_rightAction a).measurable,hinv⟩,?_⟩
  have hrate : ell j-ell i = (d+1:ℝ) := by
    simp [ell,coordinateContractionWeights,hij]
  have he : Real.exp ((ell j-ell i)*t) = c := by
    rw [hrate]
    dsimp [t]
    rw [mul_comm,div_mul_cancel₀ _ (by positivity),Real.exp_log hc]
  have hs : rootTimeScaling ell i j t = Homeomorph.mulLeft₀ c hc.ne' := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,he]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell t μ hfree hinv
  simpa only [hs] using H



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory


namespace PrimeDegreePackets

lemma rootInformationMean_nat (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (m : ℕ) :
    rootInformationMean hij μ m = (m:ℝ≥0∞) * rootInformationMean hij μ 1 := by
  induction m with
  | zero => simpa using rootInformationMean_zero_time d hij μ hA
  | succ m ih =>
    rw [Nat.cast_add,Nat.cast_one,rootInformationMean_add d hij μ hA (by positivity) zero_le_one,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]

 

lemma ae_rootLeaf_ball_eq_one_of_mean_zero (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    {t : ℝ} (ht : 0 ≤ t) (hz : rootInformationMean hij μ t = 0) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t))) = 1 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have H := (lintegral_eq_zero_iff' (aemeasurable_rootInformation d hij μ hA t).ennreal_ofReal).mp hz
  filter_upwards [H,ae_rootInformation_nonneg d hij μ hA ht,
    ae_intrinsicRootLeaf_spec hij μ hfree,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hz hn hs hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  have he : rootInformation hij μ t x = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hn
  have hlog : Real.log (intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t)))).toReal = 0 := by
    exact neg_eq_zero.mp he
  exact (ENNReal.toReal_eq_one_iff _).mp
    (Real.eq_one_of_pos_of_log_eq_zero
      (ENNReal.toReal_pos (hp _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne) hlog)

 

theorem rootInformationMean_eq_zero_iff_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    rootInformationMean hij μ 1 = 0 ↔
      ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  constructor
  · intro hz
    have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
      (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
    have H : ∀ᵐ x ∂μ, ∀ m : ℕ,
        intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-(m:ℝ)))) = 1 := by
      apply ae_all_iff.mpr
      intro m
      apply ae_rootLeaf_ball_eq_one_of_mean_zero d hij μ hA (by positivity)
      rw [rootInformationMean_nat d hij μ hA,hz,mul_zero]
    filter_upwards [H,ae_intrinsicRootLeaf_spec hij μ hfree,
      ae_intrinsicRootLeaf_atom_dirac d hij μ hA] with x hx hs hd
    apply hd
    have hsmall (m : ℕ) : intrinsicRootLeaf hij μ x (Metric.ball 0 ((m+1:ℝ)⁻¹)) = 1 := by
      apply le_antisymm
      · rw [←hs.2]
        exact measure_mono (Metric.ball_subset_ball (inv_le_one₀ (by positivity) |>.mpr (by linarith only [Nat.cast_nonneg (α := ℝ) m])))
      · rw [←hx m]
        apply measure_mono (Metric.ball_subset_ball ?_)
        rw [Real.exp_neg]
        exact inv_anti₀ (by positivity) (Real.add_one_le_exp _)
    have hanti : Antitone (fun m : ℕ => Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) := by
      intro a b hab
      apply Metric.ball_subset_ball
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    have h0 : intrinsicRootLeaf hij μ x {0} = 1 := by
      rw [←real_iInter_ball_inv_nat,hanti.measure_iInter
        (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet)
        ⟨0,by rw [hsmall]; exact ENNReal.one_ne_top⟩]
      simp only [hsmall,iInf_const]
    rw [h0]
    exact one_ne_zero
  · intro hd
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hd] with x hx
    simp [rootInformation,hx,Measure.dirac_apply_of_mem (Metric.mem_ball_self (Real.exp_pos _))]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMaximal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HopfMeanBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean bounds from eventual orbit excursions

A conull union of positive finite excursions has nonnegative mean by the
finite Hopf inequality. This avoids assuming integrability of an unbounded
information function before truncating it.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

/-- Positive partial sums somewhere along almost every orbit force a
nonnegative integral. -/
theorem integral_nonneg_of_ae_positive_birkhoffSum
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {T : Y → Y} {f : Y → ℝ} (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (hfm : Measurable f)
    (hexc : ∀ᵐ x ∂μ, ∃ n : ℕ, 0 < birkhoffSum T f n x) :
    0 ≤ ∫ x, f x ∂μ := by
  let E : ℕ → Set Y := fun n => {x | 0 < positiveRunningSum T f n x}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt measurable_const (measurable_positiveRunningSum hT.measurable hfm n)
  have hmono : Monotone E := by
    intro a b hab x hx
    exact hx.trans_le (positiveRunningSum_mono T f x hab)
  have hconull : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hexc] with x hx
    obtain ⟨n, hn⟩ := hx
    exact mem_iUnion.mpr ⟨n, hn.trans_le (birkhoffSum_le_positiveRunningSum T f n x)⟩
  have hlim := tendsto_setIntegral_of_monotone hEm hmono hf.integrableOn
  have heq : (∫ x in ⋃ n, E n, f x ∂μ) = ∫ x, f x ∂μ := by
    rw [Measure.restrict_congr_set (show (⋃ n, E n) =ᵐ[μ] (univ : Set Y) from
      hconull.mono (fun x hx => by
        show (x ∈ ⋃ n, E n) = (x ∈ (univ : Set Y))
        simp [hx]))]
    simp
  rw [heq] at hlim
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n => finite_hopf_maximal hT hf hfm n

/-- A bounded observable whose orbit average is eventually below `c`
has mean at most `c`. -/
theorem integral_le_of_ae_birkhoffSum_lt
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {T : Y → Y} {g : Y → ℝ} (hT : MeasurePreserving T μ μ)
    (hg : Integrable g μ) (hgm : Measurable g) (c : ℝ)
    (hexc : ∀ᵐ x ∂μ, ∃ n : ℕ, birkhoffSum T g n x < c * n) :
    (∫ x, g x ∂μ) ≤ c := by
  have h := integral_nonneg_of_ae_positive_birkhoffSum hT
    ((integrable_const c).sub hg) (measurable_const.sub hgm) ?_
  · change 0 ≤ ∫ x, c - g x ∂μ at h
    rw [integral_sub (integrable_const c) hg] at h
    simpa using (sub_nonneg.mp h)
  · filter_upwards [hexc] with x hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    change 0 < ∑ k ∈ Finset.range n, (c - g (T^[k] x))
    rw [Finset.sum_sub_distrib]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm,
      birkhoffSum]
      using sub_pos.mpr hn

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RealLeafDensity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear lower bounds at typical centers of real leaf measures

Differentiation of Lebesgue measure relative to an arbitrary locally
finite real measure bounds their small-ball ratio at almost every center.
This supplies the dimension-one bound for actual root information.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

/-- A locally finite measure has at least linear mass in small balls
around almost every one of its own typical points. -/
theorem ae_real_ball_linear_lower_bound (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal r ≤ C * ν (ball x r) := by
  have hhalf : Tendsto (fun r : ℝ => r / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => r / 2) := continuous_id.div_const 2
      simpa only [zero_div] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r / 2
      exact div_pos (show 0 < r from hr) (by norm_num)
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (volume : Measure ℝ) ν,
    Measure.rnDeriv_lt_top (volume : Measure ℝ) ν] with x hx hfin
  let C := (volume : Measure ℝ).rnDeriv ν x + 1
  have hC : C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hfin.ne, ENNReal.one_ne_top⟩
  have hC0 : C ≠ 0 := by dsimp [C] <;> positivity
  have hless : (volume : Measure ℝ).rnDeriv ν x < C := ENNReal.lt_add_right hfin.ne one_ne_zero
  have hbound := (hx.comp hhalf).eventually (gt_mem_nhds hless)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, self_mem_nhdsWithin] with r hr hr0
  change 0 < r at hr0
  have h := (ENNReal.div_le_iff_le_mul (Or.inr hC) (Or.inr hC0)).mp hr.le
  have hs : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hvol : (volume : Measure ℝ) (closedBall x (r / 2)) = ENNReal.ofReal r := by
    rw [Real.volume_closedBall]
    congr 1
    ring
  rw [hvol] at h
  exact h.trans (by simpa only [mul_comm] using
    (mul_le_mul_left (measure_mono hs : ν (closedBall x (r / 2)) ≤ ν (ball x r)) C))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootLeafLowerBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Typical root leaves have a linear lower mass bound

The property is expressed at countably many exponential radii. This makes
it measurable and allows transfer through the actual root-box disintegration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma measurableSet_hasDiscreteLinearLowerBound :
    MeasurableSet {ν : Measure ℝ | HasDiscreteLinearLowerBound ν} := by
  simp only [HasDiscreteLinearLowerBound, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro C
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le measurable_const
    (measurable_const.mul (Measure.measurable_coe
      (isOpen_ball (x := (0 : ℝ)) (ε := Real.exp (-(n : ℝ)))).measurableSet))

lemma ae_basedRealMeasure_discrete_lower_bound (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] :
    ∀ᵐ x ∂ν, HasDiscreteLinearLowerBound (basedRealMeasure ν x) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop),
      Eventually.of_forall fun n => Real.exp_pos _⟩
  filter_upwards [ae_real_ball_linear_lower_bound ν, ν.support_mem_ae] with x hx hs
  obtain ⟨C, hC, hbound⟩ := hx
  have hm : 0 < ν (ball x 1) :=
    (ν.mem_support_iff_forall x).mp hs _ (ball_mem_nhds _ zero_lt_one)
  have hmT : ν (ball x 1) ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top hC hmT)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexp.eventually hbound)
  refine ⟨K, N, ?_⟩
  intro n hn
  have hmass : basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) =
      (ν (ball x 1))⁻¹ * ν (ball x (Real.exp (-(n : ℝ)))) := by
    change (centerRealMeasure ν x (ball 0 1))⁻¹ *
      centerRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) = _
    rw [centerRealMeasure_ball, centerRealMeasure_ball]
  have heq : (C * ν (ball x 1)) *
      basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) =
      C * ν (ball x (Real.exp (-(n : ℝ)))) := by
    rw [hmass, mul_assoc, ← mul_assoc (ν (ball x 1)),
      ENNReal.mul_inv_cancel hm.ne' hmT, one_mul]
  calc
    ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
        C * ν (ball x (Real.exp (-(n : ℝ)))) := hN n hn
    _ = (C * ν (ball x 1)) *
        basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) := heq.symm
    _ ≤ (K : ℝ≥0∞) * basedRealMeasure ν x (ball 0 (Real.exp (-(n : ℝ)))) :=
      mul_le_mul_left hK.le _

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma ae_basedLeaf_discrete_lower_bound (A : PrimeDegreePackets.RootBox hij k)
    (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, HasDiscreteLinearLowerBound (A.basedLeaf R μ z) := by
  let κ := A.regularLeafKernel R hAR μ hfree
  have hmeas : MeasurableSet {z : RootSlice i j k × ℝ |
      HasDiscreteLinearLowerBound (basedRealMeasure (κ z.1) z.2)} :=
    measurableSet_hasDiscreteLinearLowerBound.preimage (basedRealKernel κ).measurable
  have hbase : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
      HasDiscreteLinearLowerBound (basedRealMeasure (κ s) t) := by
    filter_upwards [A.ae_regularLeafKernel_eq R hAR μ hfree,
      A.ae_leafMeasure_spec R hAR μ hfree] with s hs hspec
    have hle : A.conditionalKernel μ s ≤ κ s := by
      rw [hs, ← hspec.2.2.1]
      exact Measure.restrict_le_self
    exact (ae_basedRealMeasure_discrete_lower_bound (κ s)).filter_mono
      (ae_mono hle)
  have H := Measure.ae_compProd_of_ae_ae hmeas hbase
  have H' : ∀ᵐ z ∂A.coordinateMeasure μ,
      HasDiscreteLinearLowerBound (basedRealMeasure (κ z.1) z.2) := by
    simpa only [PrimeDegreePackets.RootBox.conditionalKernel, Measure.disintegrate] using H
  have he : ∀ᵐ z ∂A.coordinateMeasure μ, κ z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  filter_upwards [H', he] with z hz hez
  simpa only [PrimeDegreePackets.RootBox.basedLeaf, ← hez] using hz

lemma ae_intrinsicRootLeaf_discrete_lower_bound_restrict
    (A : PrimeDegreePackets.RootBox hij k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ.restrict A.range, HasDiscreteLinearLowerBound (intrinsicRootLeaf hij μ x) := by
  apply A.ae_of_coordinate μ
  filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    ae_basedLeaf_discrete_lower_bound A R hAR μ hfree] with z he hz
  rwa [he]

end RootBox

/-- The actual intrinsic root leaf has a linear lower mass bound at almost
all base points. No entropy input is assumed. -/
theorem ae_intrinsicRootLeaf_discrete_lower_bound {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, HasDiscreteLinearLowerBound (intrinsicRootLeaf hij μ x) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ)
    (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => RootBox.ae_intrinsicRootLeaf_discrete_lower_bound_restrict
      B.val.box B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion, Measure.restrict_univ] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationGrowth
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear growth of actual root information

Small-ball differentiation bounds the information along integer scales.
The actual scaling cocycle identifies these scales with Birkhoff sums.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The information at integer time is the corresponding finite orbit sum. -/
lemma ae_rootInformation_nat_sum (n : ℕ) :
    ∀ᵐ x ∂μ, rootInformation hij μ n x =
      birkhoffSum (fun y => rightAction y (rootCanonicalFlow d j 1))
        (rootInformation hij μ 1) n x := by
  induction n with
  | zero =>
    have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
      (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
    filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
    simp [rootInformation, hx.2]
  | succ n ih =>
    have hT := rootCanonicalFlow_preserving d j 1 μ hA
    have him : ∀ᵐ y ∂μ.map (fun y => rightAction y (rootCanonicalFlow d j 1)),
        rootInformation hij μ n y =
          birkhoffSum (fun y => rightAction y (rootCanonicalFlow d j 1))
            (rootInformation hij μ 1) n y := by
      rw [hT.map_eq]
      exact ih
    have hip := ae_of_ae_map hT.measurable.aemeasurable him
    filter_upwards [hip, ae_rootInformation_cocycle d hij μ hA n 1] with x hi hc
    simpa only [Nat.cast_succ, hi, birkhoffSum_succ'] using hc

/-- Root information grows at most linearly, with slope one and a
point-dependent additive constant. -/
lemma ae_rootInformation_linear_bound :
    ∀ᵐ x ∂μ, ∃ B : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      rootInformation hij μ n x ≤ n + B := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_discrete_lower_bound hij μ hfree,
    ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x hx hs hp
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  obtain ⟨C, N, hCN⟩ := hx
  refine ⟨Real.log (C + 1 : ℝ), N, ?_⟩
  intro n hn
  have hr := Real.exp_pos (-(n : ℝ))
  have hm : 0 < ν (ball 0 (Real.exp (-(n : ℝ)))) := hp _ hr
  have hfin : ν (ball 0 (Real.exp (-(n : ℝ)))) ≠ ∞ := measure_ball_lt_top.ne
  have hbig : ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
      ((C + 1 : ℕ) : ℝ≥0∞) * ν (ball 0 (Real.exp (-(n : ℝ)))) :=
    (hCN n hn).trans (mul_le_mul_left (by exact_mod_cast Nat.le_succ C) _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) hfin) hbig
  rw [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  simp only [Nat.cast_add, Nat.cast_one] at hreal
  have hmreal : 0 < (ν (ball 0 (Real.exp (-(n : ℝ))))).toReal :=
    ENNReal.toReal_pos hm.ne' hfin
  have hlog := Real.log_le_log hr hreal
  rw [Real.log_exp, Real.log_mul (by positivity) hmreal.ne'] at hlog
  change -Real.log (ν (ball 0 (Real.exp (-(n : ℝ))))).toReal ≤ _
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationBound
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual root information coefficient lies in the unit interval

Truncation, finite Hopf bounds and monotone convergence turn the almost
sure linear small-ball bound into a finite mean bound. No entropy formula
or ergodic theorem is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

/-- The coefficient defined by the actual root leaf information is finite
and at most one. -/
theorem rootInformationMean_le_one : rootInformationMean hij μ 1 ≤ 1 := by
  let T : X (d + 1) → X (d + 1) := fun x => rightAction x (rootCanonicalFlow d j 1)
  have hT : MeasurePreserving T μ μ := rootCanonicalFlow_preserving d j 1 μ hA
  have hmeas := aemeasurable_rootInformation d hij μ hA 1
  let f : X (d + 1) → ℝ := fun x => max (hmeas.mk (rootInformation hij μ 1) x) 0
  have hfm : Measurable f := hmeas.measurable_mk.max measurable_const
  have hfnonneg (x) : 0 ≤ f x := le_max_right _ _
  have hfeq : f =ᵐ[μ] rootInformation hij μ 1 := by
    filter_upwards [hmeas.ae_eq_mk, ae_rootInformation_nonneg d hij μ hA zero_le_one] with x hx hn
    exact (congrArg (max · 0) hx).symm.trans (max_eq_left hn)
  let g (M : ℕ) (x : X (d + 1)) : ℝ := min (f x) M
  have hgm (M : ℕ) : Measurable (g M) := hfm.min measurable_const
  have hg0 (M : ℕ) (x) : 0 ≤ g M x := le_min (hfnonneg x) (Nat.cast_nonneg M)
  have hgint (M : ℕ) : Integrable (g M) μ :=
    integrable_of_le_of_le (hgm M).aestronglyMeasurable
      (Eventually.of_forall (hg0 M)) (Eventually.of_forall fun x => min_le_right (f x) (M : ℝ))
      (integrable_const 0) (integrable_const (M : ℝ))
  have hsum : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T f n x = rootInformation hij μ n x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq hfeq n,
      ae_rootInformation_nat_sum d hij μ hA n] with x he hs
    exact he.trans hs.symm
  have hgmean (M : ℕ) : (∫ x, g M x ∂μ) ≤ 1 := by
    have hbound (c : ℝ) (hc : 1 < c) : (∫ x, g M x ∂μ) ≤ c := by
      apply integral_le_of_ae_birkhoffSum_lt hT (hgint M) (hgm M) c
      filter_upwards [hsum, ae_rootInformation_linear_bound d hij μ hA] with x hx hb
      obtain ⟨B, N, hN⟩ := hb
      obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (B / (c - 1)))
      have hnN : N ≤ n := by exact_mod_cast (le_max_left (N : ℝ) _).trans hn.le
      have hBn : B < (n : ℝ) * (c - 1) :=
        (div_lt_iff₀ (by linarith : 0 < c - 1)).mp ((le_max_right _ _).trans_lt hn)
      refine ⟨n, ?_⟩
      have hle : birkhoffSum T (g M) n x ≤ birkhoffSum T f n x := by
        apply Finset.sum_le_sum
        intro k _
        exact min_le_left _ _
      rw [hx n] at hle
      have hfin := (hle.trans (hN n hnN))
      nlinarith
    by_contra! h
    have hh := hbound (((∫ x, g M x ∂μ) + 1) / 2) (by linarith)
    linarith
  have hlin (M : ℕ) : (∫⁻ x, ENNReal.ofReal (g M x) ∂μ) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hgint M) (Eventually.of_forall (hg0 M))]
    exact ENNReal.ofReal_le_one.mpr (hgmean M)
  have hlim : Tendsto (fun M : ℕ => ∫⁻ x, ENNReal.ofReal (g M x) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun M => (hgm M).ennreal_ofReal.aemeasurable)
    · exact Eventually.of_forall fun x a b hab => ENNReal.ofReal_le_ofReal
        (min_le_min_left (f x) (Nat.cast_le.mpr hab))
    · apply Eventually.of_forall
      intro x
      have heq : ∀ᶠ M : ℕ in atTop, g M x = f x := by
        obtain ⟨N, hN⟩ := exists_nat_gt (f x)
        filter_upwards [eventually_ge_atTop N] with M hM
        exact min_eq_left (hN.le.trans (Nat.cast_le.mpr hM))
      exact tendsto_const_nhds.congr' (heq.mono fun M hM => congrArg ENNReal.ofReal hM.symm)
  have hbound := le_of_tendsto hlim (Eventually.of_forall hlin)
  have he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = rootInformationMean hij μ 1 :=
    lintegral_congr_ae (hfeq.mono fun x hx => congrArg ENNReal.ofReal hx)
  rwa [he] at hbound

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CanonicalRootBasic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean root coefficients and their elementary properties

The coefficient is the mean leaf information at unit scale. Diagonal
covariance makes real-time mean information linear in time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

lemma canonicalRootCoefficient_zero_iff_oai (i j : Fin (d + 1)) (hij : i ≠ j) :
    canonicalRootCoefficient d μ i j = 0 ↔
      ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  rw [canonicalRootCoefficient, dite_eq_right hij, ENNReal.toReal_eq_zero_iff]
  have hfin : rootInformationMean hij μ 1 ≠ ∞ :=
    ne_of_lt ((rootInformationMean_le_one d hij μ hA).trans_lt ENNReal.one_lt_top)
  simp only [hfin, or_false]
  exact rootInformationMean_eq_zero_iff_dirac d hij μ hA

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff_oai := @OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff_oai
