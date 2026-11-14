-- Prove2me | solution 1 for OAI.DukePrimeDegree.RootPrefixBox.selfConstant_image_massContained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:48:04.837296+00:00
-- url     : https://prove2.me/submissions/b0ca69c1-5652-4f0d-9cc2-565c230384bc

import Mathlib
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Pairing
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
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
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
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
import Definitions.Def_OAIQ244Duke024
import Definitions.Def_OAIQ244Duke035
import Theorems.Thm_OAI_DukePrimeDegree_RootPrefixBox_ae_normalized_uncentered_eq_regularLeaf

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_KernelStabilizerMeasurable
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditioningFiniteLabels
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma countableFutureFiber_eq_of_mem {S V Y : Type*}
    (T : Y → Y) (Q : Y → ℕ) (F : S × V → Y)
    (z : S × V) {u : V} (hu : u ∈ countableFutureFiber T Q F z) :
    countableFutureFiber T Q F (z.1,u) = countableFutureFiber T Q F z := by
  ext v
  constructor
  · intro hv k
    exact (hv k).trans (hu k)
  · intro hv k
    exact (hv k).trans (hu k).symm

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_InfiniteLabelProbability
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
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
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_StationaryRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureFiberKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local future conditional as a self-consistent Markov kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V] [MeasurableSpace Y]

lemma futureFiberTimeKernel_apply_good (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V)
    (hz : κ z.1 (countableFutureFiber T Q F z) ≠ 0) :
    futureFiberTimeKernel κ hT hQ hF z =
      (anchorNormalize (κ z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z) := by
  change (if (futureSliceKernel κ hT hQ hF z) univ ≠ 0 then
    normalizedFutureSliceKernel κ hT hQ hF z else Measure.dirac z.2) = _
  have hm : (futureSliceKernel κ hT hQ hF z) univ =
      κ z.1 (countableFutureFiber T Q F z) := Measure.restrict_apply_univ _
  rw [hm,ite_eq_left hz]
  change ((futureSliceKernel κ hT hQ hF z) univ)⁻¹ •
    (κ z.1).restrict (countableFutureFiber T Q F z) = _
  rw [hm,anchorNormalize,Measure.restrict_smul]

lemma futureFiberTimeKernel_apply_zero (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V)
    (hz : κ z.1 (countableFutureFiber T Q F z) = 0) :
    futureFiberTimeKernel κ hT hQ hF z = Measure.dirac z.2 := by
  change (if (futureSliceKernel κ hT hQ hF z) univ ≠ 0 then
    normalizedFutureSliceKernel κ hT hQ hF z else Measure.dirac z.2) = _
  have hm : (futureSliceKernel κ hT hQ hF z) univ =
      κ z.1 (countableFutureFiber T Q F z) := Measure.restrict_apply_univ _
  rw [hm,hz,ite_eq_right (not_ne_iff.mpr rfl)]

instance futureFiberTimeKernel_markov (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) :
    IsMarkovKernel (futureFiberTimeKernel κ hT hQ hF) := by
  refine ⟨fun z => ⟨?_⟩⟩
  by_cases hz : κ z.1 (countableFutureFiber T Q F z)=0
  · rw [futureFiberTimeKernel_apply_zero κ hT hQ hF z hz]
    simp
  · rw [futureFiberTimeKernel_apply_good κ hT hQ hF z hz]
    simp only [anchorNormalize,Measure.restrict_smul,Measure.smul_apply,
      Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hz (measure_ne_top _ _)

instance futureFiberCoordinateKernel_markov (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) :
    IsMarkovKernel (futureFiberCoordinateKernel κ hT hQ hF) := by
  unfold futureFiberCoordinateKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma futureFiberCoordinateKernel_apply (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V) :
    futureFiberCoordinateKernel κ hT hQ hF z =
      (futureFiberTimeKernel κ hT hQ hF z).map (Prod.mk z.1) := by
  rw [futureFiberCoordinateKernel,Kernel.prod_apply,Kernel.deterministic_apply,
    Measure.dirac_prod]

theorem futureFiberCoordinateKernel_self_constant [MeasurableSingletonClass S]
    [MeasurableSingletonClass V] (κ : Kernel S V) [IsMarkovKernel κ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F) (z : S × V) :
    ∀ᵐ w ∂futureFiberCoordinateKernel κ hT hQ hF z,
      futureFiberCoordinateKernel κ hT hQ hF w =
        futureFiberCoordinateKernel κ hT hQ hF z := by
  rw [futureFiberCoordinateKernel_apply]
  by_cases hz : κ z.1 (countableFutureFiber T Q F z)=0
  · rw [futureFiberTimeKernel_apply_zero κ hT hQ hF z hz,
      Measure.map_dirac]
    rw [ae_dirac_eq]
    change futureFiberCoordinateKernel κ hT hQ hF (z.1,z.2)=Measure.dirac (z.1,z.2)
    exact futureFiberCoordinateKernel_apply κ hT hQ hF z |>.trans (by
      rw [futureFiberTimeKernel_apply_zero κ hT hQ hF z hz,Measure.map_dirac])
  · have hfiber : MeasurableSet (countableFutureFiber T Q F z) := by
      simp only [countableFutureFiber,Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_eq_fun
        (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
    have hmem : ∀ᵐ w ∂(futureFiberTimeKernel κ hT hQ hF z).map (Prod.mk z.1),
        w.1=z.1 ∧ w.2 ∈ countableFutureFiber T Q F z := by
      apply (ae_map_iff measurable_prodMk_left.aemeasurable
        (((measurableSet_singleton z.1).preimage measurable_fst).inter
          (hfiber.preimage measurable_snd))).mpr
      rw [futureFiberTimeKernel_apply_good κ hT hQ hF z hz]
      filter_upwards [ae_restrict_mem hfiber] with v hv
      exact ⟨rfl,hv⟩
    filter_upwards [hmem] with w hw
    obtain ⟨s,v⟩ := w
    dsimp only at hw
    rcases hw with ⟨hs,hv⟩
    subst s
    have he := countableFutureFiber_eq_of_mem T Q F z hv
    have hm : κ z.1 (countableFutureFiber T Q F (z.1,v)) ≠ 0 := by rwa [he]
    rw [futureFiberCoordinateKernel_apply,
      futureFiberTimeKernel_apply_good κ hT hQ hF _ hm,
      futureFiberTimeKernel_apply_good κ hT hQ hF _ hz,he]

theorem futureFiberCoordinateKernel_stationary_restrict
    [StandardBorelSpace V] [Nonempty V]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0)
    (E : Set (S × V)) (hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E) :
    (ρ.restrict E).bind (futureFiberCoordinateKernel ρ.condKernel hT hQ hF) =
      ρ.restrict E := by
  apply bind_eq_of_real_integrals
  intro A hA
  have H := setIntegral_countableFuture_conditional_probability ρ hQ hT hF hpos A hA E hE
  have he : (∫ z in E, (futureFiberCoordinateKernel ρ.condKernel hT hQ hF z).real A ∂ρ) =
      ∫ z in E,
        ((anchorNormalize (ρ.condKernel z.1) (countableFutureFiber T Q F z)).restrict
          (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A} ∂ρ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hpos] with z hz
    rw [futureFiberCoordinateKernel_apply,
      futureFiberTimeKernel_apply_good ρ.condKernel hT hQ hF z hz]
    exact congrArg ENNReal.toReal (Measure.map_apply measurable_prodMk_left hA)
  rw [he,H]
  simp only [Measure.real,Measure.restrict_apply hA]

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixFutureMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SelfConditionalKernelMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting self-consistency through measurable coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace DukePrimeDegree

theorem measurableSet_kernel_selfConstant {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] (κ : Kernel Y Y) [IsMarkovKernel κ] :
    MeasurableSet {x | ∀ᵐ y ∂κ x, κ y=κ x} := by
  have hrel : MeasurableSet {z : Y × Y | κ z.2=κ z.1} :=
    measurableSet_finite_kernel_eq (κ.comap Prod.snd measurable_snd)
      (κ.comap Prod.fst measurable_fst)
  have hm : Measurable (fun x => κ x {y | κ y≠κ x}) :=
    Kernel.measurable_kernel_prodMk_left hrel.compl
  have he : {x | ∀ᵐ y ∂κ x, κ y=κ x} = {x | κ x {y | κ y≠κ x}=0} := by
    ext x
    exact ae_iff
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

/-- No global injectivity of the coordinate map is required. The actual
ambient kernel must agree almost everywhere with the pushed local kernel. -/
theorem selfConstant_kernel_map
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] [StandardBorelSpace Y]
    (ρ : Measure Z) (η : Kernel Z Z) [IsMarkovKernel η]
    (hstat : ρ.bind η=ρ)
    (hself : ∀ᵐ z ∂ρ, ∀ᵐ w ∂η z, η w=η z)
    (F : Z → Y) (hF : Measurable F)
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hversion : ∀ᵐ z ∂ρ, κ (F z)=(η z).map F) :
    ∀ᵐ x ∂ρ.map F, ∀ᵐ y ∂κ x, κ y=κ x := by
  have hv : ∀ᵐ z ∂ρ, ∀ᵐ w ∂η z, κ (F w)=(η w).map F := by
    apply Measure.ae_ae_of_ae_bind η.measurable.aemeasurable
    rwa [hstat]
  apply (ae_map_iff hF.aemeasurable (measurableSet_kernel_selfConstant κ)).mpr
  filter_upwards [hversion,hself,hv] with z hz hs hvz
  rw [hz]
  have hset : MeasurableSet {y | κ y=(η z).map F} :=
    measurableSet_finite_kernel_eq κ (Kernel.const Y ((η z).map F))
  apply (ae_map_iff hF.aemeasurable hset).mpr
  filter_upwards [hs,hvz] with w hw hvw
  rw [hvw,hw]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixSelfConditional
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Self-consistency of the ambient future kernel on quotient boxes -/

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
    [MeasurableSpace V] [BorelSpace V] [MeasurableSingletonClass V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

theorem selfConstant_image_massContained_oai
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
    ∀ᵐ x ∂μ.restrict (F '' (E ∩ B.domain)), ∀ᵐ y ∂κ x, κ y=κ x := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP hf g
  let ρ := B.coordinateMeasure μ
  let K := B.regularLeafKernel R hBR μ hfree
  let E := {z | K z.1 (countableFutureFiber T Q F z \ B.time) = 0}
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  let η := futureFiberCoordinateKernel ρ.condKernel hT hQ hF
  have hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E :=
    measurableSet_future_mass_contained K hT hQ hF B.time B.time_open.measurableSet
  have hEle : (⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))) ≤
      (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
    apply iSup_le
    intro m
    exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
  have hEm : MeasurableSet E := hEle E hE
  have hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    exact ne_of_gt (hz.trans_le (measure_mono (fun t ht k => ht (k+1))))
  have hstat : (ρ.restrict E).bind η=ρ.restrict E :=
    futureFiberCoordinateKernel_stationary_restrict ρ hT hQ hF hpos E hE
  have hself : ∀ᵐ z ∂ρ.restrict E, ∀ᵐ w ∂η z, η w=η z :=
    Filter.Eventually.of_forall (futureFiberCoordinateKernel_self_constant ρ.condKernel hT hQ hF)
  have hversion : ∀ᵐ z ∂ρ.restrict E, κ (F z)=(η z).map F := by
    have hka := B.ae_coordinate_of_ambient μ hκ
    have hn := B.ae_normalized_uncentered_eq_regularLeaf R hBR μ hfree
    have hs := ae_of_ae_map measurable_fst.aemeasurable (B.ae_leafMeasure_spec R hBR μ hfree)
    have hk := ae_of_ae_map measurable_fst.aemeasurable (B.ae_regularLeafKernel_eq R hBR μ hfree)
    filter_upwards [ae_restrict_of_ae hka,ae_restrict_of_ae hn,
      ae_restrict_of_ae hs,ae_restrict_of_ae hk,ae_restrict_of_ae hpos,
      ae_restrict_mem hEm] with z hka hn hs hk hz hnull
    have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
      simp only [countableFutureFiber,Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => measurableSet_eq_fun
        (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
    have hmass : K z.1 B.time=1 := by
      change B.regularLeafKernel R hBR μ hfree z.1 B.time=1
      rw [hk]
      exact hs.2.1
    have hc : ρ.condKernel z.1=(anchorNormalize (K z.1) B.time).restrict B.time := by
      change B.conditionalKernel μ z.1=_
      rw [hk]
      simpa only [anchorNormalize,hs.2.1,inv_one,one_smul] using hs.2.2.1.symm
    have hnorm := normalized_restriction_of_null_diff (K z.1)
      (countableFutureFiber T Q F z) B.time hfuture B.time_open.measurableSet
      (by rw [hmass]; exact one_ne_zero) (by rw [hmass]; exact ENNReal.one_ne_top) hnull
    rw [hka,←B.map_uncentered_future_eq_ambient μ ell hell Q 1 z]
    change (((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
      (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).map
      (fun t => F (z.1,t)))=(η z).map F
    rw [hn]
    dsimp only [η]
    rw [futureFiberCoordinateKernel_apply,
      futureFiberTimeKernel_apply_good ρ.condKernel hT hQ hF z hz,
      Measure.map_map hF measurable_prodMk_left,hc,hnorm]
    rfl
  have H := selfConstant_kernel_map (ρ.restrict E) η hstat hself F hF κ hversion
  have hdom := B.coordinateMeasure_ae_domain μ
  have heq : ρ.restrict (E ∩ B.domain)=ρ.restrict E := by
    apply Measure.restrict_congr_set
    filter_upwards [hdom] with z hz
    exact propext ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩
  have hm := B.map_restricted_coordinates μ (E ∩ B.domain)
    (hEm.inter (B.transverse_open.prod B.time_open).measurableSet) inter_subset_right
  rw [heq] at hm
  rwa [hm] at H

end RootPrefixBox
end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.RootPrefixBox.selfConstant_image_massContained_oai.{u_1} := @OAI.DukePrimeDegree.RootPrefixBox.selfConstant_image_massContained_oai.{u_1}
