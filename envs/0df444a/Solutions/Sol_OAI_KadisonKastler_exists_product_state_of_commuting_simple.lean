-- Prove2me | solution 1 for OAI.KadisonKastler.exists_product_state_of_commuting_simple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:14.624212+00:00
-- url     : https://prove2.me/submissions/a97a9927-7ac9-4cca-a7c8-a2cbeed842c1

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_Q260K015
import Theorems.Thm_OAI_KadisonKastler_pure_restriction_commuting_factorization

section
-- module Solutions.OAIQ075_KS.TracialSplitting_FullProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD

open Filter Topology

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section SmallFullSupport

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma simple_starAlgHom_injective [Nontrivial D] (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) : Function.Injective ι := by
  have hι : Continuous ι := (ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))).continuous
  have hc : IsClosed (TwoSidedIdeal.ker ι : Set A) := by
    have he : (TwoSidedIdeal.ker ι : Set A) = {a : A | ι a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker ι
    rw [he]
    exact isClosed_eq hι continuous_const
  rcases hsimple (TwoSidedIdeal.ker ι) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot ι).mp hb
  · have : (1 : A) ∈ TwoSidedIdeal.ker ι := by rw [ht]; exact Set.mem_univ _
    have hz := (TwoSidedIdeal.mem_ker ι).mp this
    simp at hz

end SmallFullSupport

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f)) := by
  simp only [gns_apply_vector]
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

theorem gnsVector_norm_eq_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : ‖gnsVector f‖ = 1 := by
  have hs := gnsVector_norm_sq f
  rw [hf, Complex.one_re] at hs
  nlinarith [norm_nonneg (gnsVector f)]

theorem state_map_star (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) :
    f (star a) = star (f a) := map_star (positiveOfSquares f hf.2) a

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem isState_restrict (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) (hf : IsState f) :
    IsState (restrictState φ f) := by
  apply (isState_iff _).mpr
  refine ⟨?_, ?_⟩
  · simp only [restrictState_apply, map_one, ((isState_iff f).mp hf).1]
  · intro a
    simpa only [restrictState_apply, map_mul, map_star] using hf.2 (φ a)

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cyclicGNSMap_norm (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) (x : f.GNS) :
    ‖cyclicGNSMap f π ξ hcoeff x‖ = ‖x‖ := by
  have heq : (fun y : f.GNS => ‖cyclicGNSMap f π ξ hcoeff y‖) = fun y => ‖y‖ := by
    apply Completion.denseRange_coe.equalizer (by fun_prop) (by fun_prop)
    funext y
    change ‖(cyclicPreGNS f π ξ hcoeff).toContinuousLinearMap.fromCompletion (y : f.GNS)‖ = ‖(y : f.GNS)‖
    rw [ContinuousLinearMap.fromCompletion_apply_coe, Completion.norm_coe]
    exact (cyclicPreGNS f π ξ hcoeff).norm_map y
  exact congrFun heq x

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_States
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_state_extension_subalgebra
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (f : S →L[ℂ] ℂ) (hf : IsState f) :
    ∃ F : A →L[ℂ] ℂ, IsState F ∧ ∀ a : S, F (a : A) = f a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let g : selfAdjointSubspace S →L[ℝ] ℝ :=
    Complex.reCLM.comp ((f.restrictScalars ℝ).comp (selfAdjointSubspaceInclusion S))
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (selfAdjointSubspaceInclusion S a)).re‖ ≤ 1 * ‖a‖
    calc
      _ ≤ ‖f (selfAdjointSubspaceInclusion S a)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
      _ ≤ ‖selfAdjointSubspaceInclusion S a‖ := state_norm_apply_le f hf _
      _ = 1 * ‖a‖ := by simp [selfAdjointSubspaceInclusion]; rfl
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (selfAdjointSubspace S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖G₀‖ * ‖sa a‖ := G₀.le_opNorm _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg _)
  have hG1 : G 1 = 1 := by
    let e : selfAdjointSubspace S := ⟨1, S.one_mem, IsSelfAdjoint.one A⟩
    have he := hG₀ e
    change G 1 = (f 1).re at he
    simpa only [(isState_iff f).mp hf |>.1, Complex.one_re] using he
  let F := positiveCLM (selfAdjointPositive G hGn hG1)
  have hF : IsState F := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1, fun a => ?_⟩
    exact ⟨((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).2.symm,
      ((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).1⟩
  refine ⟨F, hF, ?_⟩
  have hs (a : S) (ha : IsSelfAdjoint a) : F (a : A) = f a := by
    let b : selfAdjointSubspace S := ⟨(a : A), a.property, by
      change star (a : A) = (a : A)
      exact congrArg Subtype.val ha.star_eq⟩
    let bsa : selfAdjoint A := ⟨(a : A), b.property.2⟩
    have hfb : (f a).im = 0 := by
      have hh := state_map_star f hf a
      rw [ha.star_eq] at hh
      exact Complex.conj_eq_iff_im.mp hh.symm
    change selfAdjointPositive G hGn hG1 (bsa : A) = f a
    rw [selfAdjointPositive_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    exact Complex.ext (by simp) (by simpa using hfb.symm)
  intro a
  have hdecomp := realPart_add_I_smul_imaginaryPart a
  rw [← hdecomp]
  change F (((realPart a : S) : A) + Complex.I • ((imaginaryPart a : S) : A)) = _
  simp only [map_add, map_smul]
  rw [hs _ (realPart a).property, hs _ (imaginaryPart a).property]

omit [PartialOrder A] [StarOrderedRing A] in

theorem character_isState (φ : WeakDual.characterSpace ℂ A) :
    IsState (WeakDual.toStrongDual (φ : WeakDual ℂ A)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  apply (isState_iff _).mpr
  refine ⟨map_one φ, fun a => ?_⟩
  change (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re
  rw [map_mul, map_star]
  have h := star_mul_self_nonneg (φ a)
  exact ⟨h.2.symm, h.1⟩

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_norming_state [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ‖f a‖ = ‖a‖ := by
  let S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ a
  let b : S := ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  obtain ⟨z, hz, hnz⟩ :=
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℂ) b).1
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  obtain ⟨f, hf, hrest⟩ := exists_state_extension_subalgebra S
    (WeakDual.toStrongDual (φ : WeakDual ℂ S)) (character_isState φ)
  refine ⟨f, hf, ?_⟩
  change ‖f (b : A)‖ = ‖b‖
  rw [hrest b]
  change ‖φ b‖ = ‖b‖
  rw [hφ]
  exact hnz

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

open scoped CStarAlgebra

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimpleIrreducibleRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful irreducible representation for Sakai's construction

Compactness of the state space gives a pure state. Its GNS representation
is irreducible, and simplicity makes the representation faithful. These
steps use the existing state-space and GNS proofs, with no representation
existence hypothesis.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_pure_state :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ IsPureState f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (A →L[ℂ] ℂ))
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    (WeakDual.withSeminorms ℂ A).toLocallyConvexSpace
  obtain ⟨f, hf, _⟩ := exists_norming_state (1 : A)
  have hne : (weakStates A).Nonempty := ⟨StrongDual.toWeakDual f, hf⟩
  obtain ⟨g, hg⟩ := isCompact_weakStates.extremePoints_nonempty hne
  exact ⟨g.toStrongDual, hg.1, hg⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_StateExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB uE

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace CurrentMain

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointFunctionalComplex_apply (f : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointFunctionalComplex f a = (f a : ℂ) := by
  have hr : ℜ (a : A) = a := Subtype.ext a.property.coe_realPart
  simp [selfAdjointFunctionalComplex, hr, a.property.imaginaryPart]

lemma selfAdjointFunctional_nonneg (f : selfAdjoint A →L[ℝ] ℝ)
    (hn : ‖f‖ ≤ 1) (h1 : f 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ f a := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 0 < ‖(a : A)‖ := norm_pos_iff.mpr (fun h => hz (Subtype.ext h))
  let b : selfAdjoint A := ‖(a : A)‖⁻¹ • a
  have hb0 : 0 ≤ (b : A) := smul_nonneg (by positivity) ha
  have hbn : ‖(b : A)‖ ≤ 1 := by
    change ‖‖(a : A)‖⁻¹ • (a : A)‖ ≤ 1
    simp [norm_smul, inv_mul_cancel₀ hp.ne']
  have hb1 : (b : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn
  have hsub : ‖(1 : selfAdjoint A) - b‖ ≤ 1 := by
    change ‖(1 : A) - (b : A)‖ ≤ 1
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hb1)).mpr
      (sub_le_self _ hb0)
  have hf : ‖f (1 - b)‖ ≤ 1 :=
    (f.le_opNorm _).trans ((mul_le_mul hn hsub (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hfb : 0 ≤ f b := by
    have := le_abs_self (f (1 - b))
    rw [map_sub, h1] at hf this
    change |1 - f b| ≤ 1 at hf
    linarith
  change 0 ≤ f (‖(a : A)‖⁻¹ • a) at hfb
  rw [map_smul, smul_eq_mul] at hfb
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hp)).mp hfb

theorem state_extension (ι : A →⋆ₐ[ℂ] B) (hi : Function.Injective ι)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ∃ g : B →ₚ[ℂ] ℂ, g 1 = 1 ∧ ∀ a, g (ι a) = f a := by
  let L := selfAdjointEmbedding ι hi
  let F := stateRealContinuous f hf
  let E := L.equivRange
  let S : Submodule ℝ (selfAdjoint B) := L.range
  let _ : NormedAddCommGroup S := inferInstance
  let _ : NormedSpace ℝ S :=
    { norm_smul_le := fun r a => norm_smul_le r ((a : selfAdjoint B) : B) }
  let Fr : S →L[ℝ] ℝ := F.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hFr : ‖Fr‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro a
    change |(f (E.symm a)).re| ≤ 1 * ‖a‖
    simpa only [one_mul,E.symm.norm_map] using state_realPart_bound f hf (E.symm a)
  obtain ⟨G,hG,hGn⟩ := exists_extension_norm_eq S Fr
  have hGa (a : selfAdjoint A) : G (L a) = (f a).re := by
    have h := hG (E a)
    change G (L a) = F (E.symm (E a)) at h
    rw [E.symm_apply_apply] at h
    exact h
  have hG1 : G 1 = 1 := by
    have h := hGa 1
    have he : L 1 = 1 := Subtype.ext (map_one ι)
    rw [he] at h
    simpa [hf] using h
  let gL := selfAdjointFunctionalComplex G.toLinearMap
  have hgpos (b : B) (hb : 0 ≤ b) : 0 ≤ gL b := by
    have h := selfAdjointFunctional_nonneg G (hGn.le.trans hFr) hG1
      ⟨b,.of_nonneg hb⟩ hb
    change 0 ≤ selfAdjointFunctionalComplex G.toLinearMap
      ((⟨b,.of_nonneg hb⟩ : selfAdjoint B) : B)
    rw [selfAdjointFunctionalComplex_apply]
    exact_mod_cast h
  let g : B →ₚ[ℂ] ℂ :=
    { toLinearMap := gL
      monotone' := by
        intro a b hab
        have h := hgpos (b-a) (sub_nonneg.mpr hab)
        rw [map_sub] at h
        exact sub_nonneg.mp h }
  have hga (a : selfAdjoint A) : g (ι a) = f a := by
    change selfAdjointFunctionalComplex G.toLinearMap ((L a : selfAdjoint B) : B) = f a
    rw [selfAdjointFunctionalComplex_apply]
    change (G (L a) : ℂ) = f a
    rw [hGa]
    exact (Complex.ext rfl (by
      have hsa : IsSelfAdjoint (f a) := a.property.map f
      have he := congrArg Complex.im hsa
      simp only [Complex.star_def,Complex.conj_im] at he
      change 0 = (f a).im
      linarith))
  refine ⟨g, ?_, ?_⟩
  · have h := hga 1
    change g (ι 1) = f 1 at h
    simpa only [map_one,hf] using h
  · intro a
    have ha : a = (ℜ a : A) + Complex.I • (ℑ a : A) := by
      exact (realPart_add_I_smul_imaginaryPart a).symm
    conv_lhs => rw [ha]
    rw [map_add,map_smul,map_add,map_smul,hga,hga]
    rw [← map_smul,← map_add,← ha]

end CurrentMain

open scoped ComplexOrder InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PureStateExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pure-state extensions along unital star embeddings

The set of state extensions is weak-star compact. If the original state
is pure, an extreme point of this set is pure on the larger algebra.
This supplies state extensions used in the derivation construction.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem exists_state_extension_of_embedding (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (f : A →L[ℂ] ℂ) (hf : IsState f) :
    ∃ g : B →L[ℂ] ℂ, IsState g ∧ restrictState φ g = f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let fP := positiveOfSquares f hf.2
  have hf1 : fP 1 = 1 := ((isState_iff f).mp hf).1
  obtain ⟨gP, hg1, hagree⟩ := CurrentMain.state_extension φ hφ fP hf1
  let g : B →L[ℂ] ℂ := gP.toLinearMap.mkContinuous 1 (fun b => by
    change ‖gP b‖ ≤ 1 * ‖b‖
    simpa only [hg1, Complex.one_re, one_mul] using positive_norm_apply_le gP b)
  have hg : IsState g := by
    apply (isState_iff g).mpr
    refine ⟨?_, fun b => ?_⟩
    · change gP 1 = 1
      exact hg1
    change (gP (star b * b)).im = 0 ∧ 0 ≤ (gP (star b * b)).re
    have h := gP.map_nonneg (star_mul_self_nonneg b)
    exact ⟨h.2.symm, h.1⟩
  refine ⟨g, hg, ?_⟩
  ext a
  change gP (φ a) = f a
  simpa only [fP, positiveOfSquares_apply] using hagree a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometricCompressionState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # States pulled back through an isometric compression -/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem state_comp_isometricCompression
    (V : H →L[ℂ] K) (hV : Isometry V)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) :
    IsState (φ.comp (operatorCompression V)) := by
  apply (isState_iff _).mpr
  constructor
  · change φ (V.adjoint.comp V)=1
    rw [V.isometry_iff_adjoint_comp_self.mp hV]
    exact ((isState_iff φ).mp hφ).1
  · intro T
    have he : operatorCompression V (star T*T)=(T.comp V).adjoint.comp (T.comp V) := by
      simp only [operatorCompression_apply,ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.star_eq_adjoint]
      rfl
    change (φ (operatorCompression V (star T*T))).im=0 ∧
      0 ≤ (φ (operatorCompression V (star T*T))).re
    rw [he]
    have hp := (positiveOfSquares φ hφ.2).map_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_adjoint_comp_self (T.comp V)))
    exact ⟨hp.2.symm,hp.1⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PureCommutingCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression to a pure cyclic representation

A pure vector-state restriction makes every commuting operator scalar
after compression to the cyclic subspace. This is the factorization step
for the initial product state on the two commuting factor algebras.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexStarModule ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

theorem cyclicGNSMap_intertwines (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a, f a=inner ℂ ξ (π a ξ)) (a : A) :
    (cyclicGNSMap f π ξ hcoeff).comp (f.gnsStarAlgHom a)=
      (π a).comp (cyclicGNSMap f π ξ hcoeff) := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
  funext b
  simp only [ContinuousLinearMap.comp_apply,Function.comp_apply,gns_apply_vector,
    gns_apply_coe,cyclicGNSMap_apply,map_mul,mul_apply_eq_comp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicStateCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Compression along a state-preserving inclusion

The GNS isometry supplies a concrete unital positive compression and its
matrix coefficients. It will be used to prescribe the two product marginals.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem gns_matrix_coefficient (P : B →ₚ[ℂ] ℂ) (x c y : B) :
    inner ℂ (P.gnsStarAlgHom x (gnsVector P))
      (P.gnsStarAlgHom c (P.gnsStarAlgHom y (gnsVector P)))=P (star x*c*y) := by
  rw [← gnsVector_coefficient P (star x*c*y)]
  simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem gnsInclusion_isometry (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) : Isometry (gnsInclusion P Q ι hPQ) := by
  apply (AddMonoidHomClass.isometry_iff_norm _).mpr
  exact cyclicGNSMap_norm Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom
    (gnsVector P) (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm)

theorem gnsInclusion_vector (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) :
    gnsInclusion P Q ι hPQ (gnsVector Q)=gnsVector P := by
  change cyclicGNSMap Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom (gnsVector P)
    (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm) (Q.toPreGNS 1)=_
  rw [cyclicGNSMap_apply]
  have hone : (P.gnsStarAlgHom.comp ι) 1=1 := map_one _
  change (P.gnsStarAlgHom.comp ι) 1 (gnsVector P)=_
  rw [hone]
  rfl

theorem gnsInclusion_intertwines (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (a : A) :
    (gnsInclusion P Q ι hPQ).comp (Q.gnsStarAlgHom a)=
      (P.gnsStarAlgHom (ι a)).comp (gnsInclusion P Q ι hPQ) :=
  cyclicGNSMap_intertwines Q (P.gnsStarAlgHom.comp ι).toNonUnitalStarAlgHom
    (gnsVector P) (fun a => (hPQ a).trans (gnsVector_coefficient P (ι a)).symm) a

theorem gnsInclusion_orbit (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (a : A) :
    gnsInclusion P Q ι hPQ (Q.gnsStarAlgHom a (gnsVector Q))=
      P.gnsStarAlgHom (ι a) (gnsVector P) := by
  have h := congrArg (fun L : Q.GNS →L[ℂ] P.GNS => L (gnsVector Q))
    (gnsInclusion_intertwines P Q ι hPQ a)
  change gnsInclusion P Q ι hPQ (Q.gnsStarAlgHom a (gnsVector Q))=
    P.gnsStarAlgHom (ι a) (gnsInclusion P Q ι hPQ (gnsVector Q)) at h
  rwa [gnsInclusion_vector] at h

theorem gnsCompression_state (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a))
    (F : (Q.GNS →L[ℂ] Q.GNS) →L[ℂ] ℂ) (hF : IsState F) :
    IsState (F.comp (gnsCompression P Q ι hPQ)) := by
  have hG := state_comp_isometricCompression (gnsInclusion P Q ι hPQ)
    (gnsInclusion_isometry P Q ι hPQ) F hF
  have he : F.comp (gnsCompression P Q ι hPQ)=
      restrictState P.gnsStarAlgHom (F.comp (operatorCompression (gnsInclusion P Q ι hPQ))) := by
    ext b
    rfl
  rw [he]
  exact isState_restrict P.gnsStarAlgHom
    (F.comp (operatorCompression (gnsInclusion P Q ι hPQ))) hG

theorem gnsCompression_pairing (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (c : B) (x y : A) :
    inner ℂ (Q.gnsStarAlgHom x (gnsVector Q))
      (gnsCompression P Q ι hPQ c (Q.gnsStarAlgHom y (gnsVector Q)))=
        P (star (ι x)*c*ι y) := by
  change inner ℂ (Q.gnsStarAlgHom x (gnsVector Q))
    ((gnsInclusion P Q ι hPQ).adjoint
      (P.gnsStarAlgHom c (gnsInclusion P Q ι hPQ (Q.gnsStarAlgHom y (gnsVector Q)))))=_
  rw [ContinuousLinearMap.adjoint_inner_right,gnsInclusion_orbit,gnsInclusion_orbit]
  exact gns_matrix_coefficient P (ι x) c (ι y)

theorem gnsCompression_eq_of_pairings (P : B →ₚ[ℂ] ℂ) (Q : A →ₚ[ℂ] ℂ)
    (ι : A →⋆ₐ[ℂ] B) (hPQ : ∀ a, Q a=P (ι a)) (c : B) (T : Q.GNS →L[ℂ] Q.GNS)
    (hT : ∀ x y : A, P (star (ι x)*c*ι y)=
      inner ℂ (Q.gnsStarAlgHom x (gnsVector Q)) (T (Q.gnsStarAlgHom y (gnsVector Q)))) :
    gnsCompression P Q ι hPQ c=T := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic Q).equalizer (gnsCompression P Q ι hPQ c).continuous T.continuous
  funext y
  apply DenseRange.eq_of_inner_right ℂ (gnsVector_cyclic Q)
  intro x
  change inner ℂ (Q.gnsStarAlgHom x (gnsVector Q))
    (gnsCompression P Q ι hPQ c (Q.gnsStarAlgHom y (gnsVector Q)))=
      inner ℂ (Q.gnsStarAlgHom x (gnsVector Q)) (T (Q.gnsStarAlgHom y (gnsVector Q)))
  rw [gnsCompression_pairing]
  exact hT x y

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateMarginalChange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Changing one marginal of a product state

A faithful GNS representation of one marginal allows any other state on that
algebra to be extended to the GNS operator algebra. Pulling it back through the
cyclic compression changes precisely that marginal of the product state.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder B] [StarOrderedRing B] in
theorem gnsCompression_product
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (φ : C →L[ℂ] ℂ) (hφ : IsState φ)
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ)
    (hprod : ∀ a b, φ (ι a*κ b)=f a*g b)
    (hres : ∀ a, f a=φ (ι a)) (a : A) (b : B) :
    gnsCompression (positiveOfSquares φ hφ.2) (positiveOfSquares f hf.2) ι hres
      (ι a*κ b)=g b • (positiveOfSquares f hf.2).gnsStarAlgHom a := by
  apply gnsCompression_eq_of_pairings
  intro x y
  have he : star (ι x)*(ι a*κ b)*ι y=ι (star x*a*y)*κ b := by
    simp only [map_mul,map_star,mul_assoc]
    rw [(hcomm y b).eq]
  change φ (star (ι x)*(ι a*κ b)*ι y)=_
  rw [he,hprod]
  simp only [smul_apply,inner_smul_right]
  rw [gns_matrix_coefficient]
  exact mul_comm _ _

theorem exists_product_state_change_left
    (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (φ : C →L[ℂ] ℂ) (hφ : IsState φ)
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ) (hg : IsState g)
    (hprod : ∀ a b, φ (ι a*κ b)=f a*g b)
    (hfaith : Function.Injective (positiveOfSquares f hf.2).gnsStarAlgHom)
    (f' : A →L[ℂ] ℂ) (hf' : IsState f') :
    ∃ ψ : C →L[ℂ] ℂ, IsState ψ ∧ ∀ a b, ψ (ι a*κ b)=f' a*g b := by
  let P := positiveOfSquares φ hφ.2
  let Q := positiveOfSquares f hf.2
  have hres (a : A) : Q a=P (ι a) := by
    change f a=φ (ι a)
    have h := hprod a 1
    simpa only [map_one,mul_one,((isState_iff g).mp hg).1] using h.symm
  obtain ⟨F,hF,hFres⟩ := exists_state_extension_of_embedding Q.gnsStarAlgHom hfaith f' hf'
  let E := gnsCompression P Q ι hres
  refine ⟨F.comp E,gnsCompression_state P Q ι hres F hF,?_⟩
  intro a b
  have he : E (ι a*κ b)=g b • Q.gnsStarAlgHom a :=
    gnsCompression_product ι κ hcomm φ hφ f hf g hprod hres a b
  change F (E (ι a*κ b))=_
  rw [he,map_smul]
  have hval : F (Q.gnsStarAlgHom a)=f' a :=
    congrArg (fun L : A →L[ℂ] ℂ => L a) hFres
  rw [hval]
  exact mul_comm _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimpleCommutingProductState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Product states for commuting simple C-star algebras

First extend a pure state and use its scalar commutant compression. Two
successive GNS compressions then prescribe arbitrary states on both algebras.
Only the simplicity and faithful embedding of the two algebras are required.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem state_gns_injective_of_simple
    [PartialOrder A] [StarOrderedRing A] (hA : CStarSimple A)
    (f : A →L[ℂ] ℂ) (hf : IsState f) :
    Function.Injective (positiveOfSquares f hf.2).gnsStarAlgHom := by
  let P := positiveOfSquares f hf.2
  have hn : ‖gnsVector P‖=1 := gnsVector_norm_eq_one P ((isState_iff f).mp hf).1
  let : Nontrivial P.GNS := ⟨⟨gnsVector P,0,by
    intro h
    rw [h,norm_zero] at hn
    exact zero_ne_one hn⟩⟩
  exact CurrentMain.simple_starAlgHom_injective hA P.gnsStarAlgHom

theorem exists_product_state_of_commuting_simple_oai [Nontrivial A]
    (hA : CStarSimple A) (hB : CStarSimple B)
    (ι : A →⋆ₐ[ℂ] C) (hι : Function.Injective ι)
    (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ) (hg : IsState g) :
    ∃ φ : C →L[ℂ] ℂ, IsState φ ∧ ∀ a b, φ (ι a*κ b)=f a*g b := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  obtain ⟨f₀,hf₀,hpure⟩ := exists_pure_state (A:=A)
  obtain ⟨φ₀,hφ₀,hres⟩ := exists_state_extension_of_embedding ι hι f₀ hf₀
  let g₀ := restrictState κ φ₀
  have hg₀ : IsState g₀ := isState_restrict κ φ₀ hφ₀
  have hp₀ : IsPureState (restrictState ι φ₀) := by rwa [hres]
  have hprod₀ (a : A) (b : B) : φ₀ (ι a*κ b)=f₀ a*g₀ b := by
    rw [pure_restriction_commuting_factorization ι φ₀ hφ₀ hp₀ (κ b)
      (fun c => (hcomm c b).symm) a]
    have hval : φ₀ (ι a)=f₀ a := congrArg (fun L : A →L[ℂ] ℂ => L a) hres
    rw [hval]
    rfl
  have hswap (b : B) (a : A) : φ₀ (κ b*ι a)=g₀ b*f₀ a := by
    rw [← (hcomm a b).eq,hprod₀,mul_comm]
  obtain ⟨φ₁,hφ₁,hprod₁⟩ := exists_product_state_change_left κ ι
    (fun b a => (hcomm a b).symm) φ₀ hφ₀ g₀ hg₀ f₀ hf₀ hswap
    (state_gns_injective_of_simple hB g₀ hg₀) g hg
  have hprod₂ (a : A) (b : B) : φ₁ (ι a*κ b)=f₀ a*g b := by
    rw [(hcomm a b).eq,hprod₁,mul_comm]
  exact exists_product_state_change_left ι κ hcomm φ₁ hφ₁ f₀ hf₀ g hg hprod₂
    (state_gns_injective_of_simple hA f₀ hf₀) f hf

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_product_state_of_commuting_simple_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_product_state_of_commuting_simple_oai.{u_1, u_2, u_3}
