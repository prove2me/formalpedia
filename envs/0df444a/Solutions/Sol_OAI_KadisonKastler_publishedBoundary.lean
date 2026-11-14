-- Prove2me | solution 1 for OAI.KadisonKastler.publishedBoundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:59:29.605213+00:00
-- url     : https://prove2.me/submissions/f99e1f37-0ad4-4b6b-b154-28eaaeb37ae5

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K065

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableRandomWalkLaw
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A symmetric fully supported law for the boundary random walk

The boundary construction starts with a probability law that assigns positive
mass to every element of the countable group. A geometric enumeration gives
such a law, and averaging with its inverse image makes it symmetric.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem symmetricRandomWalkLaw_inv : (symmetricRandomWalkLaw G).map Inv.inv =
    symmetricRandomWalkLaw G := by
  rw [symmetricRandomWalkLaw, Measure.map_add _ _ (measurable_of_countable _)]
  rw [Measure.map_smul,
    Measure.map_smul,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hid : (Inv.inv : G → G) ∘ Inv.inv = id := by funext g; exact inv_inv g
  rw [hid, Measure.map_id, add_comm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonsingularBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular boundary actions and simultaneous representatives

The action preserves null sets, not necessarily the measure. Countability
allows all the identities used in the boundary argument to hold on one
invariant conull set. The final definition isolates the exact unitary
coefficient property in Björklund, arXiv:1406.0763, Theorem 2.1 and
Remark 2.2, expressed as a property of the unitary coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {G D : Type*} [Group G] [MeasurableSpace D]

namespace NonsingularAction

variable {μ : Measure D} (α : NonsingularAction G D μ)

/-- If an equivariant function is almost everywhere constant, its constant
value is fixed. This uses nonsingularity and does not use invariance of μ. -/
theorem fixed_of_ae_constant [NeZero μ]
    {E : Type*} (σ : G → E → E) (f : D → E) (v : E)
    (hf : f =ᵐ[μ] fun _ => v)
    (heq : ∀ g, ∀ᵐ x ∂μ, f (α.toPerm g x) = σ g (f x)) :
    ∀ g, σ g v = v := by
  intro g
  have hp := (α.quasi g).ae hf
  have hall : ∀ᵐ x ∂μ, σ g v = v := by
    filter_upwards [hf, hp, heq g] with x hx hpx hex
    rw [hx, hpx] at hex
    exact hex.symm
  exact hall.exists.choose_spec

end NonsingularAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkIdentityBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The boundary law of a walk starting at the identity

The initial root law was chosen with full support. Starting at the identity
is absolutely continuous before taking the invariant factor; after one
increment its boundary law is exactly the chosen boundary probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Countable G] [MeasurableSingletonClass G] in
theorem randomWalkFromIdentity_measurable : Measurable (randomWalkFromIdentity G) :=
  measurable_const.prodMk measurable_id

theorem randomWalkFromIdentity_quasi :
    Measure.QuasiMeasurePreserving (randomWalkFromIdentity G)
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) (randomWalkPathLaw G) := by
  refine ⟨randomWalkFromIdentity_measurable G, ?_⟩
  change (Measure.map (Prod.mk (1 : G)) (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))) ≪ _
  rw [← Measure.dirac_prod]
  exact Measure.AbsolutelyContinuous.prod
    (absolutelyContinuous_symmetricRandomWalkLaw (Measure.dirac 1))
    (Measure.AbsolutelyContinuous.refl _)

theorem randomWalkAdvance_fromIdentity_law :
    (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)).map
      (randomWalkAdvance G ∘ randomWalkFromIdentity G) = randomWalkPathLaw G := by
  simpa [Function.comp_def, randomWalkAdvance, randomWalkFromIdentity, randomWalkPathLaw] using
    iid_first_increment_tail_law (symmetricRandomWalkLaw G)

theorem randomWalkIdentityBoundary_measurePreserving :
    MeasurePreserving (randomWalkIdentityBoundary G)
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) (randomWalkBoundaryMeasure G) := by
  have hm : Measurable (randomWalkIdentityBoundary G) :=
    (shiftBoundaryMap_measurePreserving (randomWalkPathLaw G) (randomWalkAdvance G)).measurable.comp
      (randomWalkFromIdentity_measurable G)
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro A hA
  change MeasurableSet[shiftInvariantSigma (randomWalkPathLaw G) (randomWalkAdvance G)] A at hA
  rw [Measure.map_apply hm hA]
  change _ = (randomWalkPathLaw G).trim (shiftInvariantSigma_le _ _) A
  rw [trim_measurableSet_eq _ hA, ← randomWalkAdvance_fromIdentity_law G,
    Measure.map_apply ((randomWalkAdvance_measurable G).comp (randomWalkFromIdentity_measurable G)) hA.1]
  apply measure_congr
  have hs := (randomWalkFromIdentity_quasi G).ae hA.2
  filter_upwards [hs] with ω hω
  exact propext hω.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralRandomWalk
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Independent forward and reflected backward random walks -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem bilateralFuture_measurable : Measurable (bilateralFuture G) :=
  Measurable.of_eval (fun n => measurable_pi_apply (n : ℤ))

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem bilateralPast_measurable : Measurable (bilateralPast G) :=
  Measurable.of_eval (fun n => measurable_pi_apply (-(n : ℤ) - 1))

theorem bilateralReflectedPast_measurable : Measurable (bilateralReflectedPast G) :=
  Measurable.of_eval (fun n => (measurable_of_countable (Inv.inv : G → G)).comp
    (measurable_pi_apply (-(n : ℤ) - 1)))

theorem bilateralFuture_law : (bilateralWalkLaw G).map (bilateralFuture G) =
    Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) :=
  Measure.map_infinitePi_infinitePi_of_inj Int.ofNat_injective

theorem bilateralPast_law : (bilateralWalkLaw G).map (bilateralPast G) =
    Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) := by
  have hi : Function.Injective (fun n : ℕ => -(n : ℤ) - 1) := by
    intro a b hab
    dsimp only at hab
    omega
  exact Measure.map_infinitePi_infinitePi_of_inj hi

theorem bilateralReflectedPast_law : (bilateralWalkLaw G).map (bilateralReflectedPast G) =
    Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) := by
  let I : (ℕ → G) → (ℕ → G) := fun ω n => (ω n)⁻¹
  have hm : Measurable I := Measurable.of_eval (fun n =>
    (measurable_of_countable (Inv.inv : G → G)).comp (measurable_pi_apply n))
  change (bilateralWalkLaw G).map (I ∘ bilateralPast G) = _
  rw [← Measure.map_map hm (bilateralPast_measurable G), bilateralPast_law]
  simpa only [symmetricRandomWalkLaw_inv] using
    (Measure.infinitePi_map_pi (fun _ : ℕ => symmetricRandomWalkLaw G)
      (fun _ : ℕ => measurable_of_countable (Inv.inv : G → G)))

theorem bilateral_halves_independent :
    IndepFun (bilateralFuture G) (bilateralPast G) (bilateralWalkLaw G) := by
  let m : ℤ → MeasurableSpace (BilateralWalkPath G) := fun n =>
    MeasurableSpace.comap (fun ω => ω n) inferInstance
  have hi : iIndep m (bilateralWalkLaw G) :=
    iIndepFun_infinitePi (X := fun _ (g : G) => g) (fun _ => measurable_id)
  have hm (n : ℤ) : m n ≤ (inferInstance : MeasurableSpace (BilateralWalkPath G)) :=
    (measurable_pi_apply n).comap_le
  have hd : Disjoint {n : ℤ | 0 ≤ n} {n : ℤ | n < 0} := by
    apply Set.disjoint_left.mpr
    intro n hn hp
    change 0 ≤ n at hn
    change n < 0 at hp
    omega
  have hh := indep_iSup_of_disjoint hm hi hd
  have hfuture : MeasurableSpace.comap (bilateralFuture G) inferInstance ≤
      ⨆ n ∈ {n : ℤ | 0 ≤ n}, m n := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (n : ℤ) (le_iSup_of_le (Int.natCast_nonneg n) le_rfl)
  have hpast : MeasurableSpace.comap (bilateralPast G) inferInstance ≤
      ⨆ n ∈ {n : ℤ | n < 0}, m n := by
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro n
    exact le_iSup_of_le (-(n : ℤ) - 1) (le_iSup_of_le (by change -(n : ℤ) - 1 < 0; omega) le_rfl)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hh hfuture) hpast

theorem bilateral_reflected_halves_independent :
    IndepFun (bilateralFuture G) (bilateralReflectedPast G) (bilateralWalkLaw G) := by
  exact (bilateral_halves_independent G).comp measurable_id
    (Measurable.of_eval (fun n => (measurable_of_countable (Inv.inv : G → G)).comp
      (measurable_pi_apply n)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBoundaryPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two boundary endpoints of a bilateral random walk

The forward and reflected backward halves have the exact boundary product
law. Every integer shift preserves the bilateral path probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem bilateralPositiveBoundary_measurePreserving :
    MeasurePreserving (bilateralPositiveBoundary G) (bilateralWalkLaw G) (randomWalkBoundaryMeasure G) :=
  (randomWalkIdentityBoundary_measurePreserving G).comp
    ⟨bilateralFuture_measurable G, bilateralFuture_law G⟩

theorem bilateralNegativeBoundary_measurePreserving :
    MeasurePreserving (bilateralNegativeBoundary G) (bilateralWalkLaw G) (randomWalkBoundaryMeasure G) :=
  (randomWalkIdentityBoundary_measurePreserving G).comp
    ⟨bilateralReflectedPast_measurable G, bilateralReflectedPast_law G⟩

theorem bilateralBoundary_independent :
    IndepFun (bilateralPositiveBoundary G) (bilateralNegativeBoundary G) (bilateralWalkLaw G) :=
  (bilateral_reflected_halves_independent G).comp
    (randomWalkIdentityBoundary_measurePreserving G).measurable
    (randomWalkIdentityBoundary_measurePreserving G).measurable

theorem bilateralBoundaryPair_measurePreserving :
    MeasurePreserving (bilateralBoundaryPair G) (bilateralWalkLaw G)
      ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)) := by
  have hp := bilateralPositiveBoundary_measurePreserving G
  have hn := bilateralNegativeBoundary_measurePreserving G
  refine ⟨hp.measurable.prodMk hn.measurable, ?_⟩
  exact ((bilateralBoundary_independent G).map_prod_eq_prod_map_map hp.measurable.aemeasurable
    hn.measurable.aemeasurable).trans (by rw [hp.map_eq, hn.map_eq])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertInvariantFunctions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Hilbert-valued functions on an invariant sigma algebra

Scalar matrix coefficients and separability turn measurable invariance into
simultaneous almost-everywhere equality of the Hilbert-valued functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} {S : X → X}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [TopologicalSpace.SeparableSpace K]
  [MeasurableSpace K] [BorelSpace K]

theorem hilbert_fixed_of_measurable_shiftInvariantSigma {f : X → K}
    (hf : Measurable[shiftInvariantSigma μ S] f) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  have hc (c : K) : (fun x => inner ℂ c (f (S x) - f x)) =ᵐ[μ] 0 := by
    have hm : Measurable[shiftInvariantSigma μ S] (fun x => inner ℂ c (f x)) :=
      (continuous_const.inner continuous_id).measurable.comp hf
    filter_upwards [complex_fixed_of_measurable_shiftInvariantSigma hm] with x hx
    simp only [inner_sub_right, hx, sub_self, Pi.zero_apply]
  have hz := ae_eq_zero_of_forall_inner hc
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

omit [MeasurableSpace K] [BorelSpace K] in
theorem hilbert_fixed_of_aestronglyMeasurable_shiftInvariantSigma
    (hS : Measure.QuasiMeasurePreserving S μ μ) {f : X → K}
    (hf : AEStronglyMeasurable[shiftInvariantSigma μ S] f μ) :
    ∀ᵐ x ∂μ, f (S x) = f x := by
  borelize K
  have hm := hilbert_fixed_of_measurable_shiftInvariantSigma hf.stronglyMeasurable_mk.measurable
  filter_upwards [hf.ae_eq_mk, hS.ae hf.ae_eq_mk, hm] with x hx hs hm
  exact hs.trans (hm.trans hx.symm)

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [MeasurableSpace K] [BorelSpace K] in
theorem firstInvariantSigma_fixed_hilbert (hS : Measure.QuasiMeasurePreserving S μ μ)
    {f : X × Y → K} (hf : AEStronglyMeasurable[firstInvariantSigma μ S] f (μ.prod ν)) :
    ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z :=
  hilbert_fixed_of_aestronglyMeasurable_shiftInvariantSigma (firstCoordinateShift_quasi hS)
    (hf.mono (firstInvariantSigma_le_shiftInvariantSigma (ν := ν)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryPairInvariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Hilbert-valued boundary functions are invariant under advancing either path. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y K : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [TopologicalSpace.SeparableSpace K]

theorem hilbert_boundary_first_invariance (hS : Measure.QuasiMeasurePreserving S μ μ)
    {f : ShiftBoundarySpace μ S × Y → K}
    (hf : AEStronglyMeasurable f ((shiftBoundaryMeasure μ S).prod ν)) :
    ∀ᵐ z ∂μ.prod ν,
      f (shiftBoundaryMap μ S (S z.1), z.2) = f (shiftBoundaryMap μ S z.1, z.2) := by
  have ht : AEStronglyMeasurable[firstInvariantSigma μ S]
      (fun z : X × Y => f (shiftBoundaryMap μ S z.1, z.2))
      ((μ.prod ν).trim (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S))) := by
    rw [firstBoundaryMeasure_eq_trim μ S]
    exact hf
  exact firstInvariantSigma_fixed_hilbert hS (ht.of_trim (firstInvariantSigma_le (Y := Y) (μ := μ) (S := S)))

variable {f : ShiftBoundarySpace μ S × ShiftBoundarySpace μ S → K}

omit [IsProbabilityMeasure ν] in
theorem boundaryPairLift_advance_left (hS : Measure.QuasiMeasurePreserving S μ μ)
    (hf : AEStronglyMeasurable f ((shiftBoundaryMeasure μ S).prod (shiftBoundaryMeasure μ S))) :
    ∀ᵐ z ∂μ.prod μ, boundaryPairLift f (S z.1, z.2) = boundaryPairLift f z := by
  have ht : AEStronglyMeasurable
      (fun z : ShiftBoundarySpace μ S × X => f (z.1, shiftBoundaryMap μ S z.2))
      ((shiftBoundaryMeasure μ S).prod μ) :=
    hf.comp_quasiMeasurePreserving ((MeasurePreserving.id (shiftBoundaryMeasure μ S)).prod
      (shiftBoundaryMap_measurePreserving μ S)).quasiMeasurePreserving
  exact hilbert_boundary_first_invariance hS ht

omit [IsProbabilityMeasure ν] in
theorem boundaryPairLift_advance_right (hS : Measure.QuasiMeasurePreserving S μ μ)
    (hf : AEStronglyMeasurable f ((shiftBoundaryMeasure μ S).prod (shiftBoundaryMeasure μ S))) :
    ∀ᵐ z ∂μ.prod μ, boundaryPairLift f (z.1, S z.2) = boundaryPairLift f z := by
  have hs := hf.comp_quasiMeasurePreserving (Measure.measurePreserving_swap
    (μ := shiftBoundaryMeasure μ S) (ν := shiftBoundaryMeasure μ S)).quasiMeasurePreserving
  have hi := boundaryPairLift_advance_left hS hs
  exact (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hi

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableQuasiSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Countable measurable selection of nonsingular maps is nonsingular. -/

namespace KadisonKastler

open MeasureTheory

variable {I X Y : Type*} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

theorem quasiMeasurePreserving_countable_selection {T : I → X → Y}
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν)
    {c : X → I} (hc : Measurable c) :
    Measure.QuasiMeasurePreserving (fun x => T (c x) x) μ ν := by
  have hm : Measurable (fun p : I × X => T p.1 p.2) :=
    measurable_from_prod_countable_right (fun i => (hT i).measurable)
  have hsel : Measurable (fun x => T (c x) x) := hm.comp (hc.prodMk measurable_id)
  refine ⟨hsel, ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hzero
  rw [Measure.map_apply hsel hA]
  have havoid : ∀ᵐ y ∂ν, y ∉ A := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hzero
  have hall : ∀ᵐ x ∂μ, ∀ i, T i x ∉ A :=
    ae_all_iff.mpr (fun i => (hT i).ae havoid)
  change μ {x | T (c x) x ∈ A} = 0
  simpa only [not_not] using (ae_iff.mp (hall.mono (fun x hx => hx (c x))))

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkPrefix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Inserting prescribed countable roots and first increments is nonsingular. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem randomWalkPrepend_measurable :
    Measurable (fun p : G × (ℕ → G) => randomWalkPrepend G p.1 p.2) := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem randomWalkPrepend_law :
    (randomWalkPathLaw G).map (fun p => randomWalkPrepend G p.1 p.2) =
      Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) := by
  let ν := Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)
  let T : (ℕ → G) → G × (ℕ → G) := fun ω => (ω 0, fun n => ω (n + 1))
  have hm : Measurable T := (measurable_pi_apply 0).prodMk
    (Measurable.of_eval (fun n => measurable_pi_apply (n + 1)))
  change ((symmetricRandomWalkLaw G).prod ν).map _ = ν
  rw [← iid_first_increment_tail_law (symmetricRandomWalkLaw G),
    Measure.map_map (randomWalkPrepend_measurable G) hm]
  have he : (fun p => randomWalkPrepend G p.1 p.2) ∘ T = id := by
    funext ω n
    cases n <;> rfl
  rw [he, Measure.map_id]

theorem randomWalkRoot_quasi (g : G) :
    Measure.QuasiMeasurePreserving (fun ω : ℕ → G => (g, ω))
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) (randomWalkPathLaw G) := by
  refine ⟨measurable_const.prodMk measurable_id, ?_⟩
  rw [← Measure.dirac_prod]
  exact Measure.AbsolutelyContinuous.prod
    (absolutelyContinuous_symmetricRandomWalkLaw (Measure.dirac g))
    (Measure.AbsolutelyContinuous.refl _)

theorem randomWalkPrepend_quasi (g : G) :
    Measure.QuasiMeasurePreserving (randomWalkPrepend G g)
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) := by
  have hp : Measure.QuasiMeasurePreserving
      (fun p : RandomWalkPath G => randomWalkPrepend G p.1 p.2)
      (randomWalkPathLaw G) (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) :=
    ⟨randomWalkPrepend_measurable G, (randomWalkPrepend_law G).symm ▸ Measure.AbsolutelyContinuous.refl _⟩
  exact hp.comp (randomWalkRoot_quasi G g)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBoundaryTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.bilateralIncrementProduct_succ _root_.OAI.KadisonKastler.bilateralIncrementProduct_zero _root_.OAI.KadisonKastler.bilateralTranslate_add _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.nestedMeanRowsL_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The boundary pair transforms by the inverse increment under a bilateral shift.

The boundary uses an invariant sigma algebra, not a point quotient. Its endpoint
identities are therefore proved on measurable Hilbert-valued functions.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem bilateralRawHalves_measurePreserving :
    MeasurePreserving (bilateralRawHalves G) (bilateralWalkLaw G)
      ((Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)).prod
        (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))) := by
  refine ⟨(bilateralFuture_measurable G).prodMk (bilateralReflectedPast_measurable G), ?_⟩
  exact ((bilateral_reflected_halves_independent G).map_prod_eq_prod_map_map
    (bilateralFuture_measurable G).aemeasurable (bilateralReflectedPast_measurable G).aemeasurable).trans
      (by rw [bilateralFuture_law, bilateralReflectedPast_law])

theorem bilateralTransportPairAt_quasi (g : G) :
    Measure.QuasiMeasurePreserving (bilateralTransportPairAt G g) (bilateralWalkLaw G)
      ((randomWalkPathLaw G).prod (randomWalkPathLaw G)) :=
  (MeasureTheory.QuasiMeasurePreserving.prodMap (randomWalkRoot_quasi G g⁻¹)
    ((randomWalkRoot_quasi G 1).comp (randomWalkPrepend_quasi G g⁻¹))).comp
      (bilateralRawHalves_measurePreserving G).quasiMeasurePreserving

theorem bilateralTransportPair_quasi :
    Measure.QuasiMeasurePreserving (bilateralTransportPair G) (bilateralWalkLaw G)
      ((randomWalkPathLaw G).prod (randomWalkPathLaw G)) :=
  quasiMeasurePreserving_countable_selection (bilateralTransportPairAt_quasi G) (measurable_pi_apply 0)

theorem bilateralTransportPair_first (ω : BilateralWalkPath G) :
    (shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G)
        (randomWalkAdvance G (bilateralTransportPair G ω).1),
      shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G) (bilateralTransportPair G ω).2) =
    bilateralBoundaryPair G (bilateralTranslate G 1 ω) := by
  apply Prod.ext
  · change ((ω 0)⁻¹ * ω 0, fun n : ℕ => ω ((n + 1 : ℕ) : ℤ)) =
      (1, fun n : ℕ => ω ((n : ℤ) + 1))
    simp
  · change (1, randomWalkPrepend G (ω 0)⁻¹ (bilateralReflectedPast G ω)) =
      (1, bilateralReflectedPast G (bilateralTranslate G 1 ω))
    congr 1
    funext n
    cases n with
    | zero => simp [randomWalkPrepend, bilateralReflectedPast, bilateralPast, bilateralTranslate]
    | succ n =>
      dsimp [randomWalkPrepend, bilateralReflectedPast, bilateralPast, bilateralTranslate]
      congr 2
      omega

theorem bilateralTransportPair_second (ω : BilateralWalkPath G) :
    (shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G) (bilateralTransportPair G ω).1,
      shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G)
        (randomWalkAdvance G (bilateralTransportPair G ω).2)) =
    (randomWalkBoundaryAction G).diagonal.toPerm (ω 0)⁻¹ (bilateralBoundaryPair G ω) := by
  change ((_, _), (1 * (ω 0)⁻¹, _)) = ((_, _), ((ω 0)⁻¹ * 1, _))
  simp only [one_mul, mul_one]
  simp [bilateralTransportPair, bilateralTransportPairAt, randomWalkPrepend, Equiv.mulLeft]

variable {G} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateral_boundary_function_transport
    {f : RandomWalkBoundary G × RandomWalkBoundary G → K}
    (hf : AEStronglyMeasurable f ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G))) :
    ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralBoundaryPair G (bilateralTranslate G 1 ω)) =
      f ((randomWalkBoundaryAction G).diagonal.toPerm (ω 0)⁻¹ (bilateralBoundaryPair G ω)) := by
  have hl := (bilateralTransportPair_quasi G).ae
    (boundaryPairLift_advance_left (randomWalkAdvance_quasi (G := G)) hf)
  have hr := (bilateralTransportPair_quasi G).ae
    (boundaryPairLift_advance_right (randomWalkAdvance_quasi (G := G)) hf)
  filter_upwards [hl, hr] with ω hleft hright
  change f _ = f _ at hleft hright
  rw [← bilateralTransportPair_first, ← bilateralTransportPair_second]
  exact hleft.trans hright.symm

theorem bilateral_equivariant_function_transport [CompleteSpace K]
    (σ : G →* unitary (K →L[ℂ] K)) {f : RandomWalkBoundary G × RandomWalkBoundary G → K}
    (hf : AEStronglyMeasurable f ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)))
    (he : ∀ g, ∀ᵐ z ∂(randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G),
      f ((randomWalkBoundaryAction G).diagonal.toPerm g z) = (σ g : K →L[ℂ] K) (f z)) :
    ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralBoundaryPair G (bilateralTranslate G 1 ω)) =
      (σ (ω 0)⁻¹ : K →L[ℂ] K) (f (bilateralBoundaryPair G ω)) := by
  have he' := (bilateralBoundaryPair_measurePreserving G).quasiMeasurePreserving.ae
    (ae_all_iff.mpr he)
  filter_upwards [bilateral_boundary_function_transport hf, he'] with ω ht heω
  exact ht.trans (heω (ω 0)⁻¹)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralCocycle
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite random-walk cocycles and the iterated coefficient transport. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
theorem bilateralIncrementProduct_add (n m : ℕ) (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G (n + m) ω =
      bilateralIncrementProduct G m (bilateralTranslate G n ω) * bilateralIncrementProduct G n ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, bilateralIncrementProduct_succ, ih, bilateralIncrementProduct_succ]
    simp [bilateralTranslate, mul_assoc, add_comm]

variable {G} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem bilateral_transport_iterate (σ : G →* unitary (K →L[ℂ] K))
    {f : BilateralWalkPath G → K}
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) (n : ℕ) :
    ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G n ω) = (σ (bilateralIncrementProduct G n ω) : K →L[ℂ] K) (f ω) := by
  induction n with
  | zero =>
    apply Filter.Eventually.of_forall
    intro ω
    have hzero : bilateralTranslate G 0 ω = ω := by funext j; simp [bilateralTranslate]
    simp [hzero, bilateralIncrementProduct]
  | succ n ih =>
    have hs := (bilateralTranslate_measurePreserving G n).quasiMeasurePreserving.ae ht
    filter_upwards [hs, ih] with ω hs hω
    have hn : (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by omega
    rw [bilateralTranslate_add, hn] at hs
    rw [hs, hω, bilateralIncrementProduct_succ, map_mul]
    simp only [bilateralTranslate, zero_add]
    rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCoordinateL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Density of finite-coordinate Hilbert functions

The random-walk proof needs approximants depending on a finite block. The
orthogonal complement is zero because its integrals over all cylinder sets
vanish, and cylinders generate the product sigma algebra.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {G K : Type*} [MeasurableSpace G]
  {μ : Measure (ℤ → G)} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
theorem finiteCoordinateL2_indicator (I : Finset ℤ) (A : Set (∀ _ : I, G))
    (hA : MeasurableSet A) (v : K) :
    indicatorConstLp 2 hA.cylinder (measure_ne_top μ _) v ∈ finiteCoordinateL2 μ := by
  refine ⟨I, ?_⟩
  have hm : @Measurable (ℤ → G) (∀ i : I, G)
      (cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)) _ (fun x i => x i) :=
    @Measurable.of_eval (ℤ → G) I (fun _ => G)
      (cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)) (fun _ => inferInstance)
      (fun x i => x i) (fun i => measurable_cylinderEvent_apply i.property)
  have hset : MeasurableSet[cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)] (cylinder I A) :=
    hm hA
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (mem_lpMeas_indicatorConstLp (𝕜 := ℂ) cylinderEvents_le_pi hset (measure_ne_top μ _))

theorem finiteCoordinateL2_orthogonal_eq_bot : (finiteCoordinateL2 (K := K) μ)ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  have hi : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  have hc (A : Set (ℤ → G)) (hA : A ∈ measurableCylinders (fun _ : ℤ => G)) :
      ∫ x in A, f x ∂μ = 0 := by
    obtain ⟨I, B, hB, rfl⟩ := (mem_measurableCylinders A).mp hA
    have hz (v : K) : inner ℂ v (∫ x in cylinder I B, f x ∂μ) = 0 := by
      rw [← L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hB.cylinder (measure_ne_top μ _) v f]
      exact hf _ (finiteCoordinateL2_indicator I B hB v)
    exact inner_self_eq_zero.mp (hz _)
  have hv : μ.withDensityᵥ (f : (ℤ → G) → K) = 0 := by
    apply VectorMeasure.ext_of_generateFrom (measurableCylinders (fun _ : ℤ => G))
    · intro A hA
      rw [withDensityᵥ_apply hi (MeasurableSet.of_mem_measurableCylinders hA), hc A hA]
      rfl
    · exact generateFrom_measurableCylinders.symm
    · exact isPiSystem_measurableCylinders
    · rw [withDensityᵥ_apply hi MeasurableSet.univ]
      apply hc
      exact (mem_measurableCylinders univ).mpr ⟨∅, univ, MeasurableSet.univ, (cylinder_univ ∅).symm⟩
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply hi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  simpa using hv

theorem finiteCoordinateL2_dense : Dense ((finiteCoordinateL2 (K := K) μ) : Set (Lp K 2 μ)) := by
  have h : (finiteCoordinateL2 (K := K) μ).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, finiteCoordinateL2_orthogonal_eq_bot]
    exact Submodule.bot_orthogonal_eq_top
  change ∀ f, f ∈ closure ((finiteCoordinateL2 (K := K) μ) : Set (Lp K 2 μ))
  intro f
  change f ∈ (finiteCoordinateL2 (K := K) μ).topologicalClosure
  rw [h]
  trivial

theorem exists_finiteCoordinate_L2_approximation (f : Lp K 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Finset ℤ) (g : Lp K 2 μ),
      AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (I : Set ℤ)] g μ ∧ dist f g < ε := by
  obtain ⟨g, ⟨I, hI⟩, hg⟩ := Metric.mem_closure_iff.mp (finiteCoordinateL2_dense (μ := μ) f) ε hε
  exact ⟨I, g, hI, hg⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralCoordinateSigma
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Coordinate measurability and independence for the bilateral product law. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem bilateralCoordinateSigma_independent {I J : Set ℤ} (hIJ : Disjoint I J) :
    Indep (cylinderEvents (X := fun _ : ℤ => G) I)
      (cylinderEvents (X := fun _ : ℤ => G) J) (bilateralWalkLaw G) := by
  let m : ℤ → MeasurableSpace (BilateralWalkPath G) := fun n =>
    MeasurableSpace.comap (fun ω => ω n) inferInstance
  have hi : iIndep m (bilateralWalkLaw G) :=
    iIndepFun_infinitePi (X := fun _ (g : G) => g) (fun _ => measurable_id)
  have hm (n : ℤ) : m n ≤ (inferInstance : MeasurableSpace (BilateralWalkPath G)) :=
    (measurable_pi_apply n).comap_le
  exact indep_iSup_of_disjoint hm hi hIJ

variable {G}

theorem bilateralCoordinate_indepFun {I J : Set ℤ} (hIJ : Disjoint I J)
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {f f' : BilateralWalkPath G → E} {g g' : BilateralWalkPath G → F}
    (hf : Measurable[cylinderEvents (X := fun _ : ℤ => G) I] f')
    (hg : Measurable[cylinderEvents (X := fun _ : ℤ => G) J] g')
    (hff' : f =ᵐ[bilateralWalkLaw G] f') (hgg' : g =ᵐ[bilateralWalkLaw G] g') :
    IndepFun f g (bilateralWalkLaw G) := by
  have hi : IndepFun f' g' (bilateralWalkLaw G) :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (bilateralCoordinateSigma_independent G hIJ) hf.comap_le)
      hg.comap_le
  exact hi.congr hff'.symm hgg'.symm

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem bilateralTranslate_coordinate_measurable {I J : Set ℤ} (k : ℤ)
    (hIJ : ∀ j ∈ I, j + k ∈ J) :
    @Measurable (BilateralWalkPath G) (BilateralWalkPath G)
      (cylinderEvents (X := fun _ : ℤ => G) J)
      (cylinderEvents (X := fun _ : ℤ => G) I) (bilateralTranslate G k) := by
  rw [measurable_cylinderEvents_iff]
  intro j hj
  exact measurable_cylinderEvent_apply (hIJ j hj)

theorem bilateralIncrementProduct_coordinate_measurable {I : Set ℤ} (n : ℕ)
    (hI : ∀ j : ℕ, j < n → (j : ℤ) ∈ I) :
    Measurable[cylinderEvents (X := fun _ : ℤ => G) I] (bilateralIncrementProduct G n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : G × G => p.1⁻¹ * p.2)).comp
      ((measurable_cylinderEvent_apply (hI n (Nat.lt_succ_self n))).prodMk
        (ih (fun j hj => hI j (hj.trans (Nat.lt_succ_self n)))))

variable {K : Type*} [NormedAddCommGroup K]

theorem bilateralTranslate_coordinate_aestronglyMeasurable {I J : Set ℤ} (k : ℤ)
    (hIJ : ∀ j ∈ I, j + k ∈ J) {f : BilateralWalkPath G → K}
    (hf : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) I] f (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) J]
      (f ∘ bilateralTranslate G k) (bilateralWalkLaw G) := by
  refine ⟨(hf.mk f) ∘ bilateralTranslate G k, ?_, ?_⟩
  · exact hf.stronglyMeasurable_mk.comp_measurable (bilateralTranslate_coordinate_measurable k hIJ)
  · exact (bilateralTranslate_measurePreserving G k).quasiMeasurePreserving.ae hf.ae_eq_mk

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Three separated increment blocks in the double-ergodicity proof. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
theorem bilateral_block_word_factorization (m : ℕ) (ω : BilateralWalkPath G) :
    bilateralIncrementProduct G (2 * m + 2) ω =
      bilateralRightWord G m ω * (bilateralMiddleWord G m ω * bilateralLeftWord G m ω) := by
  have hn : 2 * m + 2 = (m + 2) + m := by omega
  rw [hn, bilateralIncrementProduct_add]
  rfl

variable {G}

theorem bilateralIncrementProduct_shift_coordinate_measurable {I : Set ℤ} (k : ℤ) (n : ℕ)
    (hI : ∀ j : ℕ, j < n → (j : ℤ) + k ∈ I) :
    Measurable[cylinderEvents (X := fun _ : ℤ => G) I]
      (fun ω => bilateralIncrementProduct G n (bilateralTranslate G k ω)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun p : G × G => p.1⁻¹ * p.2)).comp
      ((measurable_cylinderEvent_apply (hI n (Nat.lt_succ_self n))).prodMk
        (ih (fun j hj => hI j (hj.trans (Nat.lt_succ_self n)))))

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_symmetricWindow_L2_approximation
    (f : Lp K 2 (bilateralWalkLaw G)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (g : Lp K 2 (bilateralWalkLaw G)),
      AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
        g (bilateralWalkLaw G) ∧ ‖f - g‖ < ε := by
  obtain ⟨I, g, hg, hfg⟩ := exists_finiteCoordinate_L2_approximation f hε
  refine ⟨I.sup Int.natAbs, g, hg.mono (cylinderEvents_mono ?_), ?_⟩
  · intro j hj
    have hjm : j.natAbs ≤ I.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hj
    have hp : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
    have hn : -(j.natAbs : ℤ) ≤ j := by
      have hh : -j ≤ ((-j).natAbs : ℤ) := Int.le_natAbs
      simpa only [Int.natAbs_neg, neg_neg] using (neg_le_neg hh)
    change -((I.sup Int.natAbs : ℕ) : ℤ) ≤ j ∧ j ≤ ((I.sup Int.natAbs : ℕ) : ℤ)
    omega
  · simpa only [dist_eq_norm] using hfg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertVariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal centering of Hilbert-valued square-integrable functions

The mean is the closest constant in L2. This is the variance estimate used
after conditioning on the middle and right independent random-walk blocks.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

omit [InnerProductSpace ℂ K] in
theorem hilbertConstantL2_ae (v : K) :
    hilbertConstantL2 μ v =ᵐ[μ] fun _ => v := MemLp.coeFn_toLp _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableUnitaryL2
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Isometric multiplication in L2 by a countable measurable unitary field. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X G K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem countableUnitaryL2_ae (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f : Lp K 2 μ) :
    countableUnitaryL2 U hc f =ᵐ[μ] fun x => (U (c x) : K →L[ℂ] K) (f x) :=
  MemLp.coeFn_toLp _

theorem countableUnitaryL2_norm (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f : Lp K 2 μ) : ‖countableUnitaryL2 U hc f‖ = ‖f‖ := by
  rw [countableUnitaryL2, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => Unitary.norm_map _ _)

theorem countableUnitaryL2_sub (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f g : Lp K 2 μ) :
    countableUnitaryL2 U hc (f - g) = countableUnitaryL2 U hc f - countableUnitaryL2 U hc g := by
  apply Lp.ext
  filter_upwards [countableUnitaryL2_ae U hc (f - g), countableUnitaryL2_ae U hc f,
    countableUnitaryL2_ae U hc g, Lp.coeFn_sub f g,
    Lp.coeFn_sub (countableUnitaryL2 U hc f) (countableUnitaryL2 U hc g)] with x h h₁ h₂ hs ht
  rw [h, ht, hs, Pi.sub_apply, Pi.sub_apply, h₁, h₂, map_sub]

theorem countableUnitaryL2_inv (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f : Lp K 2 μ) :
    countableUnitaryL2 (fun g => (U g)⁻¹) hc (countableUnitaryL2 U hc f) = f := by
  apply Lp.ext
  filter_upwards [countableUnitaryL2_ae (fun g => (U g)⁻¹) hc (countableUnitaryL2 U hc f),
    countableUnitaryL2_ae U hc f] with x h₁ h₂
  rw [h₁, h₂]
  exact (Unitary.linearIsometryEquiv (U (c x))).symm_apply_apply (f x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralL2Transport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The bilateral cocycle acts isometrically on L2. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

omit [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem bilateralTranslateL2_ae (k : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 k f =ᵐ[bilateralWalkLaw G] f ∘ bilateralTranslate G k :=
  Lp.coeFn_compMeasurePreserving f (bilateralTranslate_measurePreserving G k)

omit [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem bilateralTranslateL2_norm (k : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    ‖bilateralTranslateL2 k f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (bilateralTranslate_measurePreserving G k)

omit [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem bilateralTranslateL2_sub (k : ℤ) (f g : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 k (f - g) = bilateralTranslateL2 k f - bilateralTranslateL2 k g := by
  exact map_sub (Lp.compMeasurePreservingₗᵢ ℂ (bilateralTranslate G k)
    (bilateralTranslate_measurePreserving G k)) f g

theorem bilateral_l2_transport (σ : G →* unitary (K →L[ℂ] K))
    (f : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) (n : ℕ) :
    bilateralTranslateL2 n f =
      countableUnitaryL2 σ (bilateralIncrementProduct_measurable G n) f := by
  apply Lp.ext
  have hi := bilateral_transport_iterate σ ht n
  filter_upwards [bilateralTranslateL2_ae n f, hi,
    countableUnitaryL2_ae σ (bilateralIncrementProduct_measurable G n) f] with ω hx hy hz
  exact hx.trans (hy.trans hz.symm)

theorem bilateral_l2_approximation_transport (σ : G →* unitary (K →L[ℂ] K))
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) (n : ℕ) :
    ‖countableUnitaryL2 σ (bilateralIncrementProduct_measurable G n) g - bilateralTranslateL2 n g‖ ≤
      2 * ‖f - g‖ := by
  let U : Lp K 2 (bilateralWalkLaw G) → Lp K 2 (bilateralWalkLaw G) := countableUnitaryL2 σ (bilateralIncrementProduct_measurable G n)
  have he : U f = bilateralTranslateL2 n f := (bilateral_l2_transport σ f ht n).symm
  calc
    ‖U g - bilateralTranslateL2 n g‖ ≤ ‖U g - U f‖ + ‖U f - bilateralTranslateL2 n g‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖g - f‖ + ‖f - g‖ := by
      rw [← countableUnitaryL2_sub, countableUnitaryL2_norm, he,
        ← bilateralTranslateL2_sub, bilateralTranslateL2_norm]
    _ = 2 * ‖f - g‖ := by rw [norm_sub_rev g f]; ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryCoordinateFunctions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Unitary multiplication preserves the specified coordinate sigma algebra. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X G K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem countableUnitaryAction_aestronglyMeasurable_sigma
    {m : MeasurableSpace X} (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable[m] c) {f : X → K} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => (U (c x) : K →L[ℂ] K) (f x)) μ := by
  borelize K
  have hm : Measurable (fun p : G × K => (U p.1 : K →L[ℂ] K) p.2) :=
    measurable_from_prod_countable_right (fun g => (U g : K →L[ℂ] K).continuous.measurable)
  refine ⟨fun x => (U (c x) : K →L[ℂ] K) (hf.mk f x), ?_, ?_⟩
  · exact (hm.comp (hc.prodMk hf.stronglyMeasurable_mk.measurable)).stronglyMeasurable
  · exact hf.ae_eq_mk.mono (fun x hx => congrArg (U (c x) : K →L[ℂ] K) hx)

theorem countableUnitaryL2_sigma {m : MeasurableSpace X}
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : @Measurable X G mX _ c)
    (hcm : Measurable[m] c) (f : Lp K 2 μ) (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (countableUnitaryL2 (mX := mX) (μ := μ) U hc f) μ := by
  let : MeasurableSpace X := mX
  exact (countableUnitaryAction_aestronglyMeasurable_sigma U hcm hf).congr
    (countableUnitaryL2_ae (mX := mX) (μ := μ) U hc f).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockFunctions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Measurability and independence of the two transported finite blocks. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateralBlockA_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j ≤ m}]
      (bilateralBlockA σ m g) (bilateralWalkLaw G) := by
  apply countableUnitaryL2_sigma
  · exact bilateralIncrementProduct_coordinate_measurable (m + 1) (by intro j hj; change (j : ℤ) ≤ m; omega)
  · exact hg.mono (cylinderEvents_mono (by intro j hj; exact hj.2))

theorem bilateralBlockB_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | (m : ℤ) + 2 ≤ j}]
      (bilateralBlockB σ m g) (bilateralWalkLaw G) := by
  apply countableUnitaryL2_sigma
  · exact bilateralIncrementProduct_shift_coordinate_measurable (m + 2) m
      (by intro j hj; change (m : ℤ) + 2 ≤ (j : ℤ) + (m + 2); omega)
  · have ht := bilateralTranslate_coordinate_aestronglyMeasurable (2 * m + 2 : ℤ)
      (show ∀ j ∈ bilateralSymmetricWindow m, j + (2 * m + 2 : ℤ) ∈ {j : ℤ | (m : ℤ) + 2 ≤ j} from by
        intro j hj
        change -(m : ℤ) ≤ j ∧ j ≤ m at hj
        change (m : ℤ) + 2 ≤ j + (2 * m + 2 : ℤ)
        omega) hg
    exact ht.congr (bilateralTranslateL2_ae (2 * m + 2) g).symm

variable [MeasurableSpace K] [BorelSpace K]

theorem bilateralBlock_independent_left (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    IndepFun (bilateralBlockA σ m g)
      (fun ω => (bilateralMiddleWord G m ω, bilateralBlockB σ m g ω)) (bilateralWalkLaw G) := by
  have ha := bilateralBlockA_coordinate σ m g hg
  have hb := (bilateralBlockB_coordinate σ m g hg).mono
    (cylinderEvents_mono (show {j : ℤ | (m : ℤ) + 2 ≤ j} ⊆ {j : ℤ | (m : ℤ) < j} from by
      intro j hj; change (m : ℤ) + 2 ≤ j at hj; change (m : ℤ) < j; omega))
  have hp : Measurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | (m : ℤ) < j}]
      (bilateralMiddleWord G m) :=
    (measurable_of_countable (Inv.inv : G → G)).comp (measurable_cylinderEvent_apply (by
      change (m : ℤ) < ((m + 1 : ℕ) : ℤ); omega))
  have hd : Disjoint {j : ℤ | j ≤ m} {j : ℤ | (m : ℤ) < j} := by
    apply Set.disjoint_left.mpr
    intro j hj hk
    change j ≤ (m : ℤ) at hj
    change (m : ℤ) < j at hk
    omega
  refine bilateralCoordinate_indepFun hd ha.stronglyMeasurable_mk.measurable
    (hp.prodMk hb.stronglyMeasurable_mk.measurable) ha.ae_eq_mk ?_
  exact hb.ae_eq_mk.mono (fun ω hω => Prod.ext rfl hω)

theorem bilateralBlock_independent_right (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    IndepFun (bilateralBlockB σ m g)
      (fun ω => (bilateralMiddleWord G m ω, bilateralBlockA σ m g ω)) (bilateralWalkLaw G) := by
  have hb := bilateralBlockB_coordinate σ m g hg
  have ha := (bilateralBlockA_coordinate σ m g hg).mono
    (cylinderEvents_mono (show {j : ℤ | j ≤ m} ⊆ {j : ℤ | j ≤ (m : ℤ) + 1} from by
      intro j hj; change j ≤ (m : ℤ) at hj; change j ≤ (m : ℤ) + 1; omega))
  have hp : Measurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j ≤ (m : ℤ) + 1}]
      (bilateralMiddleWord G m) :=
    (measurable_of_countable (Inv.inv : G → G)).comp (measurable_cylinderEvent_apply (by
      change ((m + 1 : ℕ) : ℤ) ≤ (m : ℤ) + 1; omega))
  have hd : Disjoint {j : ℤ | (m : ℤ) + 2 ≤ j} {j : ℤ | j ≤ (m : ℤ) + 1} := by
    apply Set.disjoint_left.mpr
    intro j hj hk
    change (m : ℤ) + 2 ≤ j at hj
    change j ≤ (m : ℤ) + 1 at hk
    omega
  refine bilateralCoordinate_indepFun hd hb.stronglyMeasurable_mk.measurable
    (hp.prodMk ha.stronglyMeasurable_mk.measurable) hb.ae_eq_mk ?_
  exact ha.ae_eq_mk.mono (fun ω hω => Prod.ext rfl hω)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IndependentL2Variance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! An independent random vector cannot improve the constant L2 approximation. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {X K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [TopologicalSpace.SeparableSpace K]

omit [TopologicalSpace.SeparableSpace K] in
theorem independent_L2_inner (f g : Lp K 2 μ) (hfg : IndepFun f g μ) :
    inner ℝ f g = inner ℝ (∫ x, f x ∂μ) (∫ x, g x ∂μ) := by
  rw [L2.inner_def]
  exact hfg.integral_bilin ((Lp.memLp f).integrable (by norm_num))
    ((Lp.memLp g).integrable (by norm_num)) (innerSL ℝ)

theorem independent_L2_centering_le (f g : Lp K 2 μ) (hfg : IndepFun f g μ) :
    ‖f - hilbertConstantL2 μ (∫ x, f x ∂μ)‖ ≤ ‖f - g‖ := by
  let a := hilbertConstantL2 μ (∫ x, f x ∂μ)
  have ha : a =ᵐ[μ] fun _ => ∫ x, f x ∂μ := hilbertConstantL2_ae _
  have haf : (f - a : Lp K 2 μ) =ᵐ[μ] fun x => f x - ∫ x, f x ∂μ := by
    filter_upwards [Lp.coeFn_sub f a, ha] with x hx hax
    rw [hx, Pi.sub_apply, hax]
  have hag : (g - a : Lp K 2 μ) =ᵐ[μ] fun x => g x - ∫ x, f x ∂μ := by
    filter_upwards [Lp.coeFn_sub g a, ha] with x hx hax
    rw [hx, Pi.sub_apply, hax]
  have hsub : IndepFun (f - a : Lp K 2 μ) (g - a : Lp K 2 μ) μ :=
    (hfg.comp (measurable_id.sub measurable_const) (measurable_id.sub measurable_const)).congr
      haf.symm hag.symm
  have hmean : ∫ x, (f - a : Lp K 2 μ) x ∂μ = 0 := by
    rw [integral_congr_ae haf, integral_sub ((Lp.memLp f).integrable (by norm_num))
      (integrable_const _)]
    simp
  have hi : inner ℝ (f - a) (g - a) = 0 := by
    rw [independent_L2_inner _ _ hsub, hmean, inner_zero_left]
  have hn := norm_sub_sq_real (f - a) (g - a)
  have he : (f - a) - (g - a) = f - g := by abel
  rw [he, hi, mul_zero, sub_zero] at hn
  change ‖f - a‖ ≤ ‖f - g‖
  nlinarith [sq_nonneg ‖g - a‖, norm_nonneg (f - a), norm_nonneg (f - g)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IndependentUnitaryVariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Variance bounds for independently separated unitary transport blocks. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable {X G K : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K] [MeasurableSpace K] [BorelSpace K]

omit [IsProbabilityMeasure μ] [MeasurableSpace K] [BorelSpace K] in
theorem countableUnitaryL2_forward_inverse
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c) (B : Lp K 2 μ) :
    countableUnitaryL2 U hc (countableUnitaryL2 (fun g => (U g)⁻¹) hc B) = B := by
  apply Lp.ext
  filter_upwards [countableUnitaryL2_ae U hc (countableUnitaryL2 (fun g => (U g)⁻¹) hc B),
    countableUnitaryL2_ae (fun g => (U g)⁻¹) hc B] with x h₁ h₂
  rw [h₁, h₂]
  exact (Unitary.linearIsometryEquiv (U (c x))).apply_symm_apply (B x)

omit [IsProbabilityMeasure μ] in
theorem independent_unitary_inverse_independent
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (A B : Lp K 2 μ) (hi : IndepFun A (fun x => (c x, B x)) μ) :
    IndepFun A (countableUnitaryL2 (fun g => (U g)⁻¹) hc B) μ := by
  let T : G × K → K := fun p => (((U p.1)⁻¹ : unitary (K →L[ℂ] K)) : K →L[ℂ] K) p.2
  have hm : Measurable T := measurable_from_prod_countable_right
    (fun g => (((U g)⁻¹ : unitary (K →L[ℂ] K)) : K →L[ℂ] K).continuous.measurable)
  have hraw : IndepFun (fun x => A x) (fun x => T (c x, B x)) μ := hi.comp measurable_id hm
  have hae : (countableUnitaryL2 (fun g => (U g)⁻¹) hc B : X → K) =ᵐ[μ]
      (fun x => T (c x, B x)) := countableUnitaryL2_ae (fun g => (U g)⁻¹) hc B
  exact hraw.congr Filter.EventuallyEq.rfl hae.symm

theorem independent_unitary_variance_left
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (A B : Lp K 2 μ) (hi : IndepFun A (fun x => (c x, B x)) μ) :
    ‖A - hilbertConstantL2 μ (∫ x, A x ∂μ)‖ ≤ ‖countableUnitaryL2 U hc A - B‖ := by
  let C := countableUnitaryL2 (fun g => (U g)⁻¹) hc B
  have hAC : IndepFun A C μ := independent_unitary_inverse_independent U hc A B hi
  have hC : countableUnitaryL2 U hc C = B := countableUnitaryL2_forward_inverse U hc B
  let : InnerProductSpace ℝ K := InnerProductSpace.complexToReal
  calc
    ‖A - hilbertConstantL2 μ (∫ x, A x ∂μ)‖ ≤ ‖A - C‖ := independent_L2_centering_le A C hAC
    _ = ‖countableUnitaryL2 U hc (A - C)‖ := (countableUnitaryL2_norm U hc _).symm
    _ = ‖countableUnitaryL2 U hc A - B‖ := by rw [countableUnitaryL2_sub, hC]

theorem independent_unitary_variance_right
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (A B : Lp K 2 μ) (hi : IndepFun B (fun x => (c x, A x)) μ) :
    ‖B - hilbertConstantL2 μ (∫ x, B x ∂μ)‖ ≤ ‖countableUnitaryL2 U hc A - B‖ := by
  have h := independent_unitary_variance_left (fun g => (U g)⁻¹) hc B A hi
  have hnorm : ‖countableUnitaryL2 (fun g => (U g)⁻¹) hc B - A‖ =
      ‖countableUnitaryL2 U hc A - B‖ := by
    rw [← countableUnitaryL2_norm U hc, countableUnitaryL2_sub]
    have hB : countableUnitaryL2 U hc (countableUnitaryL2 (fun g => (U g)⁻¹) hc B) = B := by
      exact countableUnitaryL2_forward_inverse U hc B
    rw [hB, norm_sub_rev]
  exact h.trans_eq hnorm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockEstimates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The quantitative independent-block estimate for the bilateral cocycle. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateralBlock_collapse (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) :
    countableUnitaryL2 σ (bilateralRightWord_measurable G m)
      (countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g)) =
    countableUnitaryL2 σ (bilateralIncrementProduct_measurable G (2 * m + 2)) g := by
  apply Lp.ext
  have hA := countableUnitaryL2_ae σ (bilateralLeftWord_measurable G m) g
  filter_upwards [countableUnitaryL2_ae σ (bilateralRightWord_measurable G m)
    (countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g)),
    countableUnitaryL2_ae σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g),
    hA, countableUnitaryL2_ae σ (bilateralIncrementProduct_measurable G (2 * m + 2)) g]
      with ω hR hP hQ hW
  rw [hR, hP]
  change _ = _ at hQ
  change _ = (σ _ : K →L[ℂ] K) (g ω) at hW
  change (bilateralBlockA σ m g) ω = (σ _ : K →L[ℂ] K) (g ω) at hQ
  rw [hQ, hW, bilateral_block_word_factorization, map_mul, map_mul]
  rfl

theorem bilateralBlock_error (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) :
    ‖countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g) -
      bilateralBlockB σ m g‖ ≤ 2 * ‖f - g‖ := by
  have hB : countableUnitaryL2 σ (bilateralRightWord_measurable G m) (bilateralBlockB σ m g) =
      bilateralTranslateL2 (2 * m + 2) g := countableUnitaryL2_forward_inverse σ _ _
  calc
    _ = ‖countableUnitaryL2 σ (bilateralRightWord_measurable G m)
        (countableUnitaryL2 σ (bilateralMiddleWord_measurable G m) (bilateralBlockA σ m g) -
          bilateralBlockB σ m g)‖ := (countableUnitaryL2_norm σ _ _).symm
    _ = ‖countableUnitaryL2 σ (bilateralIncrementProduct_measurable G (2 * m + 2)) g -
        bilateralTranslateL2 (2 * m + 2) g‖ := by
      rw [countableUnitaryL2_sub, bilateralBlock_collapse, hB]
    _ ≤ 2 * ‖f - g‖ := bilateral_l2_approximation_transport σ f g ht _

theorem bilateralBlock_centering (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    ‖bilateralBlockA σ m g - hilbertConstantL2 (bilateralWalkLaw G)
        (∫ ω, bilateralBlockA σ m g ω ∂bilateralWalkLaw G)‖ ≤ 2 * ‖f - g‖ ∧
    ‖bilateralBlockB σ m g - hilbertConstantL2 (bilateralWalkLaw G)
        (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G)‖ ≤ 2 * ‖f - g‖ := by
  borelize K
  have herror := bilateralBlock_error σ m f g ht
  constructor
  · exact (independent_unitary_variance_left σ (bilateralMiddleWord_measurable G m)
      (bilateralBlockA σ m g) (bilateralBlockB σ m g)
      (bilateralBlock_independent_left σ m g hg)).trans herror
  · exact (independent_unitary_variance_right σ (bilateralMiddleWord_measurable G m)
      (bilateralBlockA σ m g) (bilateralBlockB σ m g)
      (bilateralBlock_independent_right σ m g hg)).trans herror

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralTranslateInverse
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Composition and inverse identities for the bilateral L2 shifts. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K]

theorem bilateralTranslateL2_zero (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 0 f = f := by
  apply Lp.ext
  have h := bilateralTranslateL2_ae 0 f
  have hzero : bilateralTranslate G 0 = id := by funext ω j; simp [bilateralTranslate]
  simpa only [hzero, Function.comp_id] using h

theorem bilateralTranslateL2_add (a b : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 a (bilateralTranslateL2 b f) = bilateralTranslateL2 (a + b) f := by
  apply Lp.ext
  have hb := (bilateralTranslate_measurePreserving G a).quasiMeasurePreserving.ae
    (bilateralTranslateL2_ae b f)
  filter_upwards [bilateralTranslateL2_ae a (bilateralTranslateL2 b f), hb,
    bilateralTranslateL2_ae (a + b) f] with ω h₁ h₂ h₃
  dsimp only [Function.comp_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃, bilateralTranslate_add, add_comm b a]

theorem bilateralTranslateL2_inverse (a : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 a (bilateralTranslateL2 (-a) f) = f := by
  rw [bilateralTranslateL2_add, add_neg_cancel, bilateralTranslateL2_zero]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralBlockApproximations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Positive- and negative-coordinate approximations to invariant coefficients. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

omit [InnerProductSpace ℂ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K] in
theorem hilbertConstantL2_coordinate (I : Set ℤ) (v : K) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) I]
      (hilbertConstantL2 (bilateralWalkLaw G) v) (bilateralWalkLaw G) :=
  aestronglyMeasurable_const.congr (hilbertConstantL2_ae v).symm

theorem bilateralPositiveApprox_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | 0 ≤ j}]
      (bilateralPositiveApprox σ m g) (bilateralWalkLaw G) := by
  apply countableUnitaryL2_sigma
  · exact bilateralIncrementProduct_coordinate_measurable (m + 1)
      (by intro j _; change 0 ≤ (j : ℤ); omega)
  · exact hilbertConstantL2_coordinate _ _

theorem bilateralNegativeApprox_coordinate (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (g : Lp K 2 (bilateralWalkLaw G)) :
    AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j < 0}]
      (bilateralNegativeApprox σ m g) (bilateralWalkLaw G) := by
  have hR : Measurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j < 2 * (m : ℤ) + 2}]
      (bilateralRightWord G m) :=
    bilateralIncrementProduct_shift_coordinate_measurable (m + 2) m
      (by intro j hj; change (j : ℤ) + (m + 2) < 2 * (m : ℤ) + 2; omega)
  have hc := countableUnitaryL2_sigma σ (bilateralRightWord_measurable G m) hR
    (hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G))
    (hilbertConstantL2_coordinate _ _)
  have ht := bilateralTranslate_coordinate_aestronglyMeasurable (-((2 * m + 2 : ℕ) : ℤ))
    (show ∀ j ∈ {j : ℤ | j < 2 * (m : ℤ) + 2}, j + -((2 * m + 2 : ℕ) : ℤ) ∈ {j : ℤ | j < 0} from by
      intro j hj
      change j < 2 * (m : ℤ) + 2 at hj
      change j + -((2 * m + 2 : ℕ) : ℤ) < 0
      omega) hc
  exact ht.congr (bilateralTranslateL2_ae _ _).symm

theorem bilateralPositiveApprox_error (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    ‖f - bilateralPositiveApprox σ m g‖ ≤ 3 * ‖f - g‖ := by
  let a := hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockA σ m g ω ∂bilateralWalkLaw G)
  have hi : countableUnitaryL2 (fun h => (σ h)⁻¹) (bilateralLeftWord_measurable G m)
      (bilateralBlockA σ m g) = g := countableUnitaryL2_inv σ _ g
  have he : ‖g - bilateralPositiveApprox σ m g‖ = ‖bilateralBlockA σ m g - a‖ := by
    have hh := countableUnitaryL2_norm (fun h => (σ h)⁻¹) (bilateralLeftWord_measurable G m)
      (bilateralBlockA σ m g - a)
    rw [countableUnitaryL2_sub, hi] at hh
    exact hh
  calc
    _ ≤ ‖f - g‖ + ‖g - bilateralPositiveApprox σ m g‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖f - g‖ + ‖bilateralBlockA σ m g - a‖ := by rw [he]
    _ ≤ ‖f - g‖ + 2 * ‖f - g‖ := by have hc := (bilateralBlock_centering σ m f g ht hg).1; linarith
    _ = 3 * ‖f - g‖ := by ring

theorem bilateralNegativeApprox_error (σ : G →* unitary (K →L[ℂ] K)) (m : ℕ)
    (f g : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω))
    (hg : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) (bilateralSymmetricWindow m)]
      g (bilateralWalkLaw G)) :
    ‖f - bilateralNegativeApprox σ m g‖ ≤ 3 * ‖f - g‖ := by
  let b := hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, bilateralBlockB σ m g ω ∂bilateralWalkLaw G)
  let Rb := countableUnitaryL2 σ (bilateralRightWord_measurable G m) b
  have hi : countableUnitaryL2 σ (bilateralRightWord_measurable G m) (bilateralBlockB σ m g) =
      bilateralTranslateL2 (2 * m + 2) g := countableUnitaryL2_forward_inverse σ _ _
  have he : ‖bilateralTranslateL2 (2 * m + 2) g - Rb‖ = ‖bilateralBlockB σ m g - b‖ := by
    have hh := countableUnitaryL2_norm σ (bilateralRightWord_measurable G m) (bilateralBlockB σ m g - b)
    rw [countableUnitaryL2_sub, hi] at hh
    exact hh
  have hn : bilateralTranslateL2 (2 * m + 2) (bilateralNegativeApprox σ m g) = Rb :=
    bilateralTranslateL2_inverse _ _
  calc
    _ = ‖bilateralTranslateL2 (2 * m + 2) f - Rb‖ := by
      rw [← bilateralTranslateL2_norm (2 * m + 2) (f - bilateralNegativeApprox σ m g),
        bilateralTranslateL2_sub, hn]
    _ ≤ ‖bilateralTranslateL2 (2 * m + 2) f - bilateralTranslateL2 (2 * m + 2) g‖ +
        ‖bilateralTranslateL2 (2 * m + 2) g - Rb‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖f - g‖ + ‖bilateralBlockB σ m g - b‖ := by
      rw [← bilateralTranslateL2_sub, bilateralTranslateL2_norm, he]
    _ ≤ ‖f - g‖ + 2 * ‖f - g‖ := by have hc := (bilateralBlock_centering σ m f g ht hg).2; linarith
    _ = 3 * ‖f - g‖ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralHalfSpaces
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Closed coordinate subspaces and their constant intersection. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup K] [CompleteSpace K]

theorem aestronglyMeasurable_of_L2_approximations {m : MeasurableSpace X} (hm : m ≤ mX)
    (f : Lp K 2 μ)
    (happrox : ∀ ε > (0 : ℝ), ∃ g : Lp K 2 μ, AEStronglyMeasurable[m] g μ ∧ dist f g < ε) :
    AEStronglyMeasurable[m] f μ := by
  have hc : IsClosed {g : Lp K 2 μ | AEStronglyMeasurable[m] g μ} :=
    isClosed_aestronglyMeasurable hm
  exact hc.closure_subset (Metric.mem_closure_iff.mpr happrox)

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [InnerProductSpace ℂ K] [TopologicalSpace.SeparableSpace K]

theorem bilateral_L2_constant_of_half_measurable (f : Lp K 2 (bilateralWalkLaw G))
    (hp : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | 0 ≤ j}]
      f (bilateralWalkLaw G))
    (hn : AEStronglyMeasurable[cylinderEvents (X := fun _ : ℤ => G) {j : ℤ | j < 0}]
      f (bilateralWalkLaw G)) :
    f = hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, f ω ∂bilateralWalkLaw G) := by
  borelize K
  have hd : Disjoint {j : ℤ | 0 ≤ j} {j : ℤ | j < 0} := by
    apply Set.disjoint_left.mpr
    intro j hp hn
    change 0 ≤ j at hp
    change j < 0 at hn
    omega
  have hi := bilateralCoordinate_indepFun hd hp.stronglyMeasurable_mk.measurable
    hn.stronglyMeasurable_mk.measurable hp.ae_eq_mk hn.ae_eq_mk
  let : InnerProductSpace ℝ K := InnerProductSpace.complexToReal
  have h := independent_L2_centering_le f f hi
  rw [sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BilateralTwistedErgodicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Unitary-cocycle invariant L2 functions on the bilateral walk are constant. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem bilateral_twisted_invariant_constant (σ : G →* unitary (K →L[ℂ] K))
    (f : Lp K 2 (bilateralWalkLaw G))
    (ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      f (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (f ω)) :
    f = hilbertConstantL2 (bilateralWalkLaw G) (∫ ω, f ω ∂bilateralWalkLaw G) := by
  apply bilateral_L2_constant_of_half_measurable
  · apply aestronglyMeasurable_of_L2_approximations cylinderEvents_le_pi
    intro ε hε
    obtain ⟨m, g, hg, hfg⟩ := exists_symmetricWindow_L2_approximation f (by positivity : 0 < ε / 4)
    refine ⟨bilateralPositiveApprox σ m g, bilateralPositiveApprox_coordinate σ m g, ?_⟩
    rw [dist_eq_norm]
    have he := bilateralPositiveApprox_error σ m f g ht hg
    linarith
  · apply aestronglyMeasurable_of_L2_approximations cylinderEvents_le_pi
    intro ε hε
    obtain ⟨m, g, hg, hfg⟩ := exists_symmetricWindow_L2_approximation f (by positivity : 0 < ε / 4)
    refine ⟨bilateralNegativeApprox σ m g, bilateralNegativeApprox_coordinate σ m g, ?_⟩
    rw [dist_eq_norm]
    have he := bilateralNegativeApprox_error σ m f g ht hg
    linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomWalkDoubleErgodicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The exact unitary double-ergodicity property of the constructed boundary.

This is the bounded unitary-coefficient specialization of the Poisson-boundary
result cited in `PublishedBoundary`, proved by the bilateral independent-block
argument of manuscript Section 4.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem randomWalkUnitaryDoubleErgodic : UnitaryDoubleErgodic (randomWalkBoundaryAction G) := by
  intro K _ _ _ _ σ f hf hbound heq
  borelize K
  let F₀ : BilateralWalkPath G → K := f ∘ bilateralBoundaryPair G
  have hp := bilateralBoundaryPair_measurePreserving G
  have hm : AEStronglyMeasurable F₀ (bilateralWalkLaw G) := hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  obtain ⟨C, hC⟩ := hbound
  have hmem : MemLp F₀ 2 (bilateralWalkLaw G) := MemLp.of_bound hm C (hp.quasiMeasurePreserving.ae hC)
  let F : Lp K 2 (bilateralWalkLaw G) := hmem.toLp F₀
  have hF : (F : BilateralWalkPath G → K) =ᵐ[bilateralWalkLaw G] F₀ := hmem.coeFn_toLp
  have ht₀ := bilateral_equivariant_function_transport σ hf heq
  have ht : ∀ᵐ ω ∂bilateralWalkLaw G,
      F (bilateralTranslate G 1 ω) = (σ (ω 0)⁻¹ : K →L[ℂ] K) (F ω) := by
    have hs := (bilateralTranslate_measurePreserving G 1).quasiMeasurePreserving.ae hF
    filter_upwards [hF, hs, ht₀] with ω hx hs ht
    exact hs.trans (ht.trans (congrArg (σ (ω 0)⁻¹ : K →L[ℂ] K) hx.symm))
  let v := ∫ ω, F ω ∂bilateralWalkLaw G
  have hconst := bilateral_twisted_invariant_constant σ F ht
  have hFv : (F : BilateralWalkPath G → K) =ᵐ[bilateralWalkLaw G] fun _ => v := by
    have he : (F : BilateralWalkPath G → K) = (hilbertConstantL2 (bilateralWalkLaw G) v : BilateralWalkPath G → K) :=
      congrArg (fun h : Lp K 2 (bilateralWalkLaw G) => (h : BilateralWalkPath G → K)) hconst
    exact (Filter.EventuallyEq.of_eq he).trans (hilbertConstantL2_ae v)
  have hfv : f =ᵐ[(randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)] fun _ => v := by
    have hraw : F₀ =ᵐ[bilateralWalkLaw G] fun _ => v := hF.symm.trans hFv
    have hbad : NullMeasurableSet {z | f z ≠ v}
        ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)) :=
      (nullMeasurableSet_eq_fun hf.aemeasurable (aemeasurable_const (b := v))).compl
    rw [Filter.EventuallyEq, ae_iff, ← hp.measure_preimage hbad]
    exact ae_iff.mp hraw
  exact ⟨v, (randomWalkBoundaryAction G).diagonal.fixed_of_ae_constant
    (fun g x => (σ g : K →L[ℂ] K) x) f v hfv heq, hfv⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary means and double ergodicity

The fully supported symmetric random-walk law supplies scalar means
and unitary double ergodicity.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

universe u

theorem publishedBoundary_oai : PublishedBoundary.{u} := by
  intro G _ _ _ _
  let : MeasurableSpace G := ⊤
  let : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  exact ⟨RandomWalkBoundary G, inferInstance, randomWalkBoundaryMeasure G, inferInstance,
    randomWalkBoundaryAction G, ⟨randomWalkScalarBoundaryMean G⟩,
    ⟨randomWalkProductScalarMean G⟩, randomWalkUnitaryDoubleErgodic G⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.publishedBoundary_oai.{u} := @OAI.KadisonKastler.publishedBoundary_oai.{u}
