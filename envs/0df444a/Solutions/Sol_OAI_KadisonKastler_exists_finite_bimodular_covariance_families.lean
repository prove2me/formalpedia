-- Prove2me | solution 1 for OAI.KadisonKastler.exists_finite_bimodular_covariance_families
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:10:19.904218+00:00
-- url     : https://prove2.me/submissions/a69c0c10-6823-4e4e-9fe7-8310c741b7cc

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_trace_scalar_mem_relativeOrbit_hull

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite averages of unitary conjugations -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {G : Type*} [Fintype G] [Nonempty G]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem norm_finiteAverage_le (f : G → V) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) :
    ‖finiteAverage f‖ ≤ C := by
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  calc
    _ = (Fintype.card G : ℝ)⁻¹ * ‖∑ g, f g‖ := by
      simp [finiteAverage, norm_smul, norm_inv]
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖f g‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _ : G, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun g _ => hf g)) (inv_nonneg.mpr hn.le)
    _ = C := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BalancedOrbitFamilies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Balanced two-sided unitary orbit families

Independent equal-weight left and right conjugation averages control the
respective covariances of the Cartesian-product orbit family. Its common
pairing is unchanged by an operator commuting with both unitary actions.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A I J : Type*} [CStarAlgebra A]
  [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

private theorem twoSidedUnitary_left_square (u v : unitary A) (a : A) :
    ((u : A) * a * (v : A)) * star ((u : A) * a * (v : A)) =
      (u : A) * (a * star a) * star (u : A) := by
  calc
    _ = ((u : A) * a) * ((v : A) * star (v : A)) * (star a * star (u : A)) := by
      simp only [star_mul]
      noncomm_ring
    _ = _ := by rw [Unitary.mul_star_self_of_mem v.property]; simp [mul_assoc]

private theorem twoSidedUnitary_right_square (u v : unitary A) (a : A) :
    star ((u : A) * a * (v : A)) * ((u : A) * a * (v : A)) =
      star (v : A) * (star a * a) * (v : A) := by
  calc
    _ = (star (v : A) * star a) * (star (u : A) * (u : A)) * (a * (v : A)) := by
      simp only [star_mul]
      noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem u.property]; simp [mul_assoc]

omit [Nonempty I] in
private theorem finiteAverage_product_fst (f : I → A) :
    finiteAverage (fun ij : I × J => f ij.1) = finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    ← Finset.smul_sum, smul_smul]
  congr 1
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  calc
    _ = (Fintype.card I : ℂ)⁻¹ * ((Fintype.card J : ℂ)⁻¹ * Fintype.card J) := by ring
    _ = _ := by simp [Fintype.card_ne_zero]

omit [Nonempty J] in
private theorem finiteAverage_product_snd (f : J → A) :
    finiteAverage (fun ij : I × J => f ij.2) = finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  simp [Fintype.card_prod, mul_inv_rev, Fintype.card_ne_zero]

private theorem finiteSignLeftCovariance_eq_finiteAverage {K : Type*} [Fintype K]
    (a : K → A) :
    finiteSignLeftCovariance a = finiteAverage (fun k => a k * star (a k)) := by
  simp only [finiteSignLeftCovariance, finiteAverage, ← Complex.coe_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

private theorem finiteSignRightCovariance_eq_finiteAverage {K : Type*} [Fintype K]
    (a : K → A) :
    finiteSignRightCovariance a = finiteAverage (fun k => star (a k) * a k) := by
  simp only [finiteSignRightCovariance, finiteAverage, ← Complex.coe_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

omit [Nonempty I] in
/-- The right randomization disappears from the left covariance. -/
theorem twoSidedOrbit_left_covariance (d : I → unitary A) (e : J → unitary A) (a : A) :
    finiteSignLeftCovariance (twoSidedOrbit d e a) =
      finiteAverage (fun i => (d i : A) * (a * star a) * star (d i : A)) := by
  rw [finiteSignLeftCovariance_eq_finiteAverage]
  have hp : (fun ij : I × J => twoSidedOrbit d e a ij * star (twoSidedOrbit d e a ij)) =
      fun ij : I × J => (d ij.1 : A) * (a * star a) * star (d ij.1 : A) := by
    funext ij
    exact twoSidedUnitary_left_square _ _ _
  rw [hp]
  exact finiteAverage_product_fst (A := A) (I := I) (J := J)
    (fun i => (d i : A) * (a * star a) * star (d i : A))

omit [Nonempty J] in
/-- The left randomization disappears from the right covariance. -/
theorem twoSidedOrbit_right_covariance (d : I → unitary A) (e : J → unitary A) (a : A) :
    finiteSignRightCovariance (twoSidedOrbit d e a) =
      finiteAverage (fun j => star (e j : A) * (star a * a) * (e j : A)) := by
  rw [finiteSignRightCovariance_eq_finiteAverage]
  have hp : (fun ij : I × J => star (twoSidedOrbit d e a ij) * twoSidedOrbit d e a ij) =
      fun ij : I × J => star (e ij.2 : A) * (star a * a) * (e ij.2 : A) := by
    funext ij
    exact twoSidedUnitary_right_square _ _ _
  rw [hp]
  exact finiteAverage_product_snd (A := A) (I := I) (J := J)
    (fun j => star (e j : A) * (star a * a) * (e j : A))

omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Each two-sided orbit point has exactly the original tracial two-norm. -/
theorem twoSidedOrbit_twoNorm (τ : FaithfulTracialState A)
    (d : I → unitary A) (e : J → unitary A) (a : A) (ij : I × J) :
    traceTwoNorm τ (twoSidedOrbit d e a ij) = traceTwoNorm τ a := by
  simp only [twoSidedOrbit, traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commutation lets a common unitary action pass through a pairing. -/
private theorem pairing_unitary_of_commute (V : H →L[ℂ] H)
    (u : unitary (H →L[ℂ] H)) (hu : Commute V (u : H →L[ℂ] H)) (x y : H) :
    inner ℂ (V ((u : H →L[ℂ] H) x)) ((u : H →L[ℂ] H) y) = inner ℂ (V x) y := by
  have he := congrArg (fun T : H →L[ℂ] H => T x) hu.eq
  change V ((u : H →L[ℂ] H) x) = (u : H →L[ℂ] H) (V x) at he
  rw [he]
  exact Unitary.inner_map_map u _ _

omit [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- A bimodular operator has the same pairing at every two-sided orbit point. -/
theorem twoSidedOrbit_pairing (Φ : A →ₗ[ℂ] H) (V : H →L[ℂ] H)
    (d : I → unitary A) (e : J → unitary A)
    (L : I → unitary (H →L[ℂ] H)) (R : J → unitary (H →L[ℂ] H))
    (hL : ∀ i x, Φ ((d i : A) * x) = (L i : H →L[ℂ] H) (Φ x))
    (hR : ∀ j x, Φ (x * (e j : A)) = (R j : H →L[ℂ] H) (Φ x))
    (hVL : ∀ i, Commute V (L i : H →L[ℂ] H))
    (hVR : ∀ j, Commute V (R j : H →L[ℂ] H))
    (a b : A) (ij : I × J) :
    inner ℂ (V (Φ (twoSidedOrbit d e a ij))) (Φ (twoSidedOrbit d e b ij)) =
      inner ℂ (V (Φ a)) (Φ b) := by
  simp only [twoSidedOrbit, hR, hL]
  rw [pairing_unitary_of_commute V (R ij.2) (hVR ij.2)]
  exact pairing_unitary_of_commute V (L ij.1) (hVL ij.1) _ _

omit [Nonempty I] in
private theorem finiteSignLeftCovariance_reindex {K : Type*} [Fintype K]
    (σ : K ≃ I) (a : I → A) :
    finiteSignLeftCovariance (fun k => a (σ k)) = finiteSignLeftCovariance a := by
  unfold finiteSignLeftCovariance
  rw [Fintype.card_congr σ]
  congr 1
  exact σ.sum_comp (fun i => a i * star (a i))

omit [Nonempty I] in
private theorem finiteSignRightCovariance_reindex {K : Type*} [Fintype K]
    (σ : K ≃ I) (a : I → A) :
    finiteSignRightCovariance (fun k => a (σ k)) = finiteSignRightCovariance a := by
  unfold finiteSignRightCovariance
  rw [Fintype.card_congr σ]
  congr 1
  exact σ.sum_comp (fun i => star (a i) * a i)

/-- Separate finite averages yield exactly the finite families used by the
bounded-ball test, with an ordinary `Fin n` index. -/
theorem exists_balanced_orbit_families (τ : FaithfulTracialState A)
    (Φ : A →ₗ[ℂ] H) (V : H →L[ℂ] H)
    (d : I → unitary A) (e : J → unitary A)
    (L : I → unitary (H →L[ℂ] H)) (R : J → unitary (H →L[ℂ] H))
    (hL : ∀ i x, Φ ((d i : A) * x) = (L i : H →L[ℂ] H) (Φ x))
    (hR : ∀ j x, Φ (x * (e j : A)) = (R j : H →L[ℂ] H) (Φ x))
    (hVL : ∀ i, Commute V (L i : H →L[ℂ] H))
    (hVR : ∀ j, Commute V (R j : H →L[ℂ] H))
    (a b : A) (ha : traceTwoNorm τ a ≤ 1) (hb : traceTwoNorm τ b ≤ 1)
    (hQa : traceTwoNorm τ (finiteAverage (fun j => star (e j : A) * (star a * a) * (e j : A))) ≤ 2)
    (hLa : traceTwoNorm τ (finiteAverage (fun i => (d i : A) * (a * star a) * star (d i : A))) ≤ 2)
    (hQb : traceTwoNorm τ (finiteAverage (fun j => star (e j : A) * (star b * b) * (e j : A))) ≤ 2)
    (hLb : traceTwoNorm τ (finiteAverage (fun i => (d i : A) * (b * star b) * star (d i : A))) ≤ 2) :
    ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → A,
      (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
      (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
      traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
      (∀ i, inner ℂ (V (Φ (f i))) (Φ (g i)) = inner ℂ (V (Φ a)) (Φ b)) := by
  let σ : Fin (Fintype.card (I × J)) ≃ I × J := (Fintype.equivFin (I × J)).symm
  let f : Fin (Fintype.card (I × J)) → A := fun i => twoSidedOrbit d e a (σ i)
  let g : Fin (Fintype.card (I × J)) → A := fun i => twoSidedOrbit d e b (σ i)
  refine ⟨Fintype.card (I × J), Fintype.card_pos, f, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (twoSidedOrbit_twoNorm τ d e a (σ i)).le.trans ha
  · intro i
    exact (twoSidedOrbit_twoNorm τ d e b (σ i)).le.trans hb
  · change traceTwoNorm τ (finiteSignRightCovariance (fun i => twoSidedOrbit d e a (σ i))) ≤ 2
    rw [finiteSignRightCovariance_reindex, twoSidedOrbit_right_covariance]
    exact hQa
  · change traceTwoNorm τ (finiteSignLeftCovariance (fun i => twoSidedOrbit d e a (σ i))) ≤ 2
    rw [finiteSignLeftCovariance_reindex, twoSidedOrbit_left_covariance]
    exact hLa
  · change traceTwoNorm τ (finiteSignRightCovariance (fun i => twoSidedOrbit d e b (σ i))) ≤ 2
    rw [finiteSignRightCovariance_reindex, twoSidedOrbit_right_covariance]
    exact hQb
  · change traceTwoNorm τ (finiteSignLeftCovariance (fun i => twoSidedOrbit d e b (σ i))) ≤ 2
    rw [finiteSignLeftCovariance_reindex, twoSidedOrbit_left_covariance]
    exact hLb
  · intro i
    exact twoSidedOrbit_pairing Φ V d e L R hL hR hVL hVR a b (σ i)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise diagonal comparison in a finite algebra

The least-norm argument is carried out in a supplied faithful tracial
Hilbert realization. Bounded completeness of the concrete finite algebra
keeps Hilbert limits in the operator algebra. No measurable selection or
existence of a boundary space is asserted here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

section Concrete

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E)
variable (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)

/-- The definition agrees with the ordinary Hilbert closed convex hull. -/
theorem diagonalTraceHull_eq (s : Set (Algebra M)) :
    diagonalTraceHull J s = closure (convexHull ℝ (J '' s)) := by
  unfold diagonalTraceHull
  congr 1
  exact (J.restrictScalars ℝ).image_convexHull s

end Concrete


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_EqualWeightAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equal-weight approximation of closed convex hulls

Natural multiplicities approximate any finite convex combination: round
scaled weights down, normalize their total, and repeat the corresponding
points. No compactness or dimension restriction on the normed space is used.
-/

namespace KadisonKastler

open Filter Set
open scoped BigOperators Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A natural-weight mean is literally an equal-weight mean with repetitions. -/
theorem exists_equalWeightAverage_of_natWeights {ι : Type*} [Fintype ι]
    (c : ι → ℕ) (f : ι → E) (hc : 0 < ∑ i, c i) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Fin n → E,
      (∀ j, g j ∈ Set.range f) ∧
      (n : ℝ)⁻¹ • ∑ j, g j = ((∑ i, c i : ℕ) : ℝ)⁻¹ • ∑ i, (c i : ℝ) • f i := by
  let K := Σ i, Fin (c i)
  have hcard : Fintype.card K = ∑ i, c i := by simp [K]
  have hK : 0 < Fintype.card K := hcard.symm ▸ hc
  let σ : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K, hK, fun j => f (σ j).1, ?_, ?_⟩
  · intro j
    exact ⟨(σ j).1, rfl⟩
  · have hsum : (∑ j : Fin (Fintype.card K), f (σ j).1) =
        ∑ i, (c i : ℝ) • f i := by
      calc
        _ = ∑ k : K, f k.1 := σ.sum_comp (fun k : K => f k.1)
        _ = _ := by
          rw [Fintype.sum_sigma]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.cast_smul_eq_nsmul ℝ]
    rw [hsum, hcard]

private theorem rounded_mean_eq {ι : Type*} [Fintype ι]
    (c : ι → ℕ) (f : ι → E) {t : ℝ} (ht : t ≠ 0) (hc : 0 < ∑ i, c i) :
    (∑ i, (c i : ℝ) / t)⁻¹ • ∑ i, ((c i : ℝ) / t) • f i =
      ((∑ i, c i : ℕ) : ℝ)⁻¹ • ∑ i, (c i : ℝ) • f i := by
  have hsum : (∑ i, (c i : ℝ) / t) = ((∑ i, c i : ℕ) : ℝ) / t := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]
  have hnum : (∑ i, ((c i : ℝ) / t) • f i) =
      t⁻¹ • ∑ i, (c i : ℝ) • f i := by
    simp only [Finset.smul_sum, smul_smul, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [hsum, hnum, smul_smul]
  congr 1
  have hc0 : (((∑ i, c i : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  field_simp

/-- Finite convex combinations can be approximated by means with repeated points. -/
theorem exists_equalWeightAverage_of_convexCombination {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (f : ι → E) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Fin n → E,
      (∀ j, g j ∈ Set.range f) ∧
      ‖(n : ℝ)⁻¹ • ∑ j, g j - ∑ i, w i • f i‖ < ε := by
  let c (t : ℝ) (i : ι) : ℕ := ⌊w i * t⌋₊
  let r (t : ℝ) (i : ι) : ℝ := (c t i : ℝ) / t
  have hr (i : ι) : Tendsto (fun t : ℝ => r t i) atTop (𝓝 (w i)) :=
    tendsto_nat_floor_mul_div_atTop (hw i)
  have hs : Tendsto (fun t : ℝ => ∑ i, r t i) atTop (𝓝 1) := by
    simpa only [hw1] using tendsto_finsetSum Finset.univ (fun i _ => hr i)
  have hf : Tendsto (fun t : ℝ => ∑ i, r t i • f i) atTop (𝓝 (∑ i, w i • f i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => (hr i).smul tendsto_const_nhds)
  have hv : Tendsto (fun t : ℝ => (∑ i, r t i)⁻¹ • ∑ i, r t i • f i)
      atTop (𝓝 (∑ i, w i • f i)) := by
    simpa only [inv_one, one_smul] using (hs.inv₀ (by norm_num)).smul hf
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < ∑ i, r t i :=
    hs.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hnear := (Metric.tendsto_nhds.mp hv) ε hε
  obtain ⟨t, ht, hcpos, hclose⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hpos.and hnear)).exists
  have hcount : 0 < ∑ i, c t i := by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    have he : (∑ i, r t i) = 0 := by
      change (∑ i, (c t i : ℝ) / t) = 0
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hz]
      simp
    linarith
  obtain ⟨n, hn, g, hg, heq⟩ := exists_equalWeightAverage_of_natWeights (c t) f hcount
  refine ⟨n, hn, g, hg, ?_⟩
  rw [heq, ← rounded_mean_eq (c t) f ht.ne' hcount]
  change ‖(∑ i, r t i)⁻¹ • ∑ i, r t i • f i - ∑ i, w i • f i‖ < ε
  simpa only [dist_eq_norm] using hclose

/-- Equal-weight means of points of a set are dense in its convex hull. -/
theorem exists_equalWeightAverage_of_mem_convexHull {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin n → E,
      (∀ i, f i ∈ S) ∧ ‖(n : ℝ)⁻¹ • ∑ i, f i - z‖ < ε := by
  obtain ⟨ι, hι, w, f, hw, hw1, hf, heq⟩ := mem_convexHull_iff_exists_fintype.mp hz
  let : Fintype ι := hι
  obtain ⟨n, hn, g, hg, hclose⟩ :=
    exists_equalWeightAverage_of_convexCombination w f hw hw1 hε
  refine ⟨n, hn, g, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hg i
    exact hj ▸ hf j
  · simpa only [heq] using hclose

/-- Every point of the closed convex hull is approximated by a finite
nonempty equal-weight average of points of the original set. -/
theorem exists_equalWeightAverage_of_mem_closedConvexHull {S : Set E} {z : E}
    (hz : z ∈ closure (convexHull ℝ S)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Fin n → E,
      (∀ i, f i ∈ S) ∧ ‖(n : ℝ)⁻¹ • ∑ i, f i - z‖ < ε := by
  obtain ⟨x, hx, hzx⟩ := Metric.mem_closure_iff.mp hz (ε / 2) (by positivity)
  obtain ⟨n, hn, f, hf, hfx⟩ :=
    exists_equalWeightAverage_of_mem_convexHull hx (show 0 < ε / 2 by positivity)
  refine ⟨n, hn, f, hf, ?_⟩
  have hxz : ‖x - z‖ < ε / 2 := by simpa only [dist_eq_norm, norm_sub_rev] using hzx
  calc
    _ ≤ ‖(n : ℝ)⁻¹ • ∑ i, f i - x‖ + ‖x - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteRelativeAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite unitary averages approximating the scalar trace -/

namespace KadisonKastler

open Set
open scoped BigOperators

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}
  {τ : FaithfulTracialState (Algebra M)}

/-- Scalar relative averaging is realized to any positive accuracy by a
nonempty finite equal-weight family of actual unitaries. -/
theorem exists_finite_relative_scalar_average
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → unitary R,
      traceTwoNorm τ ((n : ℂ)⁻¹ • ∑ i, φ (u i) * a * star (φ (u i)) -
        τ.toLinearMap a • (1 : Algebra M)) < ε := by
  classical
  have hc := trace_scalar_mem_relativeOrbit_hull J hJ hτ φ hirr a
  rw [diagonalTraceHull_eq] at hc
  obtain ⟨n, hn, f, hf, hclose⟩ := exists_equalWeightAverage_of_mem_closedConvexHull hc hε
  have hex (i : Fin n) : ∃ u : unitary R, J (φ u * a * star (φ u)) = f i := by
    obtain ⟨x, ⟨u, rfl⟩, hx⟩ := hf i
    exact ⟨u, hx⟩
  choose u hu using hex
  refine ⟨n, hn, u, ?_⟩
  rw [← hJ, map_sub]
  have he : J ((n : ℂ)⁻¹ • ∑ i, φ (u i) * a * star (φ (u i))) =
      (n : ℝ)⁻¹ • ∑ i, f i := by
    rw [map_smul, map_sum]
    simp only [hu, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.coe_smul]
  rw [he]
  exact hclose

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_JointRelativeAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simultaneous finite relative averages

Successively averaging two elements gives one finite family controlling
both. The second average cannot increase the first element's tracial
norm; its trace preserves the scalar target for the second element.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A R E : Type*} [CStarAlgebra A] [CStarAlgebra R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem trace_relativeConjugation (τ : FaithfulTracialState A)
    (φ : R →⋆ₐ[ℂ] A) (u : unitary R) (a : A) :
    τ.toLinearMap (φ u * a * star (φ u)) = τ.toLinearMap a := by
  have hu : star (φ u) * φ u = 1 := by
    simpa only [map_mul, map_star, map_one] using
      congrArg φ (Unitary.star_mul_self_of_mem u.property)
  calc
    _ = τ.toLinearMap (φ u * (a * star (φ u))) := congrArg τ.toLinearMap (mul_assoc _ _ _)
    _ = τ.toLinearMap ((a * star (φ u)) * φ u) := τ.tracial _ _
    _ = _ := by rw [mul_assoc, hu, mul_one]

/-- Every finite relative average preserves the trace. -/
theorem trace_relativeConjugationAverage {I : Type*} [Fintype I] [Nonempty I]
    (τ : FaithfulTracialState A) (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (a : A) :
    τ.toLinearMap (relativeConjugationAverage φ u a) = τ.toLinearMap a := by
  unfold relativeConjugationAverage finiteAverage
  simp only [map_smul, map_sum, trace_relativeConjugation, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp [Fintype.card_ne_zero]

/-- A finite relative average is contractive for the tracial two-norm. -/
theorem traceTwoNorm_relativeConjugationAverage_le {I : Type*}
    [Fintype I] [Nonempty I] (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (a : A) :
    traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ traceTwoNorm τ a := by
  rw [← hJ]
  have he : J (relativeConjugationAverage φ u a) =
      finiteAverage (fun i => J (φ (u i) * a * star (φ (u i)))) := by
    simp only [relativeConjugationAverage, finiteAverage, map_smul, map_sum]
  rw [he]
  apply norm_finiteAverage_le
  intro i
  rw [hJ]
  let v : unitary A := Unitary.map (StarMonoidHom.ofClass φ) (u i)
  change traceTwoNorm τ ((v : A) * a * (star v : unitary A)) ≤ traceTwoNorm τ a
  simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  exact le_rfl

/-- The Cartesian-product family implements composition of averages. -/
theorem relativeConjugationAverage_comp {I K : Type*} [Fintype I] [Fintype K]
    (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (v : K → unitary R) (a : A) :
    relativeConjugationAverage φ (fun ki : K × I => v ki.1 * u ki.2) a =
      relativeConjugationAverage φ v (relativeConjugationAverage φ u a) := by
  have hcard : (Fintype.card (K × I) : ℂ)⁻¹ =
      (Fintype.card K : ℂ)⁻¹ * (Fintype.card I : ℂ)⁻¹ := by
    rw [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm]
  simp only [relativeConjugationAverage, finiteAverage, hcard,
    Fintype.sum_prod_type, Submonoid.coe_mul, map_mul, star_mul,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    Finset.smul_sum, smul_smul, mul_assoc]

private theorem traceTwoNorm_scalar_one (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (c : ℂ) :
    traceTwoNorm τ (c • (1 : A)) = ‖c‖ := by
  rw [← hJ, map_smul, norm_smul, hJ, traceTwoNorm_one, mul_one]

/-- Any scalar-averaging property supplies simultaneous two-norm bounds
for two trace-bounded elements. No positivity assumption is needed. -/
theorem exists_joint_relative_averages_of_scalar
    (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (φ : R →⋆ₐ[ℂ] A)
    (havg : ∀ a : A, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧
      ∃ u : Fin n → unitary R,
        traceTwoNorm τ (relativeConjugationAverage φ u a -
          τ.toLinearMap a • (1 : A)) < ε)
    (a b : A) (ha : ‖τ.toLinearMap a‖ ≤ 1) (hb : ‖τ.toLinearMap b‖ ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → unitary R,
      traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ 2 ∧
      traceTwoNorm τ (relativeConjugationAverage φ u b) ≤ 2 := by
  classical
  obtain ⟨m, hm, u, hu⟩ := havg a 1 zero_lt_one
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have ha' : traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ 2 := by
    have htriangle := traceTwoNorm_add_le τ
      (relativeConjugationAverage φ u a - τ.toLinearMap a • (1 : A))
      (τ.toLinearMap a • (1 : A))
    rw [sub_add_cancel, traceTwoNorm_scalar_one τ J hJ] at htriangle
    linarith
  obtain ⟨n, hn, v, hv⟩ := havg (relativeConjugationAverage φ u b) 1 zero_lt_one
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [trace_relativeConjugationAverage] at hv
  have hb' : traceTwoNorm τ
      (relativeConjugationAverage φ v (relativeConjugationAverage φ u b)) ≤ 2 := by
    have htriangle := traceTwoNorm_add_le τ
      (relativeConjugationAverage φ v (relativeConjugationAverage φ u b) -
        τ.toLinearMap (relativeConjugationAverage φ u b) • (1 : A))
      (τ.toLinearMap (relativeConjugationAverage φ u b) • (1 : A))
    rw [sub_add_cancel, traceTwoNorm_scalar_one τ J hJ,
      trace_relativeConjugationAverage] at htriangle
    linarith
  let K := Fin n × Fin m
  let σ : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let w : K → unitary R := fun ki => v ki.1 * u ki.2
  have he (x : A) : relativeConjugationAverage φ (fun j => w (σ j)) x =
      relativeConjugationAverage φ v (relativeConjugationAverage φ u x) := by
    calc
      _ = relativeConjugationAverage φ w x := by
        unfold relativeConjugationAverage finiteAverage
        rw [Fintype.card_congr σ]
        congr 1
        exact σ.sum_comp (fun ki => φ (w ki) * x * star (φ (w ki)))
      _ = _ := relativeConjugationAverage_comp φ u v x
  refine ⟨Fintype.card K, Fintype.card_pos, fun j => w (σ j), ?_, ?_⟩
  · rw [he]
    exact (traceTwoNorm_relativeConjugationAverage_le τ J hJ φ v _).trans ha'
  · rw [he]
    exact hb'

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CompleteSpace E] {M : VonNeumannAlgebra H}

/-- In a concrete finite factor, irreducibility supplies one actual
finite family simultaneously averaging any two trace-bounded elements. -/
theorem exists_joint_finite_relative_average
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a b : Algebra M) (ha : ‖τ.toLinearMap a‖ ≤ 1) (hb : ‖τ.toLinearMap b‖ ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → unitary R,
      traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ 2 ∧
      traceTwoNorm τ (relativeConjugationAverage φ u b) ≤ 2 := by
  apply exists_joint_relative_averages_of_scalar τ J hJ φ ?_ a b ha hb
  intro x ε hε
  simpa only [relativeConjugationAverage, finiteAverage, Fintype.card_fin] using
    exists_finite_relative_scalar_average J hJ hτ φ hirr x hε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBimodularBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded-ball tests for bimodular operators

Relative scalar averaging supplies the finite covariance families. The
left and right unitary actions then preserve their pairings, so the
proved sign-randomization and clipping estimate applies with constant 384.
-/

namespace KadisonKastler

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}

private theorem norm_trace_square_le_one {A : Type*} [CStarAlgebra A]
    (τ : FaithfulTracialState A) (a : A) (ha : traceTwoNorm τ a ≤ 1) :
    ‖τ.toLinearMap (star a * a)‖ ≤ 1 := by
  have h := τ.cauchySchwarz a a
  nlinarith [traceTwoNorm_nonneg τ a]

private theorem norm_trace_square_reverse_le_one {A : Type*} [CStarAlgebra A]
    (τ : FaithfulTracialState A) (a : A) (ha : traceTwoNorm τ a ≤ 1) :
    ‖τ.toLinearMap (a * star a)‖ ≤ 1 := by
  rw [τ.tracial a (star a)]
  exact norm_trace_square_le_one τ a ha

/-- Irreducibility and bimodularity produce the actual finite families
required for covariance testing. -/
theorem exists_finite_bimodular_covariance_families_oai
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (V : E →L[ℂ] E) (L Q : unitary R → unitary (E →L[ℂ] E))
    (hL : ∀ (u : unitary R) (x : Algebra M), J (φ u * x) = (L u : E →L[ℂ] E) (J x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), J (x * φ u) = (Q u : E →L[ℂ] E) (J x))
    (hVL : ∀ u, Commute V (L u : E →L[ℂ] E))
    (hVQ : ∀ u, Commute V (Q u : E →L[ℂ] E))
    (a b : Algebra M) (ha : traceTwoNorm τ a ≤ 1) (hb : traceTwoNorm τ b ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → Algebra M,
      (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
      (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
      traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
      (∀ i, inner ℂ (V (J (f i))) (J (g i)) = inner ℂ (V (J a)) (J b)) := by
  obtain ⟨m, hm, u, hua, hub⟩ := exists_joint_finite_relative_average τ J hJ hτ φ hirr
    (a * star a) (b * star b)
    (norm_trace_square_reverse_le_one τ a ha) (norm_trace_square_reverse_le_one τ b hb)
  obtain ⟨n, hn, v, hva, hvb⟩ := exists_joint_finite_relative_average τ J hJ hτ φ hirr
    (star a * a) (star b * b)
    (norm_trace_square_le_one τ a ha) (norm_trace_square_le_one τ b hb)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let d : Fin m → unitary (Algebra M) := fun i =>
    Unitary.map (StarMonoidHom.ofClass φ) (u i)
  let e : Fin n → unitary (Algebra M) := fun j =>
    star (Unitary.map (StarMonoidHom.ofClass φ) (v j))
  have hd : ∀ i x, J ((d i : Algebra M) * x) = (L (u i) : E →L[ℂ] E) (J x) := by
    intro i x
    exact hL (u i) x
  have he : ∀ j x, J (x * (e j : Algebra M)) =
      (Q (star (v j)) : E →L[ℂ] E) (J x) := by
    intro j x
    change J (x * star (φ (v j))) = (Q (star (v j)) : E →L[ℂ] E) (J x)
    simpa only [Unitary.coe_star, map_star] using hQ (star (v j)) x
  have hQa : traceTwoNorm τ (finiteAverage
      (fun j => star (e j : Algebra M) * (star a * a) * (e j : Algebra M))) ≤ 2 := by
    change traceTwoNorm τ (finiteAverage
      (fun j => star (star (φ (v j))) * (star a * a) * star (φ (v j)))) ≤ 2
    simpa only [relativeConjugationAverage, star_star] using hva
  have hQb : traceTwoNorm τ (finiteAverage
      (fun j => star (e j : Algebra M) * (star b * b) * (e j : Algebra M))) ≤ 2 := by
    change traceTwoNorm τ (finiteAverage
      (fun j => star (star (φ (v j))) * (star b * b) * star (φ (v j)))) ≤ 2
    simpa only [relativeConjugationAverage, star_star] using hvb
  exact exists_balanced_orbit_families τ J V d e
    (fun i => L (u i)) (fun j => Q (star (v j))) hd he
    (fun i => hVL (u i)) (fun j => hVQ (star (v j))) a b ha hb
    hQa hua hQb hub

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_finite_bimodular_covariance_families_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_finite_bimodular_covariance_families_oai.{u_1, u_2, u_3}
