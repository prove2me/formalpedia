-- Prove2me | solution 1 for OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:14:06.325159+00:00
-- url     : https://prove2.me/submissions/977a3c15-20d9-4fc3-b515-0d14d22b4447

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
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
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K005
import Definitions.Def_Q260K007
import Definitions.Def_Q260K008
import Definitions.Def_Q260K016

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Jordan
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Orientation of surjective Jordan maps

This is the algebraic argument recalled in §5 of *Universal strong
Kadison–Kastler stability* (2026), following I. N. Herstein, *Jordan
homomorphisms*, Trans. Amer. Math. Soc. 81 (1956), 331–341. The target is
assumed prime explicitly; no von Neumann algebra representation is needed
for this algebraic step.
-/

namespace KadisonKastler

variable {A B : Type*}
  [Ring A]
  [_root_.Algebra ℂ A]
  [Ring B]
  [_root_.Algebra ℂ B]

private theorem eq_of_add_self_eq_add_self {x y : B} (h : x + x = y + y) : x = y := by
  apply smul_right_injective B (two_ne_zero : (2 : ℂ) ≠ 0)
  simpa only [two_smul] using h

theorem PreservesJordan.map_square {θ : A →ₗ[ℂ] B} (hθ : PreservesJordan θ) (x : A) :
    θ (x * x) = θ x * θ x := by
  apply eq_of_add_self_eq_add_self
  simpa only [map_add] using hθ x x

theorem PreservesJordan.map_triple {θ : A →ₗ[ℂ] B} (hθ : PreservesJordan θ) (x y : A) :
    θ (x * y * x) = θ x * θ y * θ x := by
  apply eq_of_add_self_eq_add_self
  calc
    θ (x * y * x) + θ (x * y * x) = θ (x * y * x + x * y * x) := (map_add θ _ _).symm
    _ = θ ((x * (x * y + y * x) + (x * y + y * x) * x) -
        (x * x * y + y * (x * x))) := by congr 1; noncomm_ring
    _ = θ x * θ (x * y + y * x) + θ (x * y + y * x) * θ x -
        (θ (x * x) * θ y + θ y * θ (x * x)) := by
      rw [map_sub, hθ x (x * y + y * x), hθ (x * x) y]
    _ = θ x * θ y * θ x + θ x * θ y * θ x := by
      rw [hθ x y, hθ.map_square x]
      noncomm_ring

theorem PreservesJordan.map_triple_add_reverse {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (x y z : A) :
    θ (x * y * z + z * y * x) = θ x * θ y * θ z + θ z * θ y * θ x := by
  calc
    θ (x * y * z + z * y * x) =
        θ ((x + z) * y * (x + z) - x * y * x - z * y * z) := by
      congr 1; noncomm_ring
    _ = θ (x + z) * θ y * θ (x + z) - θ x * θ y * θ x - θ z * θ y * θ z := by
      rw [map_sub, map_sub, hθ.map_triple, hθ.map_triple, hθ.map_triple]
    _ = θ x * θ y * θ z + θ z * θ y * θ x := by
      rw [map_add]
      noncomm_ring

/-- The two potential multiplicative defects anticommute through every
element of the target. -/
theorem PreservesJordan.defect_relation {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ) (a b : A) (C : B) :
    (θ (a * b) - θ a * θ b) * C * (θ (a * b) - θ b * θ a) +
      (θ (a * b) - θ b * θ a) * C * (θ (a * b) - θ a * θ b) = 0 := by
  obtain ⟨c, rfl⟩ := hsurj C
  have he : θ (b * a) = θ a * θ b + θ b * θ a - θ (a * b) := by
    have h := hθ a b
    rw [map_add] at h
    linear_combination (norm := noncomm_ring) h
  have hfirst := hθ.map_triple_add_reverse (a * b) c (b * a)
  have hsource : a * b * c * (b * a) + b * a * c * (a * b) =
      a * (b * c * b) * a + b * (a * c * a) * b := by noncomm_ring
  rw [hsource, map_add, hθ.map_triple, hθ.map_triple,
    hθ.map_triple, hθ.map_triple, he] at hfirst
  linear_combination (norm := noncomm_ring) hfirst

private theorem prime_or_of_anticommutation (hprime : IsPrimeAlgebra B)
    (h k : B) (hrel : ∀ c, h * c * k + k * c * h = 0) : h = 0 ∨ k = 0 := by
  by_cases hk : k = 0
  · exact Or.inr hk
  left
  apply (hprime h k ?_).resolve_right hk
  intro c₁
  apply (hprime (h * c₁ * k) k ?_).resolve_right hk
  intro c₂
  have hzero : (h * c₁ * k * c₂ * k) + (h * c₁ * k * c₂ * k) = 0 + 0 := by
    linear_combination (norm := noncomm_ring)
      hrel (c₁ * k * c₂) + (hrel c₁) * c₂ * k - k * c₁ * (hrel c₂)
  exact eq_of_add_self_eq_add_self hzero

/-- For each pair of source elements, one of the two orientations holds. -/
theorem PreservesJordan.map_mul_or_map_mul_reverse {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (a b : A) :
    θ (a * b) = θ a * θ b ∨ θ (a * b) = θ b * θ a := by
  simpa only [sub_eq_zero] using prime_or_of_anticommutation hprime
    (θ (a * b) - θ a * θ b) (θ (a * b) - θ b * θ a)
    (hθ.defect_relation hsurj a b)

private theorem additive_zero_cover {X Y : Type*} [AddGroup X] [AddGroup Y]
    (f g : X →+ Y) (hcover : ∀ x, f x = 0 ∨ g x = 0) : f = 0 ∨ g = 0 := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    apply AddMonoidHom.ext
    intro x
    exact Classical.byContradiction (fun hx => h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hex
  have hgx : g x = 0 := (hcover x).resolve_left hx
  apply AddMonoidHom.ext
  intro y
  by_cases hgy : g y = 0
  · exact hgy
  have hfy : f y = 0 := (hcover y).resolve_right hgy
  rcases hcover (x + y) with hxy | hxy
  · rw [map_add, hfy, add_zero] at hxy
    exact False.elim (hx hxy)
  · rw [map_add, hgx, zero_add] at hxy
    exact False.elim (hgy hxy)

/-- Herstein's orientation theorem in the complex prime-target case.
A surjective complex-linear Jordan map is multiplicative or antimultiplicative.
The two applications of `additive_zero_cover` are the two additive-subgroup
union arguments in the manuscript's proof. -/
theorem PreservesJordan.multiplicative_or_antimultiplicative {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) :
    (∀ a b, θ (a * b) = θ a * θ b) ∨ (∀ a b, θ (a * b) = θ b * θ a) := by
  have hlocal (a : A) : mulDefect θ a = 0 ∨ reverseMulDefect θ a = 0 := by
    apply additive_zero_cover
    intro b
    simpa only [mulDefect, reverseMulDefect, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      sub_eq_zero] using hθ.map_mul_or_map_mul_reverse hsurj hprime a b
  rcases additive_zero_cover (mulDefect θ) (reverseMulDefect θ) hlocal with h | h
  · left
    intro a b
    have h' := congrArg (fun f : A →+ A →+ B => f a b) h
    exact sub_eq_zero.mp h'
  · right
    intro a b
    have h' := congrArg (fun f : A →+ A →+ B => f a b) h
    exact sub_eq_zero.mp h'

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Multiplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Multiplicative defects of maps close to a representation

These estimates are the normed-algebra calculation used in the UCP criterion
in §2 of *Universal strong Kadison–Kastler stability* (2026). They require no
positivity theorem: contractivity, where used, is an explicit hypothesis.
-/

namespace KadisonKastler

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]

/-- A map within `e` of an isometric representation has norm at most `1 + e`. -/
theorem norm_image_le_of_close_to_isometric_hom
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ}
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖) (x : A) :
    ‖F x‖ ≤ (1 + e) * ‖x‖ := by
  calc
    ‖F x‖ ≤ ‖F x - ρ x‖ + ‖ρ x‖ := norm_le_norm_sub_add _ _
    _ ≤ e * ‖x‖ + ‖x‖ := by rw [hρ]; exact add_le_add (hclose x) le_rfl
    _ = (1 + e) * ‖x‖ := by ring

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_JordanOrientation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Quantitative exclusion of the reversed Jordan orientation

The calculation in §5 of *Universal strong Kadison–Kastler stability*
excludes an antihomomorphism that is sufficiently close to the inclusion.
Closeness alone gives a `3e + e²` estimate; contractivity improves it to `3e`.
The applications to Jordan maps keep the embeddings in the common ambient
algebra explicit.
-/

namespace KadisonKastler

variable {A B D : Type*}
  [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]
  [NormedRing D] [NormedAlgebra ℂ D]

/-- The three error terms controlling a commutator under an
antimultiplicative map close to an isometric representation. -/
theorem commutator_norm_le_three_terms
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ}
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (hanti : ∀ x y, F (x * y) = F y * F x) (a b : A) :
    ‖a * b - b * a‖ ≤
      e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) := by
  have hexpand : ι (a * b - b * a) =
      (ι (a * b) - F (a * b)) + (F b - ι b) * F a + ι b * (F a - ι a) := by
    simp only [map_sub, map_mul, hanti]
    noncomm_ring
  calc
    ‖a * b - b * a‖ = ‖ι (a * b - b * a)‖ := (hι _).symm
    _ = ‖(ι (a * b) - F (a * b)) + (F b - ι b) * F a +
        ι b * (F a - ι a)‖ := by rw [hexpand]
    _ ≤ ‖ι (a * b) - F (a * b)‖ + ‖(F b - ι b) * F a‖ +
        ‖ι b * (F a - ι a)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using hclose (a * b)
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hclose b) (norm_nonneg _))
      · exact (norm_mul_le _ _).trans (by
          rw [hι b]
          exact mul_le_mul_of_nonneg_left (hclose a) (norm_nonneg b))

/-- Closeness alone controls an antimultiplicative map's commutators;
contractivity is not assumed. -/
theorem commutator_norm_le_of_close_antimultiplicative_without_contractivity
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ} (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (hanti : ∀ x y, F (x * y) = F y * F x) (a b : A) :
    ‖a * b - b * a‖ ≤ (3 * e + e ^ 2) * ‖a‖ * ‖b‖ := by
  calc
    ‖a * b - b * a‖ ≤
        e * ‖a * b‖ + (e * ‖b‖) * ‖F a‖ + ‖b‖ * (e * ‖a‖) :=
      commutator_norm_le_three_terms ι F hι hclose hanti a b
    _ ≤ e * (‖a‖ * ‖b‖) + (e * ‖b‖) * ((1 + e) * ‖a‖) +
        ‖b‖ * (e * ‖a‖) := by
      apply add_le_add _ le_rfl
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le a b) he)
        (mul_le_mul_of_nonneg_left (norm_image_le_of_close_to_isometric_hom ι F hι hclose a)
          (mul_nonneg he (norm_nonneg b)))
    _ = (3 * e + e ^ 2) * ‖a‖ * ‖b‖ := by ring

/-- A norm-two commutator excludes a close antihomomorphism without
contractivity, using the slightly smaller tolerance `3e + e² < 2`. -/
theorem not_antimultiplicative_of_norm_two_commutator_without_contractivity
    (ι : A →ₐ[ℂ] D) (F : A →ₗ[ℂ] D) {e : ℝ} (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖F x - ι x‖ ≤ e * ‖x‖)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ‖a * b - b * a‖ = 2) (hsmall : 3 * e + e ^ 2 < 2) :
    ¬ ∀ x y, F (x * y) = F y * F x := by
  intro hanti
  have hbound := commutator_norm_le_of_close_antimultiplicative_without_contractivity
    ι F he hι hclose hanti a b
  rw [hab, ha, hb, mul_one, mul_one] at hbound
  exact (not_le_of_gt hsmall) hbound

/-- The multiplicative orientation follows from closeness alone, with no
contractivity assumption on the Jordan map. -/
theorem PreservesJordan.multiplicative_of_close_without_contractivity
    (θ : A →ₗ[ℂ] B) (ι : A →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (a b : A) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ‖a * b - b * a‖ = 2) (hsmall : 3 * e + e ^ 2 < 2) :
    ∀ x y, θ (x * y) = θ x * θ y := by
  rcases hθ.multiplicative_or_antimultiplicative hsurj hprime with hmult | hanti
  · exact hmult
  · exfalso
    apply not_antimultiplicative_of_norm_two_commutator_without_contractivity
      ι (κ.toLinearMap.comp θ) he hι hclose a b ha hb hab hsmall
    intro x y
    change κ (θ (x * y)) = κ (θ y) * κ (θ x)
    rw [hanti, map_mul]

section CStar

variable [StarRing A] [CStarRing A] [Nontrivial A]

/-- Anticommuting unitaries have a commutator of norm two. In particular this
applies to the selfadjoint anticommuting unitaries in a unital matrix algebra. -/
theorem norm_commutator_of_anticommuting_unitaries (a b : unitary A)
    (hab : (a : A) * (b : A) = -((b : A) * (a : A))) :
    ‖(a : A) * (b : A) - (b : A) * (a : A)‖ = 2 := by
  have hrewrite : (a : A) * (b : A) - (b : A) * (a : A) =
      (2 : ℂ) • ((a : A) * (b : A)) := by
    rw [two_smul, hab]
    abel
  rw [hrewrite, norm_smul, CStarRing.norm_coe_unitary_mul, CStarRing.norm_coe_unitary]
  simp

/-- The finite-factor orientation step using only closeness and a pair of
anticommuting unitaries, before any contractivity conclusion is available. -/
theorem PreservesJordan.multiplicative_of_close_of_anticommuting_unitaries_without_contractivity
    (θ : A →ₗ[ℂ] B) (ι : A →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (a b : unitary A) (hab : (a : A) * (b : A) = -((b : A) * (a : A)))
    (hsmall : 3 * e + e ^ 2 < 2) : ∀ x y, θ (x * y) = θ x * θ y := by
  exact PreservesJordan.multiplicative_of_close_without_contractivity θ ι κ hθ hsurj hprime
    he hι hclose a b (CStarRing.norm_coe_unitary a) (CStarRing.norm_coe_unitary b)
    (norm_commutator_of_anticommuting_unitaries a b hab) hsmall

end CStar

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixUnitsExistence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Full matrix subalgebras of every finite size in a II₁ factor

The existing continuous-dimension construction gives an equivalent
partition of the identity of every positive finite size. Its displayed
partial-isometry legs give the required actual matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Every positive finite matrix size occurs unitally inside the factor. -/
theorem exists_matrixUnits_of_size (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (k : ℕ) (hk : 0 < k) :
    Nonempty (Generator.MatrixUnitSystem (Fin k) (Algebra M)) := by
  have hc : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM.factor c hc
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hunit : (1 : Algebra M) ≠ 0 := by
    intro h
    exact hM.nonzero (congrArg Subtype.val h).symm
  obtain ⟨E⟩ := Generator.Tracial.traceFreeDimension_exists_equivalent_partition
    hc hM.diffuse hM.finite hunit k hk
      (⟨1, IsStarProjection.one (Algebra M)⟩ : Generator.Tracial.AlgebraProjection M)
  exact ⟨E.matrixUnits rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorAnticommuting
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Anticommuting unitaries in finite factors

The two Pauli matrices in a unital system of two-by-two matrix units give
selfadjoint anticommuting unitaries. Every II₁ factor contains such a system,
so the quantitative Jordan orientation test applies without an additional
assumption on the source factor.
-/

namespace KadisonKastler

noncomputable section

section MatrixUnits

variable {A : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
  (E : Generator.MatrixUnitSystem (Fin 2) A)

theorem matrixUnitsPauli_anticommute :
    (matrixUnitsPauliZUnitary E : A) * (matrixUnitsPauliXUnitary E : A) =
      -((matrixUnitsPauliXUnitary E : A) * (matrixUnitsPauliZUnitary E : A)) := by
  change matrixUnitsPauliZ E * matrixUnitsPauliX E =
    -(matrixUnitsPauliX E * matrixUnitsPauliZ E)
  simp [matrixUnitsPauliZ, matrixUnitsPauliX, add_mul, mul_add,
    E.mul_entry, sub_eq_add_neg, add_comm]

/-- A unital two-by-two matrix algebra supplies the exact pair used in the
Jordan orientation argument. -/
theorem exists_anticommuting_unitaries_of_matrixUnits
    (E : Generator.MatrixUnitSystem (Fin 2) A) :
    ∃ a b : unitary A, star (a : A) = (a : A) ∧ star (b : A) = (b : A) ∧
      (a : A) * (b : A) = -((b : A) * (a : A)) :=
  ⟨matrixUnitsPauliZUnitary E, matrixUnitsPauliXUnitary E,
    matrixUnitsPauliZ_star E, matrixUnitsPauliX_star E, matrixUnitsPauli_anticommute E⟩

end MatrixUnits

section Factor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Every concrete II₁ factor contains selfadjoint anticommuting unitaries. -/
theorem exists_anticommuting_unitaries_of_II1
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    ∃ a b : unitary (Algebra M),
      star (a : Algebra M) = (a : Algebra M) ∧
      star (b : Algebra M) = (b : Algebra M) ∧
      (a : Algebra M) * (b : Algebra M) = -((b : Algebra M) * (a : Algebra M)) := by
  obtain ⟨E⟩ := exists_matrixUnits_of_size hM 2 (by decide)
  exact exists_anticommuting_unitaries_of_matrixUnits E

/-- A sufficiently close surjective Jordan map out of a II₁ factor has the
multiplicative orientation; no contractivity hypothesis is needed. -/
theorem PreservesJordan.multiplicative_of_close_of_II1_oai
    {B D : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    [NormedRing D] [NormedAlgebra ℂ D]
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (θ : Algebra M →ₗ[ℂ] B) (ι : Algebra M →ₐ[ℂ] D) (κ : B →ₐ[ℂ] D) {e : ℝ}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (he : 0 ≤ e)
    (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (hclose : ∀ x, ‖κ (θ x) - ι x‖ ≤ e * ‖x‖)
    (hsmall : 3 * e + e ^ 2 < 2) :
    ∀ x y, θ (x * y) = θ x * θ y := by
  have hunit : (1 : Algebra M) ≠ 0 := by
    intro h
    exact hM.nonzero (congrArg Subtype.val h).symm
  let : Nontrivial (Algebra M) := nontrivial_of_ne _ _ hunit
  obtain ⟨a, b, _, _, hab⟩ := exists_anticommuting_unitaries_of_II1 hM
  exact PreservesJordan.multiplicative_of_close_of_anticommuting_unitaries_without_contractivity
    θ ι κ hθ hsurj hprime he hι hclose a b hab hsmall

end Factor

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.PreservesJordan.multiplicative_of_close_of_II1_oai.{u_1, u_2, u_3}
