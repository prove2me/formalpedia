-- Prove2me | solution 1 for OAI.Tingley.tingley_sphere_isometry_full
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:29:16.918576+00:00
-- url     : https://prove2.me/submissions/ab612a48-abb1-4dcf-b5dc-c75adb807473

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/Extension.lean:L100-L114
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Tingley.tingley_sphere_isometry_full.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Tingley_tingley_sphere_isometry_full) verbatim and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace
import Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveScheduling
import Definitions.Def_OAI_Analysis_SphereIsometry_InvariantConvexSet
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignmentSet
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapEstimate
import Definitions.Def_OAI_Analysis_SphereIsometry_DiameterBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapBounds
import Definitions.Def_OAI_Analysis_SphereIsometry_ScalarBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapNoncompactness
import Definitions.Def_OAI_Analysis_SphereIsometry_ProbabilitySimplex
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_FiniteComplex
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricFlags
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionData
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricBasic
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricSupport
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexDiameter
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricMesh
import Definitions.Def_OAI_Analysis_SphereIsometry_IteratedPoints
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerFacet
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SpernerBoundary
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionRestriction
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_SubdivisionIncidence
import Definitions.Def_OAI_Analysis_SphereIsometry_BarycentricZero
import Definitions.Def_OAI_Analysis_SphereIsometry_Sperner
import Definitions.Def_OAI_Analysis_SphereIsometry_SimplexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactApproximation
import Definitions.Def_OAI_Analysis_SphereIsometry_CompactConvexFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_CoefficientBins
import Definitions.Def_OAI_Analysis_SphereIsometry_ConvexCoverRegroup
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiConvexHull
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingIteration
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiTotalBounded
import Definitions.Def_OAI_Analysis_SphereIsometry_KuratowskiNested
import Definitions.Def_OAI_Analysis_SphereIsometry_CondensingFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMapFixedPoint
import Definitions.Def_OAI_Analysis_SphereIsometry_AlignedConfiguration
import Definitions.Def_OAI_Analysis_SphereIsometry_Alignment
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordSecant
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialPerturbation
import Definitions.Def_OAI_Analysis_SphereIsometry_LargeChord
import Definitions.Def_OAI_Analysis_SphereIsometry_SmallChord
import Definitions.Def_OAI_Analysis_SphereIsometry_ChordContradiction
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialExtension
import Definitions.Def_OAI_Analysis_SphereIsometry_Extension

-- ---- from OAI.Analysis.SphereIsometry.RadialExtension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The radial extension of a sphere isometry with zero defect

The extension is defined on actual vectors, including zero. A zero cross-radius
bound gives its all-pairs isometry; sphere surjectivity gives its surjectivity.
Mazur–Ulam then supplies real linearity. Uniqueness is proved against arbitrary
real-linear extensions, without assuming they are continuous or surjective.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Any real-linear extension has the radial formula, without additional hypotheses on it. -/
theorem linear_extension_eq_radial (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L : X →ₗ[ℝ] Y) (hL : ∀ u : UnitSphere X, L (u : X) = (f u : Y)) (x : X) :
    L x = radialExtension f x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, radialExtension_zero]
  · calc
      L x = L (‖x‖ • (normalize x hx : X)) :=
        congrArg L (norm_smul_normalize x hx).symm
      _ = ‖x‖ • L (normalize x hx : X) := L.map_smul _ _
      _ = ‖x‖ • (f (normalize x hx) : Y) := by rw [hL]
      _ = radialExtension f x := (radialExtension_of_ne_zero f x hx).symm

end Tingley

end

end OAI

-- ---- from OAI.Analysis.SphereIsometry.Extension ----
namespace OAI

/-!
# The unique real-linear extension of an onto sphere isometry

The intermediate hypotheses of the separate constructions are discharged here:
positive original defect produces an actual attained defect in completed normed
quotients, alignment produces actual opposite chords, and the chord theorem
rules them out. The original radial extension consequently preserves distance.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable [Nontrivial X] [Nontrivial Y]

theorem extension_radial (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) (hx : x ≠ 0) :
    extension f x = ‖x‖ • (f (normalize x hx) : Y) :=
  radialExtension_of_ne_zero f x hx

theorem extension_surjective (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    Function.Surjective (extension f) := (extension f).surjective

theorem extension_unique (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L : X →ₗ[ℝ] Y) (hL : ∀ x : UnitSphere X, L (x : X) = (f x : Y)) :
    L = (extension f).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact linear_extension_eq_radial f L hL x

/-- Radial formula, surjectivity, and uniqueness among all real-linear extensions. -/
theorem tingley_sphere_isometry_full
    (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ u : UnitSphere X, T (u : X) = (f u : Y)) ∧
      T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f (normalize x hx) : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : UnitSphere X, L (u : X) = (f u : Y)) →
        L = T.toLinearEquiv.toLinearMap) := by
  let e := sphereIsometryEquiv f hf hs
  refine ⟨extension e, extension_unit e, extension_zero e,
    extension_radial e, extension_surjective e, ?_⟩
  intro L hL
  exact extension_unique e L hL

end Tingley

end

end OAI

-- ---- mission target ----
open OAI OAI.Tingley
universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

namespace OAI
namespace Tingley
theorem _root_.solution
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [Nontrivial X] [Nontrivial Y]
    (f : UnitSphere X → UnitSphere Y) (hf : Isometry f) (hs : Function.Surjective f) :
    ∃ T : X ≃ₗᵢ[ℝ] Y,
      (∀ u : UnitSphere X, T (u : X) = (f u : Y)) ∧
      T 0 = 0 ∧
      (∀ x : X, ∀ hx : x ≠ 0, T x = ‖x‖ • (f (normalize x hx) : Y)) ∧
      Function.Surjective T ∧
      (∀ L : X →ₗ[ℝ] Y, (∀ u : UnitSphere X, L (u : X) = (f u : Y)) →
        L = T.toLinearEquiv.toLinearMap) := by
  first
    | exact OAI.Tingley.tingley_sphere_isometry_full f hf hs
    | exact OAI.Tingley.tingley_sphere_isometry_full
    | (apply OAI.Tingley.tingley_sphere_isometry_full <;> assumption)
    | (intros; apply OAI.Tingley.tingley_sphere_isometry_full <;> assumption)
end Tingley
end OAI
