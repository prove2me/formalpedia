-- Prove2me | solution 1 for OAI.ProjectionCounterexample.simplex_eq_halfspaceBody
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:53.7927+00:00
-- url     : https://prove2.me/submissions/c64ce323-74c2-4ae9-8eaa-66cdc4411045

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexFacets.lean:L37-L52
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.simplex_eq_halfspaceBody. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_coordinates

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacets ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem simplex_eq_halfspaceBody (d : ℕ) :
    simplex d = halfspaceBody (simplexFunctional d) simplexLevel := by
  rw [simplex_eq_coordinates]
  ext x
  constructor
  · rintro ⟨hx, hs⟩ i
    cases i with
    | none => simpa [simplexLevel] using hs
    | some i => simpa [simplexLevel] using neg_nonpos.mpr (hx i)
  · intro hx
    constructor
    · intro i
      have := hx (some i)
      simpa [simplexLevel] using this
    · have := hx none
      simpa [simplexLevel] using this

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set

theorem solution (d : ℕ) :
    simplex d = halfspaceBody (simplexFunctional d) simplexLevel := by
  first
    | exact OAI.ProjectionCounterexample.simplex_eq_halfspaceBody d
    | exact OAI.ProjectionCounterexample.simplex_eq_halfspaceBody
    | (apply OAI.ProjectionCounterexample.simplex_eq_halfspaceBody <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.simplex_eq_halfspaceBody <;> assumption)
