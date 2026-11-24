-- Prove2me | solution 1 for GlobalTheory.jacobson_closedPoints_tools_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:27.823062+00:00
-- url     : https://prove2.me/submissions/bfdd5456-ddab-4ac4-96ee-8c3619d1c7fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Theorems.Thm_GlobalTheory_jacobson_tools_of_locallyOfFiniteType_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧ (∀ (ξ : X) (κ : Type) [Finite κ] (U : κ → X.Opens) (W : X.Opens), ξ ∈ W → ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧ (∀ (κ : Type) [Finite κ] (Sg : κ → Set X), IrreducibleSpace X → (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) :=
  jacobson_tools_of_locallyOfFiniteType_int
end GlobalTheory
