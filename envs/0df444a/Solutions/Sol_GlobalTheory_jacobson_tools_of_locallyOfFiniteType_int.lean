-- Prove2me | solution 1 for GlobalTheory.jacobson_tools_of_locallyOfFiniteType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:25.054907+00:00
-- url     : https://prove2.me/submissions/77480103-ced5-4add-af4b-1ff67520a012

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Theorems.Thm_GlobalTheory_jacobsonSpace_of_locallyOfFiniteType_int
import Theorems.Thm_GlobalTheory_finite_residueField_of_isClosed_of_locallyOfFiniteType_int
import Theorems.Thm_GlobalTheory_subset_of_isOpen_of_closedPoints
import Theorems.Thm_GlobalTheory_exists_isClosed_specializes_mem_iff
import Theorems.Thm_GlobalTheory_exists_dense_of_closedPoints_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧
      (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
      (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧
      (∀ (ξ : X) (ι : Type) [Finite ι] (U : ι → X.Opens) (W : X.Opens), ξ ∈ W →
        ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧
      (∀ (ι : Type) [Finite ι] (Sg : ι → Set X), IrreducibleSpace X →
        (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) := by
  intro X π _
  have hJ := jacobsonSpace_of_locallyOfFiniteType_int π
  refine ⟨hJ, finite_residueField_of_isClosed_of_locallyOfFiniteType_int π, ?_, ?_, ?_⟩
  · intro U V h
    exact TopologicalSpace.Opens.ext (subset_antisymm
      (subset_of_isOpen_of_closedPoints U.isOpen V.isOpen fun x hx => (h x hx).1)
      (subset_of_isOpen_of_closedPoints V.isOpen U.isOpen fun x hx => (h x hx).2))
  · intro ξ ι _ U W hξ
    exact exists_isClosed_specializes_mem_iff ξ (fun i => (U i : Set X)) (fun i => (U i).isOpen)
      W.isOpen hξ
  · intro ι _ Sg _ h
    exact exists_dense_of_closedPoints_cover Sg h
end GlobalTheory
