-- Prove2me | solution 1 for GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:41:37.662848+00:00
-- url     : https://prove2.me/submissions/c817be31-11df-42fb-8961-43dae54043a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Theorems.Thm_GlobalTheory_ZM_secCoord_of_locally


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → Ideal.span (Set.range v) = ⊤ → (∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) → SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.secCoord_of_locally | exact GlobalTheory.ZM.secCoord_of_locally | (intros; apply GlobalTheory.ZM.secCoord_of_locally <;> assumption)
end _root_.GlobalTheory.T
