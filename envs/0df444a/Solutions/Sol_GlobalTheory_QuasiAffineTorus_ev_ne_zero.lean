-- Prove2me | solution 1 for GlobalTheory.QuasiAffineTorus.ev_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:04:59.86325+00:00
-- url     : https://prove2.me/submissions/e2db77d4-fed6-46f5-9407-e9e99f8f4c9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
import Theorems.Thm_GlobalTheory_QuasiAffineTorus_appTop_eq_of_ev_eq

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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
variable {k : Type} [Field k]
namespace GlobalTheory.QuasiAffineTorus
theorem _root_.solution {N : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ N) {f : Γ(N.left, ⊤)}
    (h : pt x ∈ N.left.basicOpen f) : ev x f ≠ 0 := fun e => by
  have h1 : x.left.appTop.hom f = 0 := by
    rw [appTop_eq_of_ev_eq (y := x) (g := 0) (by rw [e, map_zero]), map_zero]
  have h2 : IsLocalRing.closedPoint k ∈ x.left ⁻¹ᵁ N.left.basicOpen f := h
  rw [Scheme.preimage_basicOpen_top] at h2
  erw [h1, Scheme.basicOpen_zero] at h2
  exact h2
end GlobalTheory.QuasiAffineTorus
