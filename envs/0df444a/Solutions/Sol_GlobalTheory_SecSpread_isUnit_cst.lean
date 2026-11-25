-- Prove2me | solution 1 for GlobalTheory.SecSpread.isUnit_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:16:22.488831+00:00
-- url     : https://prove2.me/submissions/9a96df11-0bec-44f3-89ad-b960990222af

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_SecSpread_spMap_appTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution (hw : φ ≫ p = π ≫ spMap (algebraMap R K)) (z : X') {d : R} (hd : d ≠ 0) :
    IsUnit (cst (φ ≫ p) z d) := by
  have hu : IsUnit (algebraMap R K d) := ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hd).isUnit
  rw [hw, cst, ← gs_pull π _ z ⊤ trivial]
  have e := congrArg (gs π z ⊤) (spMap_appTop (algebraMap R K) d)
  refine (congrArg IsUnit e).mpr ?_
  rw [gs_eq π z ⊤ trivial]
  exact ((hu.map _).map _).map _
end GlobalTheory.SecSpread
