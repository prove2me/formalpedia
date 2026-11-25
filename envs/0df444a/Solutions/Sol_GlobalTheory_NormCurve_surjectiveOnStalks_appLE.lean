-- Prove2me | solution 1 for GlobalTheory.NormCurve.surjectiveOnStalks_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:08.762913+00:00
-- url     : https://prove2.me/submissions/c5305397-b5da-4dcd-9f4b-a59ad9f39e34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint
import Theorems.Thm_GlobalTheory_NormCurve_isAffineOpen_of_subsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.NormCurve
variable {k : Type} [Field k] {X Z : Scheme.{0}}
variable [IsIntegral Z] [Subsingleton Z] [IsAffine Z] (f : Z ⟶ X) [SurjectiveOnStalks f]
namespace GlobalTheory.NormCurve
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (V : Z.Opens) [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.SurjectiveOnStalks :=
  HasRingHomProperty.appLE @SurjectiveOnStalks f inferInstance ⟨U, hU⟩
    ⟨V, isAffineOpen_of_subsingleton V⟩ e
end GlobalTheory.NormCurve
