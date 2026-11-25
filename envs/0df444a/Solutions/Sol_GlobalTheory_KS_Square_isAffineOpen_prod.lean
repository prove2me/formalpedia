-- Prove2me | solution 1 for GlobalTheory.KS.Square.isAffineOpen_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:05.277312+00:00
-- url     : https://prove2.me/submissions/70fe5f5d-d11e-4159-95d3-1b4940d28fe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Square
variable {Z : Scheme.{0}}
variable {J : Type} {V : J → Z.Opens}
namespace GlobalTheory.KS.Square
theorem _root_.solution {S X Y : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
    (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine U := hU
  have : IsAffine W := hW
  have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
  exact IsAffine.of_isPullback
    (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl)
end GlobalTheory.KS.Square
