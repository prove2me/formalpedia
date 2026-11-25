-- Prove2me | solution 1 for GlobalTheory.UU.BiTransport.exists_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:53:03.697883+00:00
-- url     : https://prove2.me/submissions/9a36d980-69bf-42fd-a85f-0b7d4e16cd05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BiTrivTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiTransport
variable {S S₀ : Scheme.{0}} {ρ : S₀ ⟶ S}
namespace GlobalTheory.UU.BiTransport
theorem _root_.solution {Z : Over S} (r : Z.left ⟶ S₀) (h : r ≫ ρ = Z.hom) : ∃ T : Over S₀, Z = Over.mk (T.hom ≫ ρ) := by
  obtain ⟨Z, ⟨⟨⟩⟩, f⟩ := Z
  change Z ⟶ S₀ at r
  change Z ⟶ S at f
  obtain rfl : r ≫ ρ = f := h
  exact ⟨Over.mk r, rfl⟩
end GlobalTheory.UU.BiTransport
