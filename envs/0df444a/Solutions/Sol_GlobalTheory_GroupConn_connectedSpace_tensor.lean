-- Prove2me | solution 1 for GlobalTheory.GroupConn.connectedSpace_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:17.759579+00:00
-- url     : https://prove2.me/submissions/4b0fe18f-23f2-41ca-b3aa-d1ec32b50651

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_of_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GroupConn
namespace GlobalTheory.GroupConn
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] [GeometricallyConnected G.hom]
    (Y : Over S) [ConnectedSpace Y.left] : ConnectedSpace (G ⊗ Y).left := by

  have : GeometricallyConnected (snd G Y).left :=
    show GeometricallyConnected (pullback.snd G.hom Y.hom) from inferInstance
  have hsec : (lift (toUnit Y ≫ η[G]) (𝟙 Y)).left ≫ (snd G Y).left = 𝟙 Y.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  exact connectedSpace_of_section (snd G Y).left _ hsec
end GlobalTheory.GroupConn
