-- Prove2me | solution 1 for GlobalTheory.GroupConn.connectedSpace_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:15:25.849075+00:00
-- url     : https://prove2.me/submissions/9b03df9e-d894-4a84-af5c-ad64e6cfc1da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_of_section
import Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_tensor

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
theorem _root_.solution : ∀ (S : Scheme.{0}) [ConnectedSpace S] (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom], ConnectedSpace G.left ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S), ConnectedSpace Y.left → ConnectedSpace (splitTorus S X ⊗ Y).left ∧ ConnectedSpace (G ⊗ Y).left := by
  intro S _ G _ _ _
  refine ⟨connectedSpace_of_section (S := S) (X := G.left) G.hom η[G].left (Over.w _),
    fun X _ _ Y _ => ⟨?_, connectedSpace_tensor G Y⟩⟩

  have : UniqueSums X :=
    UniqueSums.of_injective_addHom (Module.Free.chooseBasis ℤ X).repr.toAddEquiv.toAddHom
      (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  exact connectedSpace_tensor (splitTorus S X) Y
end GlobalTheory.GroupConn
