-- Prove2me | solution 1 for GlobalTheory.CubeLift.Reduces.scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:29:18.136259+00:00
-- url     : https://prove2.me/submissions/f596970c-a696-478a-a031-c30f2a4abb62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
import Theorems.Thm_GlobalTheory_CubeLift_app_app
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G₀] [IsCommMonObj G₀]
  {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ red J} {P : CP G} {P₀ : CP G₀}
  {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i₀ : splitTorus _ X ⟶ G₀}
namespace GlobalTheory.CubeLift
namespace Reduces
theorem _root_.solution {t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1])}
    {σ₀ : CubTriv P₀.c i₀} (h : Reduces w t σ₀) {g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ}
    (hg : app (bcMap (red J) X) g = 1) : Reduces w (scaleGen g t) σ₀ := fun T z C₀ C hC₀ hC W hW x => by
  have e : gm (x.left ≫ bcMap (red J) X) z ⊤ g = 1 := by
    rw [gm_top]
    exact (congrArg _ ((app_app _ _ g).symm.trans (by rw [hg, map_one]))).trans (map_one _)
  rw [val_scaleGen _ _ _ hC, e, _root_.one_mul]
  exact h T z C₀ C hC₀ hC W hW x
end Reduces
end GlobalTheory.CubeLift
